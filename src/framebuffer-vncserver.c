/*
 * $Id$
 *
 * This program is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by the
 * Free Software Foundation; either version 2, or (at your option) any
 * later version.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 *
 * This project is an adaptation of the original fbvncserver for the iPAQ
 * and Zaurus.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <unistd.h>
#include <sys/mman.h>
#include <sys/ioctl.h>

#include <sys/stat.h>
#include <sys/sysmacros.h> /* For makedev() */

#include <fcntl.h>
#include <linux/fb.h>
#include <linux/input.h>

#include <assert.h>
#include <errno.h>
#include <arpa/inet.h> /* htonl, ntohl */
#include <sodium.h>
#include <gnutls/gnutls.h>

/* Ensure rfb/rfb.h exposes the sslctx member in rfbClientRec.
 * libvncserver on the target was built with GnuTLS, so the struct layout
 * includes sslctx.  We must see the same layout at compile time. */
#ifndef LIBVNCSERVER_HAVE_LIBGNUTLS
#define LIBVNCSERVER_HAVE_LIBGNUTLS 1
#endif

/* libvncserver */
#include "rfb/rfb.h"
#include "rfb/keysym.h"

#include "touch.h"
#include "mouse.h"
#include "keyboard.h"
#include "logging.h"

/*****************************************************************************/
#define LOG_FPS

#define BITS_PER_SAMPLE 5
#define SAMPLES_PER_PIXEL 2

// #define CHANNELS_PER_PIXEL 4

static char fb_device[256] = "/dev/fb0";
static char touch_device[256] = "/dev/input/event1";
static char kbd_device[256] = "/dev/input/event0";
static char mouse_device[256] = "";

static struct fb_var_screeninfo var_scrinfo;
static struct fb_fix_screeninfo fix_scrinfo;
static int fbfd = -1;
static unsigned short int *fbmmap = MAP_FAILED;
static unsigned short int *vncbuf;
static unsigned short int *fbbuf;

static int vnc_port = 5900;
static int vnc_rotate = 0;
static int touch_rotate = -1;
static int target_fps = 10;
static rfbScreenInfoPtr server;
static size_t bytespp;
static unsigned int bits_per_pixel;
static unsigned int frame_size;
static unsigned int fb_xres;
static unsigned int fb_yres;
int verbose = 0;
/* Path to Argon2id hash file for VeNCrypt Plain auth. */
static const char *hashFilePath = NULL;
/* When set, read password from stdin, hash it, write to this path, and exit. */
static const char *writeHashFile = NULL;

#define UNUSED(x) (void)(x)

/* VeNCrypt sub-types. */
#define VENCRYPT_PLAIN    256 /* Plain (username + password, no TLS) */
#define VENCRYPT_TLSPLAIN 259 /* Plain over anonymous TLS */

/**
 * Read the Argon2id hash string from the hash file.
 * Returns a heap-allocated, zero-terminated string on success, or NULL on failure.
 * Caller must sodium_free() the result.
 */
static char *load_password_hash(void)
{
    if (!hashFilePath) return NULL;

    FILE *fp = fopen(hashFilePath, "r");
    if (!fp) {
        error_print("cannot open hash file %s\n", hashFilePath);
        return NULL;
    }

    /* Argon2id hash strings are at most crypto_pwhash_STRBYTES (128) chars. */
    char *buf = sodium_malloc(crypto_pwhash_STRBYTES);
    if (!buf) {
        fclose(fp);
        return NULL;
    }
    memset(buf, 0, crypto_pwhash_STRBYTES);

    if (!fgets(buf, crypto_pwhash_STRBYTES, fp)) {
        error_print("failed to read hash from %s\n", hashFilePath);
        sodium_free(buf);
        fclose(fp);
        return NULL;
    }
    fclose(fp);

    /* Strip trailing newline. */
    size_t len = strlen(buf);
    if (len > 0 && buf[len - 1] == '\n') buf[len - 1] = '\0';

    return buf;
}

/* Send an RFB auth failure with optional reason text. */
static void send_auth_failure(rfbClientPtr cl, const char *reason)
{
    uint32_t result = htonl(1);
    if (rfbWriteExact(cl, (const char *)&result, 4) < 0) return;

    if (!reason) return;

    uint32_t len = (uint32_t)strlen(reason);
    uint32_t len_be = htonl(len);
    if (rfbWriteExact(cl, (const char *)&len_be, 4) < 0) return;
    if (len > 0) rfbWriteExact(cl, reason, (int)len);
}

/*
 * libvncserver 0.9.13 internal SSL context.  When cl->sslctx is non-NULL the
 * library's rfbReadExact / rfbWriteExact transparently route through the
 * internal rfbssl_read / rfbssl_write which use ctx->session.  We replicate
 * the struct layout so we can initialise a GnuTLS anonymous-TLS session and
 * plug it in without touching libvncserver internals.
 */
struct rfbssl_ctx {
    char                                  peekbuf[2048];
    int                                   peeklen;
    int                                   peekstart;
    gnutls_session_t                      session;
    gnutls_certificate_credentials_t      x509_cred;
    gnutls_dh_params_t                    dh_params;
};

/* Shared anonymous credentials – initialised once, reused for every TLS
 * client connection. */
static gnutls_anon_server_credentials_t g_anon_cred = NULL;

/**
 * Initialise the global anonymous TLS credentials (call once at startup).
 * Returns 0 on success, -1 on failure.
 */
static int tls_init_global(void)
{
    int ret;

    ret = gnutls_global_init();
    if (ret != GNUTLS_E_SUCCESS) {
        rfbErr("gnutls_global_init: %s\n", gnutls_strerror(ret));
        return -1;
    }

    ret = gnutls_anon_allocate_server_credentials(&g_anon_cred);
    if (ret != GNUTLS_E_SUCCESS) {
        rfbErr("gnutls_anon_allocate_server_credentials: %s\n",
               gnutls_strerror(ret));
        return -1;
    }

    /* Use built-in DH parameters (GnuTLS ≥ 3.6). */
    gnutls_anon_set_server_known_dh_params(g_anon_cred,
                                           GNUTLS_SEC_PARAM_MEDIUM);
    return 0;
}

/**
 * Establish anonymous TLS on an already-connected client socket.
 * On success cl->sslctx is set and all subsequent rfbReadExact /
 * rfbWriteExact calls go through GnuTLS transparently.
 * Returns 0 on success, -1 on failure.
 */
static int setup_tls(rfbClientPtr cl)
{
    int ret;
    struct rfbssl_ctx *ctx = calloc(1, sizeof(*ctx));
    if (!ctx) return -1;

    ret = gnutls_init(&ctx->session, GNUTLS_SERVER);
    if (ret != GNUTLS_E_SUCCESS) goto fail;

    /* Anonymous key-exchange only (ECDH preferred, plain DH as fallback).
     * TigerVNC and gtk-vnc both use anonymous TLS for VeNCrypt TLS* types.
     * Build from NONE to avoid any implicit restrictions from NORMAL and
     * to exclude TLS 1.3 (which has no anonymous cipher suites). */
    const char *prio_err = NULL;
    ret = gnutls_priority_set_direct(ctx->session,
                                     "NONE:+VERS-TLS1.2:+VERS-TLS1.1:+VERS-TLS1.0:"
                                     "+AES-128-GCM:+AES-256-GCM:+AES-128-CBC:+AES-256-CBC:"
                                     "+AEAD:+SHA256:+SHA384:+SHA1:"
                                     "+ANON-ECDH:+ANON-DH:+COMP-NULL:+CURVE-ALL",
                                     &prio_err);
    if (ret != GNUTLS_E_SUCCESS) {
        rfbErr("VeNCrypt priority_set_direct failed: %s (near: %s)\n",
               gnutls_strerror(ret), prio_err ? prio_err : "?");
        goto fail_session;
    }

    ret = gnutls_credentials_set(ctx->session, GNUTLS_CRD_ANON, g_anon_cred);
    if (ret != GNUTLS_E_SUCCESS) {
        rfbErr("VeNCrypt credentials_set failed: %s\n", gnutls_strerror(ret));
        goto fail_session;
    }

    gnutls_transport_set_ptr(ctx->session,
                             (gnutls_transport_ptr_t)(uintptr_t)cl->sock);

    rfbLog("VeNCrypt: starting TLS handshake on fd %d\n", cl->sock);

    /* TLS handshake (blocking, retry on EAGAIN / EINTR). */
    do {
        ret = gnutls_handshake(ctx->session);
    } while (ret == GNUTLS_E_AGAIN || ret == GNUTLS_E_INTERRUPTED);

    if (ret != GNUTLS_E_SUCCESS) {
        rfbErr("VeNCrypt TLS handshake failed: %s (alert: %d)\n",
               gnutls_strerror(ret), gnutls_alert_get(ctx->session));
        goto fail_session;
    }

    /* Allocate a dummy x509_cred so libvncserver's rfbssl_destroy (which
     * unconditionally calls gnutls_certificate_free_credentials) does not
     * crash on cleanup. */
    ret = gnutls_certificate_allocate_credentials(&ctx->x509_cred);
    if (ret != GNUTLS_E_SUCCESS) {
        rfbErr("VeNCrypt x509 credential allocation failed: %s\n",
               gnutls_strerror(ret));
        goto fail_session;
    }
    ctx->dh_params = NULL;

    cl->sslctx = (rfbSslCtx *)ctx;

    info_print("VeNCrypt TLS established: %s\n",
               gnutls_protocol_get_name(
                   gnutls_protocol_get_version(ctx->session)));
    return 0;

fail_session:
    gnutls_deinit(ctx->session);
fail:
    rfbErr("VeNCrypt TLS setup error: %s\n", gnutls_strerror(ret));
    free(ctx);
    return -1;
}

/**
 * VeNCrypt security handler (RFB security type 19).
 *
 * Implements the VeNCrypt 0.2 handshake offering TLSPlain (259) only.
 * TLSPlain wraps the connection in anonymous TLS before the Plain
 * username/password exchange.  The password is verified against the
 * stored Argon2id hash.
 */
static void vencrypt_handler(rfbClientPtr cl)
{
    uint8_t buf[8];

    /* --- VeNCrypt version negotiation --- */
    /* Send server VeNCrypt version 0.2 */
    buf[0] = 0; /* major */
    buf[1] = 2; /* minor */
    if (rfbWriteExact(cl, (const char *)buf, 2) < 0) return;

    /* Read client VeNCrypt version */
    if (rfbReadExact(cl, (char *)buf, 2) <= 0) return;
    if (buf[0] != 0 || buf[1] < 2) {
        /* Unsupported version — send nack */
        buf[0] = 0xFF;
        rfbWriteExact(cl, (const char *)buf, 1);
        rfbCloseClient(cl);
        return;
    }

    /* Send version ack (0 = OK) */
    buf[0] = 0;
    if (rfbWriteExact(cl, (const char *)buf, 1) < 0) return;

    /* --- Advertise sub-types --- */
    /* Number of sub-types: 1 (TLSPlain only; do not allow plaintext fallback) */
    buf[0] = 1;
    if (rfbWriteExact(cl, (const char *)buf, 1) < 0) return;

    uint32_t subtypes[1];
    subtypes[0] = htonl(VENCRYPT_TLSPLAIN); /* 259 */
    if (rfbWriteExact(cl, (const char *)subtypes, 4) < 0) return;

    /* Read client's chosen sub-type */
    uint32_t chosen;
    if (rfbReadExact(cl, (char *)&chosen, 4) <= 0) return;
    chosen = ntohl(chosen);

    if (chosen != VENCRYPT_TLSPLAIN) {
        rfbErr("VeNCrypt: client chose unsupported sub-type %u\n", chosen);
        /* Send sub-type rejection (1 byte: 0 = rejected) */
        buf[0] = 0;
        rfbWriteExact(cl, (const char *)buf, 1);
        rfbCloseClient(cl);
        return;
    }

    /* Send sub-type acceptance (1 byte: 1 = accepted) */
    buf[0] = 1;
    if (rfbWriteExact(cl, (const char *)buf, 1) < 0) return;

    /* --- TLS handshake --- */
    if (setup_tls(cl) != 0) {
        rfbCloseClient(cl);
        return;
    }
    /* From here on rfbReadExact/rfbWriteExact go through GnuTLS. */

    /* --- Plain authentication --- */
    /* Read username_len (4 bytes BE) + password_len (4 bytes BE) */
    uint32_t ulen_be, plen_be;
    if (rfbReadExact(cl, (char *)&ulen_be, 4) <= 0) return;
    if (rfbReadExact(cl, (char *)&plen_be, 4) <= 0) return;
    uint32_t ulen = ntohl(ulen_be);
    uint32_t plen = ntohl(plen_be);

    /* Sanity limits */
    if (ulen > 1024 || plen > 1024) {
        rfbErr("VeNCrypt: credential lengths too large (u=%u p=%u)\n", ulen, plen);
        send_auth_failure(cl, "Invalid username/password length");
        rfbCloseClient(cl);
        return;
    }

    /* Read and discard username */
    if (ulen > 0) {
        char *ubuf = malloc(ulen);
        if (!ubuf || rfbReadExact(cl, ubuf, ulen) <= 0) {
            free(ubuf);
            rfbCloseClient(cl);
            return;
        }
        free(ubuf);
    }

    /* Read password into sodium-guarded memory */
    char *password = sodium_malloc(plen + 1);
    if (!password) {
        rfbCloseClient(cl);
        return;
    }

    if (plen > 0 && rfbReadExact(cl, password, plen) <= 0) {
        sodium_free(password);
        rfbCloseClient(cl);
        return;
    }
    password[plen] = '\0';

    /* Load stored hash and verify */
    char *stored_hash = load_password_hash();
    rfbBool ok = FALSE;

    if (stored_hash && password[0] != '\0') {
        if (crypto_pwhash_str_verify(stored_hash, password, plen) == 0) {
            ok = TRUE;
        }
    }

    /* Wipe secrets */
    sodium_free(password);
    if (stored_hash) sodium_free(stored_hash);

    /* Send result: 0 = OK, 1 = failed (uint32 BE)
     * Custom security handlers must send SecurityResult explicitly —
     * libvncserver only auto-sends it for the built-in None type. */
    if (ok) {
        uint32_t result = htonl(0);
        if (rfbWriteExact(cl, (const char *)&result, 4) < 0) {
            rfbErr("VeNCrypt: client %s disconnected before auth result "
                   "(probable timeout during hash verification)\n", cl->host);
            rfbCloseClient(cl);
            return;
        }
        info_print("VeNCrypt: authentication succeeded from %s\n", cl->host);
        cl->state = RFB_INITIALISATION;
    } else {
        send_auth_failure(cl, "Authentication failed");
        rfbErr("VeNCrypt: authentication failed from %s\n", cl->host);
        rfbCloseClient(cl);
    }
}

static rfbSecurityHandler vencryptSecurityHandler = {
    .type    = 19, /* rfbSecTypeVeNCrypt */
    .handler = vencrypt_handler,
    .next    = NULL
};

#if defined(__GNUC__)
/* Optional API in newer libvncserver builds. On older versions this symbol
 * is absent; keep a weak declaration so we can fall back at runtime. */
extern void rfbRegisterChannelSecurityHandler(rfbSecurityHandler *handler) __attribute__((weak));
#endif

/* Reject built-in DES VNCAuth if a client chooses security type 2.
 * We keep this fallback for older libvncserver that lacks channel security
 * registration API. */
static rfbBool reject_vncauth_password_check(rfbClientPtr cl, const char *response, int len)
{
    UNUSED(response);
    UNUSED(len);
    rfbErr("Rejected VNCAuth (type 2) from %s: VeNCrypt is required\n", cl->host);
    return FALSE;
}

/* No idea, just copied from fbvncserver as part of the frame differerencing
 * algorithm.  I will probably be later rewriting all of this. */
static struct varblock_t
{
    int min_i;
    int min_j;
    int max_i;
    int max_j;
    int r_offset;
    int g_offset;
    int b_offset;
    int rfb_xres;
    int rfb_maxy;
} varblock;

/*****************************************************************************/

static void init_fb(void)
{
    size_t pixels;

    if ((fbfd = open(fb_device, O_RDONLY)) == -1)
    {
        error_print("cannot open fb device %s\n", fb_device);
        exit(EXIT_FAILURE);
    }

    if (ioctl(fbfd, FBIOGET_VSCREENINFO, &var_scrinfo) != 0)
    {
        error_print("ioctl error\n");
        exit(EXIT_FAILURE);
    }

    if (ioctl(fbfd, FBIOGET_FSCREENINFO, &fix_scrinfo) != 0)
    {
        error_print("ioctl error\n");
        exit(EXIT_FAILURE);
    }

    /*
     * Get actual resolution of the framebufffer, which is not always the same as the screen resolution.
     * This prevents the screen from 'smearing' on 1366 x 768 displays
     */

    fb_xres = fix_scrinfo.line_length / (var_scrinfo.bits_per_pixel / 8.0);
    fb_yres = var_scrinfo.yres;

    pixels = fb_xres * fb_yres;
    bytespp = var_scrinfo.bits_per_pixel / 8;
    bits_per_pixel = var_scrinfo.bits_per_pixel;
    frame_size = pixels * bits_per_pixel / 8;

    info_print("  xres=%d, yres=%d, xresv=%d, yresv=%d, xoffs=%d, yoffs=%d, bpp=%d\n",
               (int)fb_xres, (int)fb_yres,
               (int)var_scrinfo.xres_virtual, (int)var_scrinfo.yres_virtual,
               (int)var_scrinfo.xoffset, (int)var_scrinfo.yoffset,
               (int)var_scrinfo.bits_per_pixel);
    info_print("  offset:length red=%d:%d green=%d:%d blue=%d:%d \n",
               (int)var_scrinfo.red.offset, (int)var_scrinfo.red.length,
               (int)var_scrinfo.green.offset, (int)var_scrinfo.green.length,
               (int)var_scrinfo.blue.offset, (int)var_scrinfo.blue.length);

    fbmmap = mmap(NULL, frame_size, PROT_READ, MAP_SHARED, fbfd, 0);

    if (fbmmap == MAP_FAILED)
    {
        error_print("mmap failed\n");
        exit(EXIT_FAILURE);
    }
}

static void cleanup_fb(void)
{
    if (fbfd != -1)
    {
        close(fbfd);
        fbfd = -1;
    }
}

static void keyevent(rfbBool down, rfbKeySym key, rfbClientPtr cl)
{
    int scancode;

    debug_print("Got keysym: %04x (down=%d)\n", (unsigned int)key, (int)down);

    if ((scancode = keysym2scancode(key, cl)))
    {
        injectKeyEvent(scancode, down);
    }
}

static void ptrevent_touch(int buttonMask, int x, int y, rfbClientPtr cl)
{
    UNUSED(cl);
    /* Indicates either pointer movement or a pointer button press or release. The pointer is
now at (x-position, y-position), and the current state of buttons 1 to 8 are represented
by bits 0 to 7 of button-mask respectively, 0 meaning up, 1 meaning down (pressed).
On a conventional mouse, buttons 1, 2 and 3 correspond to the left, middle and right
buttons on the mouse. On a wheel mouse, each step of the wheel upwards is represented
by a press and release of button 4, and each step downwards is represented by
a press and release of button 5.
  From: http://www.vislab.usyd.edu.au/blogs/index.php/2009/05/22/an-headerless-indexed-protocol-for-input-1?blog=61 */

    debug_print("Got ptrevent: %04x (x=%d, y=%d)\n", buttonMask, x, y);
    // Simulate left mouse event as touch event
    static int pressed = 0;
    if (buttonMask & 1)
    {
        if (pressed == 1)
        {
            injectTouchEvent(MouseDrag, x, y, &var_scrinfo);
        }
        else
        {
            pressed = 1;
            injectTouchEvent(MousePress, x, y, &var_scrinfo);
        }
    }
    if (buttonMask == 0)
    {
        if (pressed == 1)
        {
            pressed = 0;
            injectTouchEvent(MouseRelease, x, y, &var_scrinfo);
        }
    }
}

static void ptrevent_mouse(int buttonMask, int x, int y, rfbClientPtr cl)
{
    UNUSED(cl);
    /* Indicates either pointer movement or a pointer button press or release. The pointer is
now at (x-position, y-position), and the current state of buttons 1 to 8 are represented
by bits 0 to 7 of button-mask respectively, 0 meaning up, 1 meaning down (pressed).
On a conventional mouse, buttons 1, 2 and 3 correspond to the left, middle and right
buttons on the mouse. On a wheel mouse, each step of the wheel upwards is represented
by a press and release of button 4, and each step downwards is represented by
a press and release of button 5.
  From: http://www.vislab.usyd.edu.au/blogs/index.php/2009/05/22/an-headerless-indexed-protocol-for-input-1?blog=61 */

    debug_print("Got mouse: %04x (x=%d, y=%d)\n", buttonMask, x, y);
    // Simulate left mouse event as touch event
    injectMouseEvent(&var_scrinfo, buttonMask, x, y);
}

/*****************************************************************************/

static void init_fb_server(int argc, char **argv, rfbBool enable_touch, rfbBool enable_mouse)
{
    info_print("Initializing server...\n");

    int rbytespp = bits_per_pixel == 1 ? 1 : bytespp;
    int rframe_size = bits_per_pixel == 1 ? frame_size * 8 : frame_size;
    /* Allocate the VNC server buffer to be managed (not manipulated) by
     * libvncserver. */
    vncbuf = malloc(rframe_size);
    assert(vncbuf != NULL);
    memset(vncbuf, bits_per_pixel == 1 ? 0xFF : 0x00, rframe_size);

    /* Allocate the comparison buffer for detecting drawing updates from frame
     * to frame. */
    fbbuf = calloc(frame_size, 1);
    assert(fbbuf != NULL);

    /* TODO: This assumes var_scrinfo.bits_per_pixel is 16. */
    server = rfbGetScreen(&argc, argv, fb_xres, fb_yres, BITS_PER_SAMPLE, SAMPLES_PER_PIXEL, rbytespp);
    assert(server != NULL);

    server->desktopName = "framebuffer";
    server->frameBuffer = (char *)vncbuf;
    server->alwaysShared = TRUE;
    server->httpDir = NULL;
    server->port = vnc_port;

    /* Register VeNCrypt and stay compatible with older libvncserver.
     *
     * Preferred path (newer libvncserver): register as channel security
     * handler to advertise only type 19.
     *
     * Fallback path (older libvncserver): register regular handler and
     * reject type 2 via passwordCheck callback to preserve VeNCrypt-only
     * authentication policy, while avoiding link failure. */
    if (hashFilePath) {
#if defined(__GNUC__)
        if (rfbRegisterChannelSecurityHandler) {
            server->authPasswdData = NULL;
            server->passwordCheck = NULL;
            rfbRegisterChannelSecurityHandler(&vencryptSecurityHandler);
        } else
#endif
        {
            server->authPasswdData = (void *)hashFilePath;
            server->passwordCheck = reject_vncauth_password_check;
            rfbRegisterSecurityHandler(&vencryptSecurityHandler);
        }
    }

    server->kbdAddEvent = keyevent;
    if (enable_touch)
    {
        server->ptrAddEvent = ptrevent_touch;
    }

    if (enable_mouse)
    {
        server->ptrAddEvent = ptrevent_mouse;
    }
    

    rfbInitServer(server);

    /* Mark as dirty since we haven't sent any updates at all yet. */
    rfbMarkRectAsModified(server, 0, 0, fb_xres, fb_yres);

    /* No idea. */
    varblock.r_offset = var_scrinfo.red.offset + var_scrinfo.red.length - BITS_PER_SAMPLE;
    varblock.g_offset = var_scrinfo.green.offset + var_scrinfo.green.length - BITS_PER_SAMPLE;
    varblock.b_offset = var_scrinfo.blue.offset + var_scrinfo.blue.length - BITS_PER_SAMPLE;
    varblock.rfb_xres = fb_yres;
    varblock.rfb_maxy = fb_xres - 1;
}

// sec
#define LOG_TIME 5

int timeToLogFPS()
{
    static struct timeval now = {0, 0}, then = {0, 0};
    double elapsed, dnow, dthen;
    gettimeofday(&now, NULL);
    dnow = now.tv_sec + (now.tv_usec / 1000000.0);
    dthen = then.tv_sec + (then.tv_usec / 1000000.0);
    elapsed = dnow - dthen;
    if (elapsed > LOG_TIME)
        memcpy((char *)&then, (char *)&now, sizeof(struct timeval));
    return elapsed > LOG_TIME;
}

/*****************************************************************************/
//#define COLOR_MASK  0x1f001f
#define COLOR_MASK (((1 << BITS_PER_SAMPLE) << 1) - 1)
#define PIXEL_FB_TO_RFB(p, r_offset, g_offset, b_offset) \
    ((p >> r_offset) & COLOR_MASK) | (((p >> g_offset) & COLOR_MASK) << BITS_PER_SAMPLE) | (((p >> b_offset) & COLOR_MASK) << (2 * BITS_PER_SAMPLE))

static void update_screen(void)
{
#ifdef LOG_FPS
    if (verbose)
    {
        static int frames = 0;
        frames++;
        if (timeToLogFPS())
        {
            double fps = frames / LOG_TIME;
            info_print("  fps: %f\n", fps);
            frames = 0;
        }
    }
#endif

    varblock.min_i = varblock.min_j = 9999;
    varblock.max_i = varblock.max_j = -1;

    if (vnc_rotate == 0 && bits_per_pixel == 24)
    {
        uint8_t *f = (uint8_t *)fbmmap; /* -> framebuffer         */
        uint8_t *c = (uint8_t *)fbbuf;  /* -> compare framebuffer */
        uint8_t *r = (uint8_t *)vncbuf; /* -> remote framebuffer  */

        if (memcmp(fbmmap, fbbuf, frame_size) != 0)
        {
            int y;
            for (y = 0; y < (int)fb_yres; y++)
            {
                int x;
                for (x = 0; x < (int)fb_xres; x++)
                {
                    uint32_t pixel = *(uint32_t *)f & 0x00FFFFFF;
                    uint32_t comp = *(uint32_t *)c & 0x00FFFFFF;

                    if (pixel != comp)
                    {
                        *(c + 0) = *(f + 0);
                        *(c + 1) = *(f + 1);
                        *(c + 2) = *(f + 2);
                        uint32_t rem = PIXEL_FB_TO_RFB(pixel,
                                                       varblock.r_offset, varblock.g_offset, varblock.b_offset);
                        *(r + 0) = (uint8_t)((rem >> 0) & 0xFF);
                        *(r + 1) = (uint8_t)((rem >> 8) & 0xFF);
                        *(r + 2) = (uint8_t)((rem >> 16) & 0xFF);

                        if (x < varblock.min_i)
                            varblock.min_i = x;
                        else if (x > varblock.max_i)
                            varblock.max_i = x;

                        if (y > varblock.max_j)
                            varblock.max_j = y;
                        else if (y < varblock.min_j)
                            varblock.min_j = y;
                    }

                    f += bytespp;
                    c += bytespp;
                    r += bytespp;
                }
            }
        }
    }
    else if (vnc_rotate == 0 && bits_per_pixel == 1)
    {
        uint8_t *f = (uint8_t *)fbmmap; /* -> framebuffer         */
        uint8_t *c = (uint8_t *)fbbuf;  /* -> compare framebuffer */
        uint8_t *r = (uint8_t *)vncbuf; /* -> remote framebuffer  */

        int xstep = 8;
        if (memcmp(fbmmap, fbbuf, frame_size) != 0)
        {
            int y;
            for (y = 0; y < (int)fb_yres; y++)
            {
                int x;
                for (x = 0; x < (int)fb_xres; x += xstep)
                {
                    uint8_t pixels = *f;

                    if (pixels != *c)
                    {
                        *c = pixels;

                        for (int bit = 0; bit < 8; bit++)
                        {
                            // *(r+bit) = ((pixels >> (7-bit)) & 0x1) ? 0xFF : 0x00;
                            *(r + bit) = ((pixels >> (7 - bit)) & 0x1) ? 0x00 : 0xFF;
                        }

                        int x2 = x + xstep - 1;
                        if (x < varblock.min_i)
                            varblock.min_i = x;
                        else if (x2 > varblock.max_i)
                            varblock.max_i = x2;

                        if (y > varblock.max_j)
                            varblock.max_j = y;
                        else if (y < varblock.min_j)
                            varblock.min_j = y;
                    }

                    f += 1;
                    c += 1;
                    r += 8;
                }
            }
        }
    }
    else if (vnc_rotate == 0)
    {
        uint32_t *f = (uint32_t *)fbmmap; /* -> framebuffer         */
        uint32_t *c = (uint32_t *)fbbuf;  /* -> compare framebuffer */
        uint32_t *r = (uint32_t *)vncbuf; /* -> remote framebuffer  */

        if (memcmp(fbmmap, fbbuf, frame_size) != 0)
        {
            //        memcpy(fbbuf, fbmmap, size);

            int xstep = 4 / bytespp;

            int y;
            for (y = 0; y < (int)fb_yres; y++)
            {
                /* Compare every 1/2/4 pixels at a time */
                int x;
                for (x = 0; x < (int)fb_xres; x += xstep)
                {
                    uint32_t pixel = *f;

                    if (pixel != *c)
                    {
                        *c = pixel;

#if 0
                /* XXX: Undo the checkered pattern to test the efficiency
                 * gain using hextile encoding. */
                if (pixel == 0x18e320e4 || pixel == 0x20e418e3)
                    pixel = 0x18e318e3;
#endif
                        if (bytespp == 4)
                        {
                            *r = PIXEL_FB_TO_RFB(pixel,
                                                 varblock.r_offset, varblock.g_offset, varblock.b_offset);
                        }
                        else if (bytespp == 2)
                        {
                            *r = PIXEL_FB_TO_RFB(pixel,
                                                 varblock.r_offset, varblock.g_offset, varblock.b_offset);

                            uint32_t high_pixel = (0xffff0000 & pixel) >> 16;
                            uint32_t high_r = PIXEL_FB_TO_RFB(high_pixel, varblock.r_offset, varblock.g_offset, varblock.b_offset);
                            *r |= (0xffff & high_r) << 16;
                        }
                        else if (bytespp == 1)
                        {
                            *r = pixel;
                        }
                        else
                        {
                            // TODO
                        }

                        int x2 = x + xstep - 1;
                        if (x < varblock.min_i)
                            varblock.min_i = x;
                        else if (x2 > varblock.max_i)
                            varblock.max_i = x2;

                        if (y > varblock.max_j)
                            varblock.max_j = y;
                        else if (y < varblock.min_j)
                            varblock.min_j = y;
                    }

                    f++;
                    c++;
                    r++;
                }
            }
        }
    }
    else if (bits_per_pixel == 16)
    {
        uint16_t *f = (uint16_t *)fbmmap; /* -> framebuffer         */
        uint16_t *c = (uint16_t *)fbbuf;  /* -> compare framebuffer */
        uint16_t *r = (uint16_t *)vncbuf; /* -> remote framebuffer  */

        switch (vnc_rotate)
        {
        case 0:
        case 180:
            server->width = fb_xres;
            server->height = fb_yres;
            server->paddedWidthInBytes = fb_xres * bytespp;
            break;

        case 90:
        case 270:
            server->width = fb_yres;
            server->height = fb_xres;
            server->paddedWidthInBytes = fb_yres * bytespp;
            break;
        }

        if (memcmp(fbmmap, fbbuf, frame_size) != 0)
        {
            int y;
            for (y = 0; y < (int)fb_yres; y++)
            {
                /* Compare every pixels at a time */
                int x;
                for (x = 0; x < (int)fb_xres; x++)
                {
                    uint16_t pixel = *f;

                    if (pixel != *c)
                    {
                        int x2, y2;

                        *c = pixel;
                        switch (vnc_rotate)
                        {
                        case 0:
                            x2 = x;
                            y2 = y;
                            break;

                        case 90:
                            x2 = fb_yres - 1 - y;
                            y2 = x;
                            break;

                        case 180:
                            x2 = fb_xres - 1 - x;
                            y2 = fb_yres - 1 - y;
                            break;

                        case 270:
                            x2 = y;
                            y2 = fb_xres - 1 - x;
                            break;
                        default:
                            error_print("rotation is invalid\n");
                            exit(EXIT_FAILURE);
                        }

                        r[y2 * server->width + x2] = PIXEL_FB_TO_RFB(pixel, varblock.r_offset, varblock.g_offset, varblock.b_offset);

                        if (x2 < varblock.min_i)
                            varblock.min_i = x2;
                        else
                        {
                            if (x2 > varblock.max_i)
                                varblock.max_i = x2;

                            if (y2 > varblock.max_j)
                                varblock.max_j = y2;
                            else if (y2 < varblock.min_j)
                                varblock.min_j = y2;
                        }
                    }

                    f++;
                    c++;
                }
            }
        }
    }
    else
    {
        error_print("not supported color depth or rotation\n");
        exit(EXIT_FAILURE);
    }

    if (varblock.min_i < 9999)
    {
        if (varblock.max_i < 0)
            varblock.max_i = varblock.min_i;

        if (varblock.max_j < 0)
            varblock.max_j = varblock.min_j;

        debug_print("Dirty page: %dx%d+%d+%d...\n",
                    (varblock.max_i + 2) - varblock.min_i, (varblock.max_j + 1) - varblock.min_j,
                    varblock.min_i, varblock.min_j);

        rfbMarkRectAsModified(server, varblock.min_i, varblock.min_j,
                              varblock.max_i + 2, varblock.max_j + 1);
    }
}

/*****************************************************************************/

void print_usage(char **argv)
{
    info_print("%s [-f device] [-p port] [-t touchscreen] [-m mouse] [-k keyboard] [-r rotation] [-R touchscreen rotation] [-F FPS] [-H hashfile] [-W hashfile] [-v] [-h]\n"
               "-p port: VNC port, default is 5900\n"
               "-H hashfile: Argon2id password hash file (enables VeNCrypt Plain auth)\n"
               "-W hashfile: read password from stdin, write Argon2id hash to file, and exit\n"
               "-f device: framebuffer device node, default is /dev/fb0\n"
               "-k device: keyboard device node (example: /dev/input/event0)\n"
               "-t device: touchscreen device node (example:/dev/input/event2)\n"
               "-m device: mouse device node (example:/dev/input/event2)\n"
               "-r degrees: framebuffer rotation, default is 0\n"
               "-R degrees: touchscreen rotation, default is same as framebuffer rotation\n"
               "-F FPS: Maximum target FPS, default is 10\n"
               "-v: verbose\n"
               "-h: print this help\n",
               *argv);
}

/**
 * Read a password from stdin, hash it with Argon2id, and write the hash to a file.
 * @param hashFilePath  Path to the output hash file.
 * @return EXIT_SUCCESS on success, EXIT_FAILURE on error.
 */
static int write_password_hash_file(const char *hashFilePath)
{
    char password[256];
    memset(password, 0, sizeof(password));

    if (!fgets(password, sizeof(password), stdin) || password[0] == '\0' || password[0] == '\n') {
        error_print("no password provided on stdin\n");
        sodium_memzero(password, sizeof(password));
        return EXIT_FAILURE;
    }

    /* Strip trailing newline. */
    size_t plen = strlen(password);
    if (plen > 0 && password[plen - 1] == '\n') password[--plen] = '\0';

    if (plen == 0) {
        error_print("password is empty\n");
        sodium_memzero(password, sizeof(password));
        return EXIT_FAILURE;
    }

    char hash[crypto_pwhash_STRBYTES];
    /* Use minimal Argon2id parameters suitable for embedded ARM.
     * INTERACTIVE (m=64MB, t=2) takes ~5s on iMX6ULL (528MHz Cortex-A7),
     * exceeding VNC client timeouts.  MIN (m=8KB, t=1) verifies in <0.5s.
     * Brute-force is rate-limited by network latency + single-threaded server. */
    if (crypto_pwhash_str(hash,
                          password,
                          plen,
                          crypto_pwhash_OPSLIMIT_MIN,
                          crypto_pwhash_MEMLIMIT_MIN) != 0) {
        error_print("failed to hash password (out of memory?)\n");
        sodium_memzero(password, sizeof(password));
        return EXIT_FAILURE;
    }
    sodium_memzero(password, sizeof(password));

    int fd = open(hashFilePath, O_WRONLY | O_CREAT | O_TRUNC, 0600);
    if (fd < 0) {
        error_print("cannot open output file %s: %s\n", hashFilePath, strerror(errno));
        sodium_memzero(hash, sizeof(hash));
        return EXIT_FAILURE;
    }
    FILE *fp = fdopen(fd, "w");
    if (!fp) {
        error_print("fdopen failed for %s\n", hashFilePath);
        close(fd);
        sodium_memzero(hash, sizeof(hash));
        return EXIT_FAILURE;
    }

    fprintf(fp, "%s\n", hash);
    fclose(fp);
    sodium_memzero(hash, sizeof(hash));
    return EXIT_SUCCESS;
}

int main(int argc, char **argv)
{
    if (sodium_init() < 0) {
        error_print("failed to initialize libsodium\n");
        return EXIT_FAILURE;
    }

    if (argc > 1)
    {
        int i = 1;
        while (i < argc)
        {
            if (*argv[i] == '-')
            {
                switch (*(argv[i] + 1))
                {
                case 'h':
                    print_usage(argv);
                    exit(0);
                    break;
                case 'f':
                    i++;
                    if (argv[i])
                        strcpy(fb_device, argv[i]);
                    break;
                case 't':
                    i++;
                    if (argv[i])
                        strcpy(touch_device, argv[i]);
                    break;
                case 'm':
                    i++;
                    if (argv[i])
                        strcpy(mouse_device, argv[i]);
                    break;                    
                case 'k':
                    i++;
                    strcpy(kbd_device, argv[i]);
                    break;
                case 'p':
                    i++;
                    if (argv[i])
                        vnc_port = atoi(argv[i]);
                    break;
                case 'H':
                    i++;
                    if (argv[i])
                        hashFilePath = argv[i];
                    break;
                case 'W':
                    i++;
                    if (argv[i])
                        writeHashFile = argv[i];
                    break;
                case 'r':
                    i++;
                    if (argv[i])
                        vnc_rotate = atoi(argv[i]);
                    break;
                case 'R':
                    i++;
                    if (argv[i])
                        touch_rotate = atoi(argv[i]);
                    break;
               case 'F':
                    i++;
                    if (argv[i])
                        target_fps = atoi(argv[i]);
                    break;
                case 'v':
                    verbose = 1;
                    break;
                }
            }
            i++;
        }
    }

    /* -W mode: read password from stdin, hash it, write to file, exit. */
    if (writeHashFile) {
        return write_password_hash_file(writeHashFile);
    }

    /* Initialize GnuTLS only when starting the server (not needed for -W mode). */
    if (tls_init_global() != 0) {
        error_print("failed to initialize GnuTLS\n");
        return EXIT_FAILURE;
    }

    if (touch_rotate < 0)
        touch_rotate = vnc_rotate;

    info_print("Initializing framebuffer device %s...\n", fb_device);
    init_fb();
    if (strlen(kbd_device) > 0)
    {
        int ret = init_kbd(kbd_device);
        if (!ret)
            info_print("Keyboard device %s not available.\n", kbd_device);
    }
    else
    {
        info_print("No keyboard device\n");
    }

    rfbBool enable_touch = FALSE;
    rfbBool enable_mouse = FALSE;
    if(strlen(touch_device) > 0 && strlen(mouse_device) > 0)
    {
        error_print("It can't using both mouse and touch device.\n");
        exit(EXIT_FAILURE);
    }
    else if (strlen(touch_device) > 0)
    {
        // init touch only if there is a touch device defined
        int ret = init_touch(touch_device, touch_rotate);
        enable_touch = (ret > 0);
    }
    else if(strlen(mouse_device) > 0)
    {
        // init touch only if there is a mouse device defined
        int ret = init_mouse(mouse_device, touch_rotate);
        enable_mouse = (ret > 0);        
    }
    else
    {
        info_print("No touch or mouse device\n");
    }

    info_print("Initializing VNC server:\n");
    info_print("	width:  %d\n", (int)fb_xres);
    info_print("	height: %d\n", (int)fb_yres);
    info_print("	bpp:    %d\n", (int)var_scrinfo.bits_per_pixel);
    info_print("	port:   %d\n", (int)vnc_port);
    info_print("	authentication mode: %s\n", hashFilePath ? "VeNCrypt (Argon2id hash)" : "none");
    info_print("	rotate: %d\n", (int)vnc_rotate);
    info_print("  mouse/touch rotate: %d\n", (int)touch_rotate);
    info_print("    target FPS: %d\n", (int)target_fps);
    init_fb_server(argc, argv, enable_touch, enable_mouse);

    /* Implement our own event loop to detect changes in the framebuffer. */
    while (1)
    {
        rfbRunEventLoop(server, 100 * 1000, TRUE);
        while (rfbIsActive(server))
        {
            if (server->clientHead != NULL)
                update_screen();

            if (target_fps > 0)
                usleep(1000 * 1000 / target_fps);
            else if (server->clientHead == NULL)
                usleep(100 * 1000);
        }
    }

    info_print("Cleaning up...\n");
    cleanup_fb();
    cleanup_kbd();
    cleanup_touch();
}
