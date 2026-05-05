PROJECT(framebuffer-vncserver)
CMAKE_MINIMUM_REQUIRED(VERSION 2.6)


FILE(GLOB SOURCES src/*.c)
ADD_EXECUTABLE(framebuffer-vncserver ${SOURCES})
INSTALL(TARGETS framebuffer-vncserver RUNTIME DESTINATION bin)

# LIBVNC
find_library(LIBVNC NAMES libvncserver vncserver)
find_library(LIBSODIUM NAMES sodium)
find_library(LIBGNUTLS NAMES gnutls)

if(NOT LIBVNC)
  message(FATAL_ERROR "Required library not found: libvncserver")
endif()

if(NOT LIBSODIUM)
  message(FATAL_ERROR "Required library not found: sodium")
endif()

if(NOT LIBGNUTLS)
  message(FATAL_ERROR "Required library not found: gnutls")
endif()

target_link_libraries(framebuffer-vncserver ${LIBVNC} ${LIBSODIUM} ${LIBGNUTLS})


MESSAGE( STATUS "LIBVNC:         " ${LIBVNC} )
MESSAGE( STATUS "LIBSODIUM:      " ${LIBSODIUM} )
MESSAGE( STATUS "LIBGNUTLS:      " ${LIBGNUTLS} )
