cmake_minimum_required(VERSION 3.11)
project(prefetch)

set(CMAKE_VERBOSE_MAKEFILE ON)
set(CMAKE_SHARED_LIBRARY_SUFFIX .so)

#===============================================================================
# 1. LOAD LLVM CONFIGURATION
#===============================================================================
# Set this to a valid LLVM installation dir
set(LT_LLVM_INSTALL_DIR "" CACHE PATH "LLVM installation directory")

# Add the location of LLVMConfig.cmake to CMake search paths (so that
# find_package can locate it)
list(APPEND CMAKE_PREFIX_PATH "${LT_LLVM_INSTALL_DIR}/lib/cmake/llvm/")

# FIXME: This is a warkaround for #25. Remove once resolved and use
# find_package(LLVM 11.0.0 REQUIRED CONFIG) instead.
find_package(LLVM REQUIRED CONFIG)

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")

#===============================================================================
# 2. BUILD CONFIGURATION
#===============================================================================
# Use the same C++ standard as LLVM does
# TODO: fix to 14 version
set(CMAKE_CXX_STANDARD 20 CACHE STRING "")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wunused-function")
#set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall")

# LLVM is normally built without RTTI. Be consistent with that.
if(NOT LLVM_ENABLE_RTTI)
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fno-rtti")
endif()

#===============================================================================
# 3. ADD THE TARGET
#===============================================================================
add_library(PrefetchIndirect SHARED
            PrefetchIndirect.cpp PrefetchIndirect.h
            RegisterPasses.cpp)

# Allow undefined symbols in shared objects on Darwin (this is the default
# behaviour on Linux)
target_link_libraries(PrefetchIndirect
        "$<$<PLATFORM_ID:Darwin>:-undefined dynamic_lookup>")


add_subdirectory(tests)