cmake_minimum_required(VERSION 3.11)
project(tests)

set(CMAKE_VERBOSE_MAKEFILE ON)

add_executable(SimpleTest1 SimpleTest1.c)
add_executable(LoopTest1 LoopTest1.c)
add_executable(randacc randacc.c)

configure_file(SimpleTest1.c ${CMAKE_CURRENT_BINARY_DIR}/SimpleTest1.c COPYONLY)
configure_file(LoopTest1.c ${CMAKE_CURRENT_BINARY_DIR}/LoopTest1.c COPYONLY)
configure_file(randacc.c ${CMAKE_CURRENT_BINARY_DIR}/randacc.c COPYONLY)