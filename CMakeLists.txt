cmake_minimum_required(VERSION 3.0.0)
project(unslr VERSION 0.1.0)

# Files
# sort lists to avoid dependency on readdir() order and make build reproducible
FILE(GLOB srcs
  src/*.c
)
LIST(SORT srcs) 

include(CTest)
enable_testing()

add_executable(unslr ${srcs})
set_directory_properties(PROPERTIES COMPILE_DEFINITIONS "UNSLR")

set(CPACK_PROJECT_NAME ${PROJECT_NAME})
set(CPACK_PROJECT_VERSION ${PROJECT_VERSION})
include(CPack)
