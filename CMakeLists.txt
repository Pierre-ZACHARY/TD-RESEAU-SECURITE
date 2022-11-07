# cmake_minimum_required(VERSION <specify CMake version here>)
project(Supports_de_TD_20220919 C)
cmake_minimum_required(VERSION 3.23)

set(CMAKE_C_STANDARD 11)

include_directories(.)
include_directories(exercises01)
include_directories(exercises02)
include_directories(exercises03)

add_executable(Supports_de_TD_20220919
        exercises03/concat.c)
