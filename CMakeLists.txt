# cmake_minimum_required(VERSION <specify CMake version here>)
project(Supports_de_TD_20220919 C)

set(CMAKE_C_STANDARD 11)

include_directories(.)
include_directories(exercises01)
include_directories(exercises02)
include_directories(exercises03)

add_executable(Supports_de_TD_20220919
        exercises01/compare.c
        exercises01/compare_problem.c
        exercises01/identity.c
        exercises01/mid.c
        exercises02/increment.c
        exercises02/is_null.c
        exercises02/is_positive.c
        exercises02/is_positive_void.c
        exercises02/max.c
        exercises02/swap.c
        exercises03/concat.c
        exercises03/is_negative.c
        exercises03/is_negative_rl.c)
