cmake_minimum_required(VERSION 3.13)
project(mallocLab C)

set(CMAKE_C_STANDARD 11)
SET(CMAKE_C_FLAGS_DEBUG
        "-Wall -Wextra -O3 -g -DDRIVER -std=gnu99 -Wno-unused-function -Wno-unused-parameter")

add_executable(mdriver mdriver.c mm.c mm.h memlib.c memlib.h fsecs.c fsecs.h fcyc.c fcyc.h clock.c
        clock.h ftimer.c ftimer.h config.h)