cmake_minimum_required(VERSION 3.5)
project(tbb_tests)

link_libraries(tbb)

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11 -ltbb -O3")

set(SOURCE_FILES
        Examples/SimpleExamples.cpp
        Examples/Stopwatch.cpp
        Examples/Stopwatch.h
        Examples/ExampleUnit.h
        second_min.cpp
        main.cpp
        )

add_executable(tbb_test ${SOURCE_FILES})