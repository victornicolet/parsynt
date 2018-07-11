cmake_minimum_required(VERSION 3.5)
project(NestedLoopsExperiments)

link_libraries(tbb)

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11 -ltbb -fopenmp")

set(SOURCE_FILES gradient1.cpp)
# All experiment executables start with prefix Exp
add_executable(Exp2DSum sum2d.cpp StopWatch.cpp StopWatch.h param.h)
add_executable(Exp2DSorted sorted2d.cpp StopWatch.cpp StopWatch.h param.h)
add_executable(ExpGradient1 gradient1.cpp StopWatch.cpp StopWatch.h param.h)
add_executable(ExpGradient2 gradient2.cpp StopWatch.cpp StopWatch.h param.h)
add_executable(ExpMaxLeftRect max_left_rec.cpp StopWatch.cpp StopWatch.h param.h)
#TODO
add_executable(ExpMaxTopStrip max_top_strip.cpp StopWatch.cpp StopWatch.h param.h)
add_executable(ExpMaxBottomStrip max_bottom_strip.cpp StopWatch.cpp StopWatch.h param.h)
add_executable(ExpMaxSegStrip max_seg_strip.cpp StopWatch.cpp StopWatch.h param.h)