cmake_minimum_required(VERSION 3.6)
project(ttbb)
message(STATUS $ENV{TBBROOT})
include_directories($ENV{TBBROOT}/include)
link_directories(${TBBROOT}/lib)

set(SOURCE_FILES
        tbb_basic.cpp)

add_executable(ttbb ${SOURCE_FILES})