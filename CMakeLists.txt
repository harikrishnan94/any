project(any)
cmake_minimum_required(VERSION 3.10)
enable_testing()

set(CMAKE_CXX_FLAGS "-std=c++17 -Wall -Wextra")

add_executable(test_any test_any.cpp)
add_test(test_any test_any)
