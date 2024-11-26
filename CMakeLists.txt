cmake_minimum_required(VERSION 3.13.5)

set(CMAKE_CXX_STANDARD 17)
project(Dependent-Cxx)

set(dependent_cxx_INCLUDE_DIR ${CMAKE_CURRENT_SOURCE_DIR}/include)
set(base_path ${dependent_cxx_INCLUDE_DIR}/dependent-cxx)

add_library(dependent-cxx INTERFACE)
target_sources(dependent-cxx INTERFACE
 ${base_path}/algebra.hpp
 ${base_path}/array.hpp
 ${base_path}/core.hpp
 ${base_path}/core-io.hpp
 )
target_include_directories(dependent-cxx INTERFACE ${dependent_cxx_INCLUDE_DIR})
target_compile_options(dependent-cxx INTERFACE -Wall -Wextra)


add_subdirectory(example)
