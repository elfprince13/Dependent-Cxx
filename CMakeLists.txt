cmake_minimum_required(VERSION 3.13.5)

set(CMAKE_CXX_STANDARD 17)
project(Dependent-Cxx)

set(DEPND_INCLUDE_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/include)
set(DEPND_LIBRARY_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/lib)
find_package(Boost 1.73)

#add_subdirectory(Cxx-Heterogeneous-Maps)
add_executable(test-depend example/depend.cc)
target_compile_options(test-depend PUBLIC -Wall -Wextra)
target_link_libraries(test-depend LINK_PUBLIC Boost::boost) #static-hmap)
