project(Examples)

add_executable(test-depend depend.cc)
target_link_libraries(test-depend LINK_PUBLIC dependent-cxx)

add_executable(test-log2 log2.cc)
target_link_libraries(test-log2 LINK_PUBLIC dependent-cxx)

add_executable(test-array-concat array-concat.cc)
target_link_libraries(test-array-concat LINK_PUBLIC dependent-cxx)