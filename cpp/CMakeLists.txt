add_library(peering_state STATIC
  peering_state.cc
)

target_include_directories(peering_state
  PUBLIC
    ${CMAKE_CURRENT_SOURCE_DIR}
)

target_compile_features(peering_state PUBLIC cxx_std_20)

add_executable(cross_validate
  cross_validate.cc
)

target_link_libraries(cross_validate
  PRIVATE
    peering_state
)
