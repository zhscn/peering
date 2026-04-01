include(FetchContent)

FetchContent_Declare(
  glaze
  GIT_REPOSITORY https://github.com/stephenberry/glaze
  GIT_TAG v7.2.2
  GIT_SHALLOW TRUE
)

FetchContent_Declare(
  fmt
  GIT_REPOSITORY https://github.com/fmtlib/fmt
  GIT_TAG 12.1.0
  GIT_SHALLOW TRUE
)

FetchContent_MakeAvailable(glaze fmt)

add_library(peering_state STATIC
  peering_state.cc
)

target_include_directories(peering_state
  PUBLIC
    ${CMAKE_CURRENT_SOURCE_DIR}
)

target_compile_features(peering_state PUBLIC cxx_std_23)

add_executable(cross_validate
  cross_validate.cc
)

target_link_libraries(cross_validate
  PRIVATE
    peering_state
    glaze::glaze
    fmt::fmt
)
