cmake_minimum_required(VERSION 3.22)
# C is enabled only because LLVMConfig.cmake runs C feature checks (FindLibEdit).
project(CrossCheck VERSION 0.1.0 LANGUAGES C CXX)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)
set(CMAKE_POSITION_INDEPENDENT_CODE ON)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)
if(NOT CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE Release)
endif()

find_package(LLVM REQUIRED CONFIG)
find_package(Clang REQUIRED CONFIG)
find_package(Z3 CONFIG QUIET)
if(NOT Z3_FOUND)
  # Some distributions (e.g. Ubuntu's libz3-dev) ship no CMake package file.
  find_path(Z3_CXX_INCLUDE_DIRS z3++.h PATH_SUFFIXES z3 REQUIRED)
  find_library(Z3_LIBRARY NAMES z3 REQUIRED)
  add_library(z3::libz3 UNKNOWN IMPORTED)
  set_target_properties(z3::libz3 PROPERTIES
    IMPORTED_LOCATION "${Z3_LIBRARY}"
    INTERFACE_INCLUDE_DIRECTORIES "${Z3_CXX_INCLUDE_DIRS}")
  set(Z3_VERSION_STRING "(found without CMake package: ${Z3_LIBRARY})")
endif()
message(STATUS "LLVM ${LLVM_PACKAGE_VERSION}, Z3 ${Z3_VERSION_STRING}")
if(LLVM_VERSION_MAJOR LESS 18)
  message(FATAL_ERROR "CrossCheck needs LLVM/Clang 18 or newer")
endif()

add_compile_options(-Wall -Wextra)

# --- core: affine expressions and the SMT back-end (no Clang dependency) -----
add_library(crosscheck_core STATIC
  src/core/LinExpr.cpp
  src/core/Solver.cpp
  src/core/Cert.cpp)
target_include_directories(crosscheck_core PUBLIC src)
target_include_directories(crosscheck_core SYSTEM PRIVATE ${Z3_CXX_INCLUDE_DIRS})
target_link_libraries(crosscheck_core PUBLIC z3::libz3)

# --- analysis: the Clang AST walker -----------------------------------------
add_library(crosscheck_analysis STATIC
  src/analysis/Analyzer.cpp
  src/analysis/Consumer.cpp
  src/analysis/Export.cpp
  src/analysis/MiniC.cpp
  src/analysis/Report.cpp)
target_include_directories(crosscheck_analysis PUBLIC src)
target_include_directories(crosscheck_analysis SYSTEM PUBLIC ${LLVM_INCLUDE_DIRS} ${CLANG_INCLUDE_DIRS})
target_compile_definitions(crosscheck_analysis PUBLIC ${LLVM_DEFINITIONS})
if(NOT LLVM_ENABLE_RTTI)
  target_compile_options(crosscheck_analysis PUBLIC -fno-rtti)
endif()
target_link_libraries(crosscheck_analysis PUBLIC crosscheck_core)
target_compile_definitions(crosscheck_analysis PRIVATE CROSSCHECK_VERSION="${PROJECT_VERSION}")

# --- the compiler plugin: clang++ -fplugin=libCrossCheckPlugin.so ------------
# Clang symbols are resolved against the host compiler, so no Clang library is
# linked here.
add_library(CrossCheckPlugin MODULE src/plugin/Plugin.cpp)
target_link_libraries(CrossCheckPlugin PRIVATE crosscheck_analysis)
set_target_properties(CrossCheckPlugin PROPERTIES PREFIX "lib")

# --- the standalone tool: crosscheck-tool file.cpp -- <compiler flags> -------
find_program(CROSSCHECK_CLANGXX NAMES clang++ PATHS ${LLVM_TOOLS_BINARY_DIR} NO_DEFAULT_PATH)
if(NOT CROSSCHECK_CLANGXX)
  find_program(CROSSCHECK_CLANGXX NAMES clang++ REQUIRED)
endif()
execute_process(COMMAND ${CROSSCHECK_CLANGXX} -print-resource-dir
  OUTPUT_VARIABLE CROSSCHECK_RESOURCE_DIR OUTPUT_STRIP_TRAILING_WHITESPACE)

if(CLANG_LINK_CLANG_DYLIB OR TARGET clang-cpp)
  set(CROSSCHECK_CLANG_LIBS clang-cpp LLVM)
else()
  set(CROSSCHECK_CLANG_LIBS clangTooling clangFrontend clangAST clangBasic)
endif()

add_executable(crosscheck-tool src/tool/Main.cpp)
target_compile_definitions(crosscheck-tool PRIVATE
  CROSSCHECK_RESOURCE_DIR="${CROSSCHECK_RESOURCE_DIR}")
target_link_libraries(crosscheck-tool PRIVATE crosscheck_analysis ${CROSSCHECK_CLANG_LIBS})

# --- tests --------------------------------------------------------------------
# Extra flags for the Clang front-end in the tests, e.g. when Clang must be
# pointed at a particular libstdc++: --gcc-install-dir=/usr/lib/gcc/x86_64-linux-gnu/13
set(CROSSCHECK_CLANG_EXTRA_FLAGS "" CACHE STRING "Extra Clang flags used by the tests")
separate_arguments(CROSSCHECK_CLANG_EXTRA_FLAGS_LIST UNIX_COMMAND "${CROSSCHECK_CLANG_EXTRA_FLAGS}")
include(CTest)
if(BUILD_TESTING)
  find_package(GTest REQUIRED)
  include(GoogleTest)

  add_executable(core_test tests/core_test.cpp)
  target_link_libraries(core_test PRIVATE crosscheck_core GTest::gtest_main)
  gtest_discover_tests(core_test)

  add_executable(analyzer_test tests/analyzer_test.cpp tests/benchmarks_test.cpp tests/export_test.cpp)
  target_compile_definitions(analyzer_test PRIVATE
    CROSSCHECK_RESOURCE_DIR="${CROSSCHECK_RESOURCE_DIR}"
    CROSSCHECK_CLANG_EXTRA_FLAGS="${CROSSCHECK_CLANG_EXTRA_FLAGS}"
    CROSSCHECK_INCLUDE_DIR="${CMAKE_CURRENT_SOURCE_DIR}/include"
    CROSSCHECK_BENCHMARK_DIR="${CMAKE_CURRENT_SOURCE_DIR}/../benchmarks")
  target_include_directories(analyzer_test PRIVATE src tests)
  target_link_libraries(analyzer_test PRIVATE crosscheck_analysis ${CROSSCHECK_CLANG_LIBS}
    GTest::gtest_main)
  gtest_discover_tests(analyzer_test DISCOVERY_TIMEOUT 120)

  # End-to-end: the plugin loaded into the compiler itself.
  set(BENCH ${CMAKE_CURRENT_SOURCE_DIR}/../benchmarks)
  set(PLUGIN_FLAGS -std=c++20 -fsyntax-only -I${CMAKE_CURRENT_SOURCE_DIR}/include
      -fplugin=$<TARGET_FILE:CrossCheckPlugin> ${CROSSCHECK_CLANG_EXTRA_FLAGS_LIST})
  foreach(name fir_filter pid_controller divide_and_conquer can_frame_decoder
               ring_buffer_isr crc_table motor_ramp)
    add_test(NAME plugin_accepts_${name}
      COMMAND ${CROSSCHECK_CLANGXX} ${PLUGIN_FLAGS} ${BENCH}/${name}.cpp)
  endforeach()
  # Flow facts (FFX, AIS, AIS2) and SARIF read back; SARIF validated against its schema
  # when -DCROSSCHECK_SARIF_SCHEMA=<sarif-schema-2.1.0.json> is given.
  find_package(Python3 COMPONENTS Interpreter)
  set(CROSSCHECK_SARIF_SCHEMA "" CACHE FILEPATH "SARIF 2.1.0 JSON schema (optional)")
  if(Python3_FOUND)
    set(SCHEMA_ARG)
    if(CROSSCHECK_SARIF_SCHEMA)
      set(SCHEMA_ARG --sarif-schema ${CROSSCHECK_SARIF_SCHEMA})
    endif()
    add_test(NAME exports_read_back
      COMMAND ${Python3_EXECUTABLE} ${CMAKE_CURRENT_SOURCE_DIR}/tests/check_exports.py
        $<TARGET_FILE:crosscheck-tool> ${BENCH} ${CMAKE_CURRENT_SOURCE_DIR}/include ${SCHEMA_ARG}
        -- ${CROSSCHECK_CLANG_EXTRA_FLAGS_LIST})
    add_test(NAME c_annotations
      COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/tests/check_c.sh $<TARGET_FILE:crosscheck-tool>
        ${CMAKE_CURRENT_SOURCE_DIR}/tests/c/annotations.c ${CMAKE_CURRENT_SOURCE_DIR}/include
        ${CROSSCHECK_CLANG_EXTRA_FLAGS_LIST})
    add_test(NAME bounds_equal_baseline
      COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/tests/check_baseline.sh $<TARGET_FILE:crosscheck-tool>
        ${BENCH} ${CMAKE_CURRENT_SOURCE_DIR}/include ${Python3_EXECUTABLE} ${CROSSCHECK_CLANG_EXTRA_FLAGS_LIST})
  endif()
  # Certificates checked by the verified Lean checker (formalization/: lake build crosscheck-check).
  set(CROSSCHECK_CHECKER "" CACHE FILEPATH "Path to the crosscheck-check executable (optional)")
  if(CROSSCHECK_CHECKER)
    add_test(NAME certificates_accepted_by_lean_checker
      COMMAND ${CMAKE_CURRENT_SOURCE_DIR}/tests/check_certificates.sh $<TARGET_FILE:crosscheck-tool>
        ${CROSSCHECK_CHECKER} "${BENCH}:${CMAKE_CURRENT_SOURCE_DIR}/tests/certificates" ${CMAKE_CURRENT_SOURCE_DIR}/include ${CROSSCHECK_CLANG_EXTRA_FLAGS_LIST})
    if(Python3_FOUND)
      add_test(NAME minic_sources_validated
        COMMAND ${Python3_EXECUTABLE} ${CMAKE_CURRENT_SOURCE_DIR}/tests/check_minic.py
          $<TARGET_FILE:crosscheck-tool> ${CROSSCHECK_CHECKER} ${CMAKE_CURRENT_SOURCE_DIR}/tests/c/minic.c
          ${CMAKE_CURRENT_SOURCE_DIR}/include ${CROSSCHECK_CLANG_EXTRA_FLAGS_LIST})
      # Random loop programs: no derived loop bound below an executed count, and every
      # certificate emitted for them accepted (tests/fuzz_bounds.py; fixed seed).
      add_test(NAME random_loops_bounds_hold
        COMMAND ${Python3_EXECUTABLE} ${CMAKE_CURRENT_SOURCE_DIR}/tests/fuzz_bounds.py
          $<TARGET_FILE:crosscheck-tool> ${CMAKE_CURRENT_SOURCE_DIR}/include
          --checker ${CROSSCHECK_CHECKER} --cxx ${CMAKE_CXX_COMPILER} --files 3 --seed 1
          -- ${CROSSCHECK_CLANG_EXTRA_FLAGS_LIST})
      # Mutated certificates: rejected by the checker, or still true when run by an
      # independent interpreter (formalization/test/mutate_certificates.py).
      add_test(NAME checker_mutants_rejected_or_sound
        COMMAND ${Python3_EXECUTABLE}
          ${CMAKE_CURRENT_SOURCE_DIR}/../formalization/test/mutate_certificates.py
          ${CROSSCHECK_CHECKER}
          ${CMAKE_CURRENT_SOURCE_DIR}/../formalization/test/certificates/program.json
          ${CMAKE_CURRENT_SOURCE_DIR}/../formalization/test/certificates/triangular.json
          --mutants 150)
    endif()
  endif()
  foreach(name rejected_allocation rejected_unbounded_loop rejected_deadline)
    add_test(NAME plugin_rejects_${name}
      COMMAND ${CROSSCHECK_CLANGXX} ${PLUGIN_FLAGS} ${BENCH}/${name}.cpp)
    set_tests_properties(plugin_rejects_${name} PROPERTIES WILL_FAIL TRUE)
  endforeach()
endif()
