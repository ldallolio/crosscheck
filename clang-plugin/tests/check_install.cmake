# Copyright (c) 2026 Luca Dall'Olio. Released under the MIT license.
#
# Installs the build tree BUILD_DIR into PREFIX, then runs the installed crosscheck-tool and the
# installed plugin (loaded into CLANGXX) on EXAMPLE with the installed annotation header.
# BINDIR, LIBDIR, INCLUDEDIR, DOCDIR: the installation directories, relative to PREFIX.
file(REMOVE_RECURSE "${PREFIX}")
execute_process(COMMAND "${CMAKE_COMMAND}" --install "${BUILD_DIR}" --prefix "${PREFIX}"
  RESULT_VARIABLE rc OUTPUT_QUIET)
if(NOT rc EQUAL 0)
  message(FATAL_ERROR "cmake --install failed (${rc})")
endif()
separate_arguments(extra UNIX_COMMAND "${EXTRA}")
set(tool "${PREFIX}/${BINDIR}/crosscheck-tool")
file(GLOB plugin "${PREFIX}/${LIBDIR}/crosscheck/libCrossCheckPlugin.*")
set(inc "${PREFIX}/${INCLUDEDIR}")
foreach(f "${tool}" "${plugin}" "${inc}/crosscheck/attributes.hpp"
          "${PREFIX}/${DOCDIR}/LICENSE")
  if(NOT EXISTS "${f}")
    message(FATAL_ERROR "not installed: ${f}")
  endif()
endforeach()
execute_process(COMMAND "${tool}" --summary "${EXAMPLE}" -- -std=c++20 "-I${inc}" ${extra}
  RESULT_VARIABLE rc OUTPUT_VARIABLE out ERROR_VARIABLE err)
if(NOT rc EQUAL 0 OR NOT out MATCHES "OK ")
  message(FATAL_ERROR "installed crosscheck-tool failed (${rc}):\n${out}\n${err}")
endif()
execute_process(COMMAND "${CLANGXX}" -std=c++20 -fsyntax-only "-I${inc}" "-fplugin=${plugin}" ${extra}
  "${EXAMPLE}" RESULT_VARIABLE rc ERROR_VARIABLE err)
if(NOT rc EQUAL 0)
  message(FATAL_ERROR "installed plugin failed (${rc}):\n${err}")
endif()
file(REMOVE_RECURSE "${PREFIX}")
