#!/usr/bin/env bash

mkdir -p build
pushd build

cmake -DLLVM_ENABLE_PROJECTS="clang;clang-tools-extra;lldb;lld" \
      -DLLVM_TARGETS_TO_BUILD="WebAssembly" \
      -DLLVM_TARGET_ARCH="wasm32" \
      -DLLVM_DEFAULT_TARGET_TRIPLE="wasm32-unknown-wasi" \
      -DCMAKE_BUILD_TYPE="DEBUG" \
      -DLLVM_ENABLE_ASSERTIONS="ON" \
      -DCMAKE_EXPORT_COMPILE_COMMANDS="ON" \
      -DLLVM_CCACHE_BUILD="ON" \
      -DLLVM_ENABLE_LLD="ON" \
      -DCMAKE_C_COMPILER="clang" \
      -DCMAKE_CXX_COMPILER="clang++" \
      -DLLVM_ENABLE_ZLIB="ON" \
      -G "Ninja" \
      ../llvm

popd
