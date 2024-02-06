#!/usr/bin/env bash

mkdir -p build
pushd build

cmake -DLLVM_ENABLE_PROJECTS="clang;clang-tools-extra;lldb;lld" \
      -DLLVM_TARGETS_TO_BUILD="ARM;AArch64;RISCV" \
      -DLLVM_TARGET_ARCH="aarch64" \
      -DLLVM_DEFAULT_TARGET_TRIPLE="aarch64-unknown-linux" \
      -DCMAKE_BUILD_TYPE="RelWithDebInfo" \
      -DLLVM_ENABLE_ASSERTIONS="ON" \
      -DCMAKE_EXPORT_COMPILE_COMMANDS="ON" \
      -DLLVM_CCACHE_BUILD="ON" \
      -DLLVM_ENABLE_LLD="OFF" \
      -DLLVM_USE_LINKER="mold" \
      -DCMAKE_C_COMPILER="clang" \
      -DCMAKE_CXX_COMPILER="clang++" \
      -DLLVM_PARALLEL_LINK_JOBS=1 \
      -G "Ninja" \
      ../llvm

popd

