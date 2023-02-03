#!/usr/bin/env bash

mkdir -p build
pushd build

cmake -DLLVM_ENABLE_PROJECTS="clang;clang-tools-extra;lldb;lld" \
      -DLLVM_TARGETS_TO_BUILD="WebAssembly" \
      -DLLVM_TARGET_ARCH="wasm32" \
      -DLLVM_DEFAULT_TARGET_TRIPLE="wasm32-unknown-wasi" \
      -DCMAKE_BUILD_TYPE="Debug" \
      -DLLVM_ENABLE_ASSERTIONS="ON" \
      -DCMAKE_EXPORT_COMPILE_COMMANDS="ON" \
      -DLLVM_CCACHE_BUILD="ON" \
      -DLLVM_ENABLE_LLD="ON" \
      -DCMAKE_C_COMPILER="clang" \
      -DCMAKE_CXX_COMPILER="clang++" \
      -G "Ninja" \
      ../llvm

popd
      # -DLLVM_ENABLE_ZLIB="ON" \

# pushd compiler-rt

# BUILD_PREFIX=$PWD/..
# ROOT_DIR=$PWD/../..
# CLANG_VERSION=17

# echo ROOT_DIR $ROOT_DIR

# VERBOSE=1 cmake -G Ninja \
#       -DCMAKE_C_COMPILER_WORKS=ON \
#       -DCMAKE_CXX_COMPILER_WORKS=ON \
#       -DCMAKE_AR=$BUILD_PREFIX/bin/ar \
#       -DCMAKE_MODULE_PATH=$ROOT_DIR/cmake \
#       -DCMAKE_BUILD_TYPE=RelWithDebInfo \
#       -DLLVM_CMAKE_DIR=$ROOT_DIR/llvm \
#       -DCOMPILER_RT_BAREMETAL_BUILD=On \
#       -DCOMPILER_RT_BUILD_XRAY=OFF \
#       -DCOMPILER_RT_INCLUDE_TESTS=OFF \
#       -DCOMPILER_RT_HAS_FPIC_FLAG=OFF \
#       -DCOMPILER_RT_ENABLE_IOS=OFF \
#       -DCOMPILER_RT_DEFAULT_TARGET_ONLY=On \
#       -DWASI_SDK_PREFIX=/scratch/martin/src/wasm/wasi-libc \
#       -DCMAKE_C_FLAGS="--sysroot=/scratch/martin/src/wasm/wasi-libc/sysroot" \
#       -DLLVM_CONFIG_PATH=$BUILD_PREFIX/llvm/bin/llvm-config \
#       -DCOMPILER_RT_OS_DIR=wasi \
#       -DCMAKE_INSTALL_PREFIX=../llvm/lib/clang/lib/clang/$CLANG_VERSION/ \
#       -DCMAKE_VERBOSE_MAKEFILE:BOOL=ON \
#       ../../compiler-rt/lib/builtins

# popd

# popd


#       # -DCMAKE_C_COMPILER_WORKS=ON \
#       # -DCMAKE_CXX_COMPILER_WORKS=ON \
#       # -DCMAKE_SYSROOT="/scratch/martin/src/wasm/wasi-libc/sysroot" \
#       # -DLLVM_CMAKE_DIR="$PWD/../llvm" \
#       # -DCMAKE_BUILD_TYPE=RelWithDebInfo \
#       # -DCOMPILER_RT_BAREMETAL_BUILD=On \
#       # -DLLVM_CONFIG_PATH="$PWD/../llvm/bin/llvm-config" \
#       # -DCOMPILER_RT_DEFAULT_TARGET_ARCH="wasm32-unknown-wasi" \
#       # -DCOMPILER_RT_DEFAULT_TARGET_TRIPLE="wasm32-unknown-wasi" \
