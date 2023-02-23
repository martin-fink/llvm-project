// WebAssemblyInstrMemSafety.td - WebAssembly MemSafety codegen support -*- tablegen -*-//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
///
/// \file
/// WebAssembly SIMD operand code-gen constructs.
///
//===----------------------------------------------------------------------===//

// defm I64_TRUNC_U_SAT_F64 : I<(outs I64:$dst), (ins F64:$src), (outs), (ins),
//                              [(set I64:$dst, (fp_to_uint F64:$src))],
//                              "i64.trunc_sat_f64_u\t$dst, $src",
//                              "i64.trunc_sat_f64_u", 0xfc07>,
//                              Requires<[HasNontrappingFPToInt]>;

// TODO(Martin): add instructions like the ones above
