// WebAssemblyInstrMemory.td-WebAssembly Memory codegen support -*- tablegen -*-
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
///
/// \file
/// WebAssembly Memory operand code-gen constructs.
///
//===----------------------------------------------------------------------===//

// TODO:
//  - WebAssemblyTargetLowering having to do with atomics
//  - Each has optional alignment.

// WebAssembly has i8/i16/i32/i64/f32/f64 memory types, but doesn't have i8/i16
// local types. These memory-only types instead zero- or sign-extend into local
// types when loading, and truncate when storing.

// Address Operands

// These patterns match the static (offset) and dynamic (address stack operand)
// operands for loads and stores, based on a combination of target global
// addresses and constants.
// For example,
// (load (add tga, x))   -> load offset=tga, addr=x
// (store v, tga)        -> store v, offset=tga, addr=0
// (load (add const, x)) -> load offset=const, addr=x
// (store v, const)      -> store v, offset=const, addr=0
// (load x)              -> load offset=0, addr=x
def AddrOps32 : ComplexPattern<i32, 2, "SelectAddrOperands32">;
def AddrOps64 : ComplexPattern<i64, 2, "SelectAddrOperands64">;

// Defines atomic and non-atomic loads, regular and extending.
multiclass WebAssemblyLoad<WebAssemblyRegClass rc, string Name, int Opcode,
                           list<Predicate> reqs = []> {
  let mayLoad = 1, UseNamedOperandTable = 1 in {
  defm "_A32": I<(outs rc:$dst),
                 (ins P2Align:$p2align, offset32_op:$off, I32:$addr),
                 (outs), (ins P2Align:$p2align, offset32_op:$off),
                 [], !strconcat(Name, "\t$dst, ${off}(${addr})${p2align}"),
                 !strconcat(Name, "\t${off}${p2align}"), Opcode, false>,
               Requires<reqs # [HasNoMemSafety]>;
  defm "_A64": I<(outs rc:$dst),
                 (ins P2Align:$p2align, offset64_op:$off, I64:$addr),
                 (outs), (ins P2Align:$p2align, offset64_op:$off),
                 [], !strconcat(Name, "\t$dst, ${off}(${addr})${p2align}"),
                 !strconcat(Name, "\t${off}${p2align}"), Opcode, true>,
               Requires<reqs # [HasNoMemSafety]>;
  defm "_A32_SAFE": I<(outs rc:$dst),
                 (ins P2Align:$p2align, offset32_op:$off, HANDLE:$addr),
                 (outs), (ins P2Align:$p2align, offset32_op:$off),
                 [], !strconcat(Name, "\t$dst, ${off}(${addr})${p2align}"),
                 !strconcat(Name, "\t${off}${p2align}"), Opcode, false>,
               Requires<reqs # [HasMemSafety]>;
  defm "_A64_SAFE": I<(outs rc:$dst),
                 (ins P2Align:$p2align, offset64_op:$off, HANDLE:$addr),
                 (outs), (ins P2Align:$p2align, offset32_op:$off),
                 [], !strconcat(Name, "\t$dst, ${off}(${addr})${p2align}"),
                 !strconcat(Name, "\t${off}${p2align}"), Opcode, false>,
               Requires<reqs # [HasMemSafety]>;
  }
}

// Basic load.
// FIXME: When we can break syntax compatibility, reorder the fields in the
// asmstrings to match the binary encoding.
defm LOAD_I32 : WebAssemblyLoad<I32, "i32.load", 0x28, []>;
defm LOAD_I64 : WebAssemblyLoad<I64, "i64.load", 0x29, []>;
defm LOAD_F32 : WebAssemblyLoad<F32, "f32.load", 0x2a, []>;
defm LOAD_F64 : WebAssemblyLoad<F64, "f64.load", 0x2b, []>;

defm LOAD_HANDLE : WebAssemblyLoad<HANDLE, "handle.load", 0xfa04, [HasMemSafety]>;

// Extending load.
defm LOAD8_S_I32 : WebAssemblyLoad<I32, "i32.load8_s", 0x2c, []>;
defm LOAD8_U_I32 : WebAssemblyLoad<I32, "i32.load8_u", 0x2d, []>;
defm LOAD16_S_I32 : WebAssemblyLoad<I32, "i32.load16_s", 0x2e, []>;
defm LOAD16_U_I32 : WebAssemblyLoad<I32, "i32.load16_u", 0x2f, []>;
defm LOAD8_S_I64 : WebAssemblyLoad<I64, "i64.load8_s", 0x30, []>;
defm LOAD8_U_I64 : WebAssemblyLoad<I64, "i64.load8_u", 0x31, []>;
defm LOAD16_S_I64 : WebAssemblyLoad<I64, "i64.load16_s", 0x32, []>;
defm LOAD16_U_I64 : WebAssemblyLoad<I64, "i64.load16_u", 0x33, []>;
defm LOAD32_S_I64 : WebAssemblyLoad<I64, "i64.load32_s", 0x34, []>;
defm LOAD32_U_I64 : WebAssemblyLoad<I64, "i64.load32_u", 0x35, []>;

// Pattern matching

multiclass LoadPat<ValueType ty, SDPatternOperator kind, string Name> {
      def : Pat<(ty (kind (AddrOps32 offset32_op:$offset, I32:$addr))),
           (!cast<NI>(Name # "_A32") 0,
                                     offset32_op:$offset,
                                     I32:$addr)>,
                                     Requires<[HasAddr32]>;

      def : Pat<(ty (kind (AddrOps64 offset64_op:$offset, I64:$addr))),
           (!cast<NI>(Name # "_A64") 0,
                                     offset64_op:$offset,
                                     I64:$addr)>,
                                     Requires<[HasAddr64]>;
}

// TODO(martin): for now we declare this new multiclass, as we don't want to implement
// the safe loads for e.g. simd instructions yet. This should be done once we are done
// with our proof of concept and can continue with the implementation.
multiclass LoadPatSafe<ValueType ty, SDPatternOperator kind, string Name> {
      def : Pat<(ty (kind (AddrOps32 offset32_op:$offset, I32:$addr))),
           (!cast<NI>(Name # "_A32") 0,
                                     offset32_op:$offset,
                                     I32:$addr)>,
                                     Requires<[HasAddr32, HasNoMemSafety]>;

      def : Pat<(ty (kind (AddrOps64 offset64_op:$offset, I64:$addr))),
           (!cast<NI>(Name # "_A64") 0,
                                     offset64_op:$offset,
                                     I64:$addr)>,
                                     Requires<[HasAddr64, HasNoMemSafety]>;

      def : Pat<(ty (kind (AddrOps32 offset32_op:$offset, HANDLE:$addr))),
           (!cast<NI>(Name # "_A32_SAFE") 0,
                                     offset32_op:$offset,
                                     HANDLE:$addr)>,
                                     Requires<[HasAddr32, HasMemSafety]>;

      def : Pat<(ty (kind (AddrOps64 offset64_op:$offset, HANDLE:$addr))),
           (!cast<NI>(Name # "_A64_SAFE") 0,
                                     offset64_op:$offset,
                                     HANDLE:$addr)>,
                                     Requires<[HasAddr64, HasMemSafety]>;
}

defm : LoadPatSafe<i32, load, "LOAD_I32">;
defm : LoadPatSafe<i64, load, "LOAD_I64">;
defm : LoadPatSafe<f32, load, "LOAD_F32">;
defm : LoadPatSafe<f64, load, "LOAD_F64">;

defm : LoadPatSafe<i32, sextloadi8, "LOAD8_S_I32">;
defm : LoadPatSafe<i32, sextloadi16, "LOAD16_S_I32">;
defm : LoadPatSafe<i64, sextloadi8, "LOAD8_S_I64">;
defm : LoadPatSafe<i64, sextloadi16, "LOAD16_S_I64">;
defm : LoadPatSafe<i64, sextloadi32, "LOAD32_S_I64">;

defm : LoadPatSafe<i32, zextloadi8, "LOAD8_U_I32">;
defm : LoadPatSafe<i32, zextloadi16, "LOAD16_U_I32">;
defm : LoadPatSafe<i64, zextloadi8, "LOAD8_U_I64">;
defm : LoadPatSafe<i64, zextloadi16, "LOAD16_U_I64">;
defm : LoadPatSafe<i64, zextloadi32, "LOAD32_U_I64">;

defm : LoadPatSafe<i32, extloadi8, "LOAD8_U_I32">;
defm : LoadPatSafe<i32, extloadi16, "LOAD16_U_I32">;
defm : LoadPatSafe<i64, extloadi8, "LOAD8_U_I64">;
defm : LoadPatSafe<i64, extloadi16, "LOAD16_U_I64">;
defm : LoadPatSafe<i64, extloadi32, "LOAD32_U_I64">;

// Defines atomic and non-atomic stores, regular and truncating
multiclass WebAssemblyStore<WebAssemblyRegClass rc, string Name, int Opcode,
                            list<Predicate> reqs = []> {
  let mayStore = 1, UseNamedOperandTable = 1 in {
  defm "_A32" : I<(outs),
                  (ins P2Align:$p2align, offset32_op:$off, I32:$addr, rc:$val),
                  (outs),
                  (ins P2Align:$p2align, offset32_op:$off), [],
                  !strconcat(Name, "\t${off}(${addr})${p2align}, $val"),
                  !strconcat(Name, "\t${off}${p2align}"), Opcode, false>,
                Requires<reqs # [HasNoMemSafety]>;
  defm "_A64" : I<(outs),
                  (ins P2Align:$p2align, offset64_op:$off, I64:$addr, rc:$val),
                  (outs),
                  (ins P2Align:$p2align, offset64_op:$off), [],
                  !strconcat(Name, "\t${off}(${addr})${p2align}, $val"),
                  !strconcat(Name, "\t${off}${p2align}"), Opcode, true>,
                Requires<reqs # [HasNoMemSafety]>;
  defm "_A32_SAFE" : I<(outs),
                  (ins P2Align:$p2align, offset32_op:$off, HANDLE:$addr, rc:$val),
                  (outs),
                  (ins P2Align:$p2align, offset32_op:$off), [],
                  !strconcat(Name, "\t${off}(${addr})${p2align}, $val"),
                  !strconcat(Name, "\t${off}${p2align}"), Opcode, false>,
                Requires<reqs # [HasMemSafety]>;
  defm "_A64_SAFE" : I<(outs),
                  (ins P2Align:$p2align, offset64_op:$off, HANDLE:$addr, rc:$val),
                  (outs),
                  (ins P2Align:$p2align, offset64_op:$off), [],
                  !strconcat(Name, "\t${off}(${addr})${p2align}, $val"),
                  !strconcat(Name, "\t${off}${p2align}"), Opcode, true>,
                Requires<reqs # [HasMemSafety]>;
  }
}

// Basic store.
// Note: WebAssembly inverts SelectionDAG's usual operand order.
defm STORE_I32  : WebAssemblyStore<I32, "i32.store", 0x36>;
defm STORE_I64  : WebAssemblyStore<I64, "i64.store", 0x37>;
defm STORE_F32  : WebAssemblyStore<F32, "f32.store", 0x38>;
defm STORE_F64  : WebAssemblyStore<F64, "f64.store", 0x39>;
defm STORE_HANDLE : WebAssemblyStore<HANDLE, "handle.store", 0xfa05, [HasMemSafety]>;

multiclass StorePat<ValueType ty, SDPatternOperator kind, string Name> {
  def : Pat<(kind ty:$val, (AddrOps32 offset32_op:$offset, I32:$addr)),
            (!cast<NI>(Name # "_A32") 0,
                                      offset32_op:$offset,
                                      I32:$addr,
                                      ty:$val)>,
            Requires<[HasAddr32]>;
  def : Pat<(kind ty:$val, (AddrOps64 offset64_op:$offset, I64:$addr)),
            (!cast<NI>(Name # "_A64") 0,
                                      offset64_op:$offset,
                                      I64:$addr,
                                      ty:$val)>,
            Requires<[HasAddr64]>;
}

multiclass StorePatSafe<ValueType ty, SDPatternOperator kind, string Name> {
  def : Pat<(kind ty:$val, (AddrOps32 offset32_op:$offset, I32:$addr)),
            (!cast<NI>(Name # "_A32") 0,
                                      offset32_op:$offset,
                                      I32:$addr,
                                      ty:$val)>,
            Requires<[HasAddr32, HasNoMemSafety]>;
  def : Pat<(kind ty:$val, (AddrOps64 offset64_op:$offset, I64:$addr)),
            (!cast<NI>(Name # "_A64") 0,
                                      offset64_op:$offset,
                                      I64:$addr,
                                      ty:$val)>,
            Requires<[HasAddr64, HasNoMemSafety]>;
  def : Pat<(kind ty:$val, (AddrOps32 offset32_op:$offset, HANDLE:$addr)),
            (!cast<NI>(Name # "_A32_SAFE") 0,
                                      offset32_op:$offset,
                                      HANDLE:$addr,
                                      ty:$val)>,
            Requires<[HasAddr32, HasMemSafety]>;
  def : Pat<(kind ty:$val, (AddrOps64 offset64_op:$offset, HANDLE:$addr)),
            (!cast<NI>(Name # "_A64_SAFE") 0,
                                      offset64_op:$offset,
                                      HANDLE:$addr,
                                      ty:$val)>,
            Requires<[HasAddr64, HasMemSafety]>;
}

defm : StorePatSafe<i32, store, "STORE_I32">;
defm : StorePatSafe<i64, store, "STORE_I64">;
defm : StorePatSafe<f32, store, "STORE_F32">;
defm : StorePatSafe<f64, store, "STORE_F64">;

// Truncating store.
defm STORE8_I32 : WebAssemblyStore<I32, "i32.store8", 0x3a>;
defm STORE16_I32 : WebAssemblyStore<I32, "i32.store16", 0x3b>;
defm STORE8_I64 : WebAssemblyStore<I64, "i64.store8", 0x3c>;
defm STORE16_I64 : WebAssemblyStore<I64, "i64.store16", 0x3d>;
defm STORE32_I64 : WebAssemblyStore<I64, "i64.store32", 0x3e>;

defm : StorePatSafe<i32, truncstorei8, "STORE8_I32">;
defm : StorePatSafe<i32, truncstorei16, "STORE16_I32">;
defm : StorePatSafe<i64, truncstorei8, "STORE8_I64">;
defm : StorePatSafe<i64, truncstorei16, "STORE16_I64">;
defm : StorePatSafe<i64, truncstorei32, "STORE32_I64">;

multiclass MemoryOps<WebAssemblyRegClass rc, string B> {
// Current memory size.
defm MEMORY_SIZE_A#B : I<(outs rc:$dst), (ins i32imm:$flags),
                         (outs), (ins i32imm:$flags),
                         [(set rc:$dst,
                           (int_wasm_memory_size (i32 imm:$flags)))],
                         "memory.size\t$dst, $flags", "memory.size\t$flags",
                         0x3f>;

// Grow memory.
defm MEMORY_GROW_A#B : I<(outs rc:$dst), (ins i32imm:$flags, rc:$delta),
                         (outs), (ins i32imm:$flags),
                         [(set rc:$dst,
                           (int_wasm_memory_grow (i32 imm:$flags),
                             rc:$delta))],
                         "memory.grow\t$dst, $flags, $delta",
                         "memory.grow\t$flags", 0x40>;

defm SEGMENT_NEW_A#B : I<(outs HANDLE:$dst), (ins rc:$size),
                         (outs), (ins rc:$size),
                         [(set HANDLE:$dst,
                            (int_wasm_segment_new rc:$size))],
                          "segment.new\t$dst, $size", "segment.new\t$size",
                          0xfa00>,
                         Requires<[HasMemSafety]>;

defm SEGMENT_FREE_A#B : I<(outs), (ins HANDLE:$handle),
                         (outs), (ins HANDLE:$handle),
                         [(int_wasm_segment_free HANDLE:$handle)],
                          "segment.free\t$handle", "segment.free\t$handle",
                          0xfa01>,
                         Requires<[HasMemSafety]>;

defm SEGMENT_STACK_NEW_A#B : I<(outs HANDLE:$dst), (ins HANDLE:$sp, rc:$size),
                         (outs), (ins HANDLE:$sp, rc:$size),
                         [(set HANDLE:$dst,
                            (int_wasm_segment_stack_new HANDLE:$sp, rc:$size))],
                          "segment.stack.new\t$dst, $sp, $size", "segment.new\t$sp, $size",
                          0xfa02>,
                         Requires<[HasMemSafety]>;

defm SEGMENT_STACK_FREE_A#B : I<(outs), (ins HANDLE:$handle, HANDLE:$sp, rc:$size),
                         (outs), (ins HANDLE:$handle, HANDLE:$sp, rc:$size),
                         [(int_wasm_segment_stack_free HANDLE:$handle, HANDLE:$sp, rc:$size)],
                          "segment.stack.free\t$handle, $sp, $size", "segment.stack.free\t$handle, $sp, $size",
                          0xfa03>,
                         Requires<[HasMemSafety]>;
}

defm : MemoryOps<I32, "32">;
defm : MemoryOps<I64, "64">;

defm SELECT_HANDLE : I<(outs HANDLE:$dst), (ins HANDLE:$lhs, HANDLE:$rhs, I32:$cond),
                    (outs), (ins),
                    [(set HANDLE:$dst, (select I32:$cond, HANDLE:$lhs, HANDLE:$rhs))],
                    "handle.select\t$dst, $lhs, $rhs, $cond", "handle.select", 0x1b>;

// ISD::SELECT requires its operand to conform to getBooleanContents, but
// WebAssembly's select interprets any non-zero value as true, so we can fold
// a setne with 0 into a select.
def : Pat<(select (i32 (setne I32:$cond, 0)), HANDLE:$lhs, HANDLE:$rhs),
          (SELECT_HANDLE HANDLE:$lhs, HANDLE:$rhs, I32:$cond)>;

// And again, this time with seteq instead of setne and the arms reversed.
def : Pat<(select (i32 (seteq I32:$cond, 0)), HANDLE:$lhs, HANDLE:$rhs),
          (SELECT_HANDLE HANDLE:$rhs, HANDLE:$lhs, I32:$cond)>;
