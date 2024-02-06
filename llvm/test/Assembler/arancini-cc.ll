; RUN: llvm-as < %s | llvm-dis | llvm-as | llvm-dis | FileCheck %s

; CHECK: arancini void @arancini_cc
define arancini void @arancini_cc() {
entry:
  ret void
}
