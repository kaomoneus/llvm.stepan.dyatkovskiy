; RUN: not opt -S %s 2>&1 | FileCheck %s

define void @func(i8 %f) {

sw0:
  switchr i8 %f [
     [i8 20  ... i8 4), label %end
; CHECK: is overlapped with wrapper case
     [i8 15 ... i8 30), label %end
  ]

end:
  ret void
}
