; RUN: not opt -S %s 2>&1 | FileCheck %s

define void @func(i8 %f) {

sw0:
  switchr i8 %f [
     [i8 4  ... i8 20), label %end
; CHECK: case is overlapped
     [i8 15 ... i8 30), label %end
     [i8 30 ... i8 40), label %end
  ]

end:
  ret void
}
