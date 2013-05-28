; RUN: opt < %s -S | FileCheck %s

declare void @l0()
declare void @l1()
declare void @l2()

; CHECK: @func
define void @func(i8 %f) {

sw0:
; CHECK:   switchr i8 %f [
; CHECK:      i8 4, label %L1
; CHECK:     [i8 5 ... i8 20), label %L0
; CHECK:     [i8 20 ... i8 40), label %L1
; CHECK:     [i8 40 ... i8 1), label %L2
; CHECK:   ]
  switchr i8 %f [
      i8 4, label %L1
      i8 5, label %L0
     [i8 6  ... i8 20), label %L0
     [i8 20 ... i8 40), label %L1
     [i8 40 ... i8 1), label %L2
  ]

L0:
  call void @l0()
  br label %end

L1:
  call void @l1()
  br label %end

L2:
  call void @l2()
  br label %end

end:
  ret void
}
