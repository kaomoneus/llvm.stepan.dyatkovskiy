; RUN: opt < %s -o %t.bc
; RUN: opt < %t.bc -S | FileCheck %s

declare void @l0()
declare void @l1()
declare void @l2()

; CHECK: @func
define void @func(i8 %f, i128 %g) {

; CHECK: sw0:
; CHECK:   switchr i8 %f [
; CHECK:      i8 4, label %L0
; CHECK:     [i8 6  ... i8 20), label %L1
; CHECK:     [i8 20 ... i8 1), label %L2
; CHECK:   ]
sw0:
  switchr i8 %f [
    ;[i8 1 ... i8 4) ==> `black hole`
      i8 4, label %L0
    ;[i8 5 ... i8 6) ==> `black hole`
     [i8 6  ... i8 20), label %L1
     [i8 20 ... i8 1), label %L2
  ]

; CHECK: sw1:
; CHECK:   switchr i8 %f [
; CHECK:      [i8 0 ... i8 0), label %L0
; CHECK:   ]
sw1:
  switchr i8 %f [
    [i8 0 ... i8 0), label %L0 ; whole set == unconditional br
  ]

; CHECK: sw2:
; CHECK:   switchr i8 %f [
; CHECK:      i8 4, label %L0
; CHECK:     [i8 5  ... i8 20), label %L1
; CHECK:     [i8 20 ... i8 4), label %L2
; CHECK:   ]
sw2:
  switchr i8 %f [
      i8 4, label %L0
     [i8 5  ... i8 20), label %L1
     [i8 20 ... i8 4), label %L2
  ]

; CHECK: sw3:
; CHECK:   switchr i128 %g [
; CHECK:      i128 4, label %L0
; CHECK:     [i128 5  ... i128 20213123123123123123123), label %L1
; CHECK:     [i128 20213123123123123123123 ... i128 4), label %L2
; CHECK:   ]
sw3:
 switchr i128 %g [
      i128 4, label %L0
     [i128 5  ... i128 20213123123123123123123), label %L1
     [i128 20213123123123123123123 ... i128 4), label %L2
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
