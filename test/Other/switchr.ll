; RUN: opt < %s -S | FileCheck %s

declare void @l0()
declare void @l1()
declare void @l2()

; CHECK: @func
define void @func(i8 %f) {

; CHECK: sw0:
sw0:
; CHECK:   switchr i8 %f [
; CHECK:     [i8 4 ... i8 20), label %L0
; CHECK:     [i8 20 ... i8 30), label %L1
; CHECK:     [i8 30 ... i8 40), label %L2
; CHECK:   ]
  switchr i8 %f [
     [i8 4  ... i8 20), label %L0
     [i8 20 ... i8 30), label %L1
     [i8 30 ... i8 40), label %L2
  ]

; CHECK: sw1:
sw1:
; CHECK:   switchr i8 %f [
; CHECK:     [i8 4 ... i8 20), label %L0
; CHECK:     [i8 20 ... i8 4), label %L1
; CHECK:   ]
  switchr i8 %f [
     [i8 4  ... i8 20), label %L0
     [i8 20 ... i8 30), label %L1
     [i8 30 ... i8 4), label %L1
  ]

; CHECK: sw2:
sw2:
; CHECK:   switchr i8 %f [
; CHECK:     [i8 4 ... i8 20), label %L0
; CHECK:     [i8 20 ... i8 4), label %L1
; CHECK:   ]
  switchr i8 %f [
     [i8 4  ... i8 20), label %L0
     [i8 20 ... i8 4), label %L1
  ];

; CHECK: sw3:
sw3:
; CHECK:   switchr i8 %f [
; CHECK:     [i8 4 ... i8 10), label %L0
; CHECK:     [i8 10 ... i8 20), label %L1
; CHECK:     [i8 20 ... i8 40), label %L2
; CHECK:     [i8 40 ... i8 3), label %L0
; CHECK:   ]
  switchr i8 %f [
     [i8 4  ... i8 3), label %L0
     [i8 10  ... i8 20), label %L1
     [i8 20 ... i8 40), label %L2
  ]

; CHECK: sw4:
sw4:
; CHECK:   switchr i8 %f [
; CHECK:     [i8 0 ... i8 0), label %L0
; CHECK:   ]
  switchr i8 %f [
     [i8 0  ... i8 0), label %L0
  ]

; CHECK: sw5:
sw5:
; CHECK:   switchr i8 %f [
; CHECK:     [i8 0 ... i8 0), label %L0
; CHECK:   ]
  switchr i8 %f [
     [i8 0  ... i8 0), label %L0
     [i8 5  ... i8 10), label %L0
  ]

; CHECK: sw6:
sw6:
; CHECK:   switchr i8 %f [
; CHECK:     [i8 0 ... i8 5), label %L0
; CHECK:     [i8 5 ... i8 10), label %L1
; CHECK:     [i8 10 ... i8 0), label %L0
; CHECK:   ]
  switchr i8 %f [
     [i8 0  ... i8 0), label %L0
     [i8 5  ... i8 10), label %L1
  ]

; CHECK: sw7:
sw7:
; CHECK:   switchr i8 %f [
; CHECK:     [i8 0 ... i8 0), label %L0
; CHECK:   ]
  switchr i8 %f [
     [i8 3  ... i8 4), label %L0
     [i8 4  ... i8 3), label %L0
  ]

; CHECK: sw8:
sw8:
; CHECK:   switchr i8 %f [
; CHECK:     [i8 4 ... i8 20), label %L0
; CHECK:     [i8 20 ... i8 40), label %L1
; CHECK:     [i8 40 ... i8 4), label %L2
; CHECK:   ]
  switchr i8 %f [
     [i8 4  ... i8 20), label %L0
     [i8 20 ... i8 30), label %L1
     [i8 30 ... i8 40), label %L1
     [i8 40 ... i8 4), label %L2
  ]

; CHECK: sw9:
sw9:
; CHECK:   switchr i8 %f [
; CHECK:     [i8 4 ... i8 20), label %L0
; CHECK:     [i8 20 ... i8 40), label %L1
; CHECK:     [i8 40 ... i8 1), label %L2
; CHECK:   ]
  switchr i8 %f [
     [i8 4  ... i8 20), label %L0
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
