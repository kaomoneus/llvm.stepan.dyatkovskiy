; RUN: llc < %s -disable-fp-elim -mtriple x86_64-apple-darwin11 | FileCheck -check-prefix=ASM %s
; RUN: llc < %s -disable-fp-elim -mtriple x86_64-apple-darwin11 -filetype=obj -o - \
; RUN:  | llvm-objdump -triple x86_64-apple-darwin11 -s - \
; RUN:  | FileCheck -check-prefix=CU %s
; RUN: llc < %s -disable-fp-elim -mtriple x86_64-apple-darwin11 \
; RUN:  | llvm-mc -triple x86_64-apple-darwin11 -filetype=obj -o - \
; RUN:  | llvm-objdump -triple x86_64-apple-darwin11 -s - \
; RUN:  | FileCheck -check-prefix=FROM-ASM %s

%ty = type { i8* }

@gv = external global i32

; This is aligning the stack with a push of a random register.
; ASM: pushq %rax

; Even though we can't encode %rax into the compact unwind, We still want to be
; able to generate a compact unwind encoding in this particular case.

; CU:      Contents of section __compact_unwind:
; CU-NEXT: 0020 00000000 00000000 1e000000 01000101
; CU-NEXT: 0030 00000000 00000000 00000000 00000000

; FROM-ASM:      Contents of section __compact_unwind:
; FROM-ASM-NEXT: 0020 00000000 00000000 1e000000 01000101
; FROM-ASM-NEXT: 0030 00000000 00000000 00000000 00000000

define i8* @foo(i64 %size) {
  %addr = alloca i64, align 8
  %tmp20 = load i32* @gv, align 4
  %tmp21 = call i32 @bar()
  %tmp25 = load i64* %addr, align 8
  %tmp26 = inttoptr i64 %tmp25 to %ty*
  %tmp29 = getelementptr inbounds %ty* %tmp26, i64 0, i32 0
  %tmp34 = load i8** %tmp29, align 8
  %tmp35 = getelementptr inbounds i8* %tmp34, i64 %size
  store i8* %tmp35, i8** %tmp29, align 8
  ret i8* null
}

declare i32 @bar()
