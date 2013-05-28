; RUN: llc < %s -o %t.s
; RUN: gcc %t.s -o %t.out
; RUN: %t.out | FileCheck %s

; CHECK: 0 belongs to [7,1)
; CHECK: 1 belongs to [1,4)
; CHECK: 2 belongs to [1,4)
; CHECK: 3 belongs to [1,4)
; CHECK: 4 belongs to [4,7)
; CHECK: 5 belongs to [4,7)
; CHECK: 6 belongs to [4,7)
; CHECK: 7 belongs to [7,1)
; CHECK: 8 belongs to [7,1)
; CHECK: 9 belongs to [7,1)

; ModuleID = 'switchr-test.c'

@.str = private unnamed_addr constant [21 x i8] c"%i belongs to [1,4)\0A\00", align 1
@.str1 = private unnamed_addr constant [21 x i8] c"%i belongs to [4,7)\0A\00", align 1
@.str2 = private unnamed_addr constant [21 x i8] c"%i belongs to [7,1)\0A\00", align 1

define i32 @main() nounwind {
entry:
  %retval = alloca i32, align 4
  %i = alloca i32, align 4
  store i32 0, i32* %retval
  store i32 0, i32* %i, align 4
  br label %for.cond

for.cond:                                         ; preds = %for.inc, %entry
  %0 = load i32* %i, align 4
  %cmp = icmp slt i32 %0, 10
  br i1 %cmp, label %for.body, label %for.end

for.body:                                         ; preds = %for.cond
  %1 = load i32* %i, align 4
  switchr i32 %1 [
    [i32 1 ... i32 4), label %sw.bb
    [i32 4 ... i32 7), label %sw.bb1
    [i32 7 ... i32 1), label %sw.default
  ]

sw.bb:                                            ; preds = %for.body, %for.body, %for.body
  %2 = load i32* %i, align 4
  %call0 = call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([21 x i8]* @.str, i32 0, i32 0), i32 %2)
  br label %sw.epilog

sw.bb1:                                           ; preds = %for.body, %for.body, %for.body
  %3 = load i32* %i, align 4
  %call2 = call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([21 x i8]* @.str1, i32 0, i32 0), i32 %3)
  br label %sw.epilog

sw.default:                                       ; preds = %for.body
  %4 = load i32* %i, align 4
  %call3 = call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([21 x i8]* @.str2, i32 0, i32 0), i32 %4)
  br label %sw.epilog

sw.epilog:                                        ; preds = %sw.default, %sw.bb1, %sw.bb
  br label %for.inc

for.inc:                                          ; preds = %sw.epilog
  %5 = load i32* %i, align 4
  %inc = add nsw i32 %5, 1
  store i32 %inc, i32* %i, align 4
  br label %for.cond

for.end:                                          ; preds = %for.cond
  ret i32 0
}

declare i32 @printf(i8*, ...)
