; Register pressure of carried addresses (milestone E2): LLVM -O2 merges
; index expressions into GEPs of four variable terms whose scales are not
; 1/2/4/8 (lencod's macroblock.c, IntraChromaPrediction4x4); the GEP is
; folded into a load, the load deferred into the store after it, and the
; store's own address is another GEP of two terms. Every scratch register
; of the chain stayed locked into the store and the block-local allocator
; ran out of registers (an assertion). main.c checks the copies.
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@img = dso_local global ptr null, align 8

define dso_local void @pred4x4(i32 %uv, i32 %bx, i32 %by) {
entry:
  %0 = load ptr, ptr @img, align 8
  %1 = getelementptr inbounds i8, ptr %0, i64 14224
  %2 = load ptr, ptr %1, align 8
  %3 = getelementptr inbounds i8, ptr %0, i64 12
  %4 = load i32, ptr %3, align 4
  %5 = sext i32 %4 to i64
  %6 = getelementptr inbounds [16 x i8], ptr %2, i64 %5, i64 2
  %7 = load i32, ptr %6, align 4
  %8 = sext i32 %by to i64
  %9 = sext i32 %uv to i64
  %10 = sext i32 %7 to i64
  %11 = sext i32 %bx to i64
  %12 = getelementptr inbounds i8, ptr %0, i64 1024
  %13 = getelementptr inbounds [16 x [16 x i16]], ptr %12, i64 0, i64 %11, i64 %8
  %14 = getelementptr inbounds i8, ptr %0, i64 2048
  %15 = getelementptr inbounds [4 x [4 x [16 x [16 x i16]]]], ptr %14, i64 0, i64 %9, i64 %10, i64 %11, i64 %8
  %16 = load i64, ptr %15, align 8
  store i64 %16, ptr %13, align 8
  %17 = add nsw i64 %11, 1
  %18 = getelementptr inbounds [16 x [16 x i16]], ptr %12, i64 0, i64 %17, i64 %8
  %19 = getelementptr inbounds [4 x [4 x [16 x [16 x i16]]]], ptr %14, i64 0, i64 %9, i64 %10, i64 %17, i64 %8
  %20 = load i64, ptr %19, align 8
  store i64 %20, ptr %18, align 8
  ret void
}
