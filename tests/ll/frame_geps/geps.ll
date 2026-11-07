; GEPs with constant indices of allocas (a frame-address scheme for them was
; tried in C1 and removed): chains, negative and byte offsets, uses
; in other blocks and in PHIs, an escaping address, pointer compares, an
; over-aligned base, and an alloca outside the entry
; block. main.c calls them and prints the results.
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

%struct.S = type { i32, [3 x float], { double, i64 } }

declare void @fill(ptr, i32)
declare i64 @sum_ints(ptr, i32)

; a chain p->c.b, stores through it, reads back through other GEPs
define i64 @g_chain(i64 %x) {
  %s = alloca %struct.S, align 8
  %c = getelementptr inbounds %struct.S, ptr %s, i32 0, i32 2
  %cb = getelementptr inbounds { double, i64 }, ptr %c, i32 0, i32 1
  store i64 %x, ptr %cb, align 8
  %ca = getelementptr inbounds { double, i64 }, ptr %c, i32 0, i32 0
  store double 2.5, ptr %ca, align 8
  %f2 = getelementptr inbounds %struct.S, ptr %s, i32 0, i32 1, i64 2
  store float 4.0, ptr %f2, align 4
  %a = getelementptr inbounds %struct.S, ptr %s, i32 0, i32 0
  store i32 7, ptr %a, align 4
  %raw = getelementptr inbounds i8, ptr %s, i64 24
  %v = load i64, ptr %raw, align 8
  %d = load double, ptr %ca, align 8
  %f = load float, ptr %f2, align 4
  %i = load i32, ptr %s, align 4
  %di = fptosi double %d to i64
  %fi = fptosi float %f to i64
  %ii = sext i32 %i to i64
  %r1 = add i64 %v, %di
  %r2 = mul i64 %fi, 100
  %r3 = add i64 %r1, %r2
  %r4 = mul i64 %ii, 10000
  %r5 = add i64 %r3, %r4
  ret i64 %r5
}

; negative offsets from a GEP into the middle of an array; the address escapes
define i64 @g_negative() {
  %arr = alloca [16 x i32], align 16
  call void @fill(ptr %arr, i32 16)
  %mid = getelementptr inbounds [16 x i32], ptr %arr, i64 0, i64 8
  %m1 = getelementptr inbounds i32, ptr %mid, i64 -3
  %m2 = getelementptr inbounds i32, ptr %mid, i64 5
  %v1 = load i32, ptr %m1, align 4
  %v2 = load i32, ptr %m2, align 4
  store i32 1000, ptr %m1, align 4
  %s = call i64 @sum_ints(ptr %arr, i32 16)
  %s2 = call i64 @sum_ints(ptr %mid, i32 8)
  %w1 = sext i32 %v1 to i64
  %w2 = sext i32 %v2 to i64
  %t1 = mul i64 %w1, 1000000
  %t2 = mul i64 %w2, 10000
  %t3 = add i64 %t1, %t2
  %t4 = add i64 %t3, %s
  %t5 = mul i64 %s2, 7
  %t6 = add i64 %t4, %t5
  ret i64 %t6
}

; uses in other blocks and in PHIs; pointer compares
define i64 @g_blocks(i32 %c) {
  %arr = alloca [4 x i64], align 8
  %e0 = getelementptr inbounds [4 x i64], ptr %arr, i64 0, i64 0
  %e1 = getelementptr inbounds [4 x i64], ptr %arr, i64 0, i64 1
  %e3 = getelementptr inbounds [4 x i64], ptr %arr, i64 0, i64 3
  store i64 10, ptr %e0, align 8
  store i64 20, ptr %e1, align 8
  %e2 = getelementptr inbounds [4 x i64], ptr %arr, i64 0, i64 2
  store i64 30, ptr %e2, align 8
  store i64 40, ptr %e3, align 8
  %t = icmp sgt i32 %c, 0
  br i1 %t, label %a, label %b
a:
  %pa = getelementptr inbounds i64, ptr %e1, i64 1
  br label %join
b:
  br label %join
join:
  %p = phi ptr [ %pa, %a ], [ %e3, %b ]
  %v = load i64, ptr %p, align 8
  %same = icmp eq ptr %p, %e2
  %z = zext i1 %same to i64
  %w = load i64, ptr %e1, align 8
  %r1 = mul i64 %z, 1000
  %r2 = add i64 %v, %r1
  %r3 = add i64 %r2, %w
  ret i64 %r3
}

; an over-aligned base (64): its GEPs stay computed
define i64 @g_overaligned(i64 %x) {
  %big = alloca [8 x i64], align 64
  %e5 = getelementptr inbounds [8 x i64], ptr %big, i64 0, i64 5
  store i64 %x, ptr %e5, align 8
  %e6 = getelementptr inbounds [8 x i64], ptr %big, i64 0, i64 6
  store i64 3, ptr %e6, align 8
  %a = ptrtoint ptr %big to i64
  %al = and i64 %a, 63
  %v5 = load i64, ptr %e5, align 8
  %v6 = load i64, ptr %e6, align 8
  %r1 = mul i64 %v5, %v6
  %r2 = add i64 %r1, %al
  ret i64 %r2
}

; an alloca outside the entry block (a dynamic one) and a GEP of it
define i64 @g_dynamic(i32 %n) {
entry:
  br label %body
body:
  %d = alloca [4 x i32], align 4
  %d2 = getelementptr inbounds [4 x i32], ptr %d, i64 0, i64 2
  store i32 %n, ptr %d2, align 4
  %d0 = getelementptr inbounds [4 x i32], ptr %d, i64 0, i64 0
  store i32 5, ptr %d0, align 4
  %v2 = load i32, ptr %d2, align 4
  %v0 = load i32, ptr %d0, align 4
  %s = add i32 %v2, %v0
  %r = sext i32 %s to i64
  ret i64 %r
}
