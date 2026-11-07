; Small aggregates returned in registers and read back by extractvalue, in
; the shapes the back-end's call-result fusion (abi.goose ret_parts_fuse),
; its extractvalue lowering and its deferred aggregate loads must handle or
; reject; main.c defines the callees and prints what these return.
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

declare { <2 x float>, <2 x float> } @mk4(float, float, float, float)
declare { <2 x float>, float } @mk3(float, float, float)
declare { double, double } @mkc(double, double)
declare { i64, double } @mkld(i64, double)
declare { double, i32 } @mkdi(double, i32)
declare { i8, double } @mkcd(i32, double)
declare { ptr, i32 } @mkpi(ptr, i32)
declare { i64, i64 } @mkll(i64, i64)
declare { float, double } @mkfd(float, double)
declare void @clobber()

define internal float @wsum4(ptr %p) {
  %a = load float, ptr %p, align 4
  %q1 = getelementptr inbounds float, ptr %p, i64 1
  %b = load float, ptr %q1, align 4
  %q2 = getelementptr inbounds float, ptr %p, i64 2
  %c = load float, ptr %q2, align 4
  %q3 = getelementptr inbounds float, ptr %p, i64 3
  %d = load float, ptr %q3, align 4
  %b2 = fmul float %b, 2.0
  %c3 = fmul float %c, 3.0
  %d4 = fmul float %d, 4.0
  %s1 = fadd float %a, %b2
  %s2 = fadd float %s1, %c3
  %s3 = fadd float %s2, %d4
  ret float %s3
}

; clang's shape (extractvalue + store into a temporary), the fields in reverse order
define float @t_swap(float %a, float %b, float %c, float %d) {
  %p = alloca [4 x float], align 4
  %r = call { <2 x float>, <2 x float> } @mk4(float %a, float %b, float %c, float %d)
  %p1 = getelementptr inbounds i8, ptr %p, i64 8
  %y = extractvalue { <2 x float>, <2 x float> } %r, 1
  store <2 x float> %y, ptr %p1, align 4
  %x = extractvalue { <2 x float>, <2 x float> } %r, 0
  store <2 x float> %x, ptr %p, align 4
  %s = call float @wsum4(ptr %p)
  ret float %s
}

; a call between the call and its extractvalues: the fields live across it
define float @t_call_between(float %a, float %b, float %c, float %d) {
  %r = call { <2 x float>, <2 x float> } @mk4(float %a, float %b, float %c, float %d)
  call void @clobber()
  %x = extractvalue { <2 x float>, <2 x float> } %r, 0
  %y = extractvalue { <2 x float>, <2 x float> } %r, 1
  call void @clobber()
  %x0 = extractelement <2 x float> %x, i32 0
  %x1 = extractelement <2 x float> %x, i32 1
  %y0 = extractelement <2 x float> %y, i32 0
  %y1 = extractelement <2 x float> %y, i32 1
  %x1b = fmul float %x1, 2.0
  %y0b = fmul float %y0, 3.0
  %y1b = fmul float %y1, 4.0
  %s1 = fadd float %x0, %x1b
  %s2 = fadd float %s1, %y0b
  %s3 = fadd float %s2, %y1b
  ret float %s3
}

; the same field twice (not fused)
define double @t_dup(double %a, double %b) {
  %r = call { double, double } @mkc(double %a, double %b)
  %x1 = extractvalue { double, double } %r, 0
  %x2 = extractvalue { double, double } %r, 0
  %y = extractvalue { double, double } %r, 1
  %t1 = fmul double %x1, 3.0
  %t2 = fmul double %x2, 5.0
  %t3 = fmul double %y, 7.0
  %s1 = fadd double %t1, %t2
  %s2 = fadd double %s1, %t3
  ret double %s2
}

; extractvalues in other blocks (not fused)
define double @t_other_block(double %a, double %b, i32 %c) {
  %r = call { double, double } @mkc(double %a, double %b)
  %t = icmp sgt i32 %c, 0
  br i1 %t, label %l1, label %l2
l1:
  %x = extractvalue { double, double } %r, 0
  ret double %x
l2:
  %y = extractvalue { double, double } %r, 1
  ret double %y
}

; one field of two, and unused results
define double @t_partial(double %a, double %b) {
  %r = call { double, double } @mkc(double %a, double %b)
  %u = call { <2 x float>, <2 x float> } @mk4(float 1.0, float 2.0, float 3.0, float 4.0)
  %v = call { i64, i64 } @mkll(i64 5, i64 6)
  %y = extractvalue { double, double } %r, 1
  ret double %y
}

; integer and mixed parts: rax/rdx and xmm0/xmm1, narrow integers
define double @t_gpr(i64 %n, double %d, ptr %q) {
  %r1 = call { i64, double } @mkld(i64 %n, double %d)
  %a1 = extractvalue { i64, double } %r1, 0
  %b1 = extractvalue { i64, double } %r1, 1
  %r2 = call { double, i32 } @mkdi(double %d, i32 -3)
  %b2 = extractvalue { double, i32 } %r2, 1
  %a2 = extractvalue { double, i32 } %r2, 0
  %r3 = call { i8, double } @mkcd(i32 200, double %d)
  %a3 = extractvalue { i8, double } %r3, 0
  %b3 = extractvalue { i8, double } %r3, 1
  %r4 = call { ptr, i32 } @mkpi(ptr %q, i32 9)
  %a4 = extractvalue { ptr, i32 } %r4, 0
  %b4 = extractvalue { ptr, i32 } %r4, 1
  %r5 = call { i64, i64 } @mkll(i64 %n, i64 -7)
  %b5 = extractvalue { i64, i64 } %r5, 1
  %a5 = extractvalue { i64, i64 } %r5, 0
  %r6 = call { float, double } @mkfd(float 0.5, double %d)
  %a6 = extractvalue { float, double } %r6, 0
  %b6 = extractvalue { float, double } %r6, 1
  ; the i8 is used zero-extended, the i32 sign-extended to 64 bits
  %a3z = zext i8 %a3 to i64
  %b2s = sext i32 %b2 to i64
  %b4s = sext i32 %b4 to i64
  %pv = load i64, ptr %a4, align 8
  %i1 = add i64 %a1, %a3z
  %i2 = mul i64 %b2s, 1000
  %i3 = add i64 %i1, %i2
  %i4 = add i64 %i3, %b4s
  %i5 = add i64 %i4, %pv
  %i6 = add i64 %i5, %a5
  %i7 = mul i64 %b5, 100000
  %i8 = add i64 %i6, %i7
  %f1 = sitofp i64 %i8 to double
  %f2 = fadd double %f1, %b1
  %f3 = fadd double %f2, %a2
  %f4 = fadd double %f3, %b3
  %a6d = fpext float %a6 to double
  %f5 = fadd double %f4, %a6d
  %f6 = fadd double %f5, %b6
  ret double %f6
}

; a use that is not an extractvalue (not fused)
define double @t_whole_use(double %a, double %b, ptr %out) {
  %r = call { double, double } @mkc(double %a, double %b)
  store { double, double } %r, ptr %out, align 8
  %x = extractvalue { double, double } %r, 0
  ret double %x
}

; a legacy-lowered instruction (i128 arithmetic) between call and extractvalues
define double @t_legacy_between(double %a, double %b, i64 %k) {
  %r = call { double, double } @mkc(double %a, double %b)
  %w = zext i64 %k to i128
  %w2 = mul i128 %w, 18446744073709551616
  %w3 = lshr i128 %w2, 63
  %t = trunc i128 %w3 to i64
  %x = extractvalue { double, double } %r, 0
  %y = extractvalue { double, double } %r, 1
  %tf = sitofp i64 %t to double
  %s1 = fadd double %x, %tf
  %y2 = fmul double %y, 10.0
  %s2 = fadd double %s1, %y2
  ret double %s2
}

; a field value that lives across calls, in a register class (<2 x float>)
define float @t_live_across(float %a, float %b, float %c) {
  %r = call { <2 x float>, float } @mk3(float %a, float %b, float %c)
  %v = extractvalue { <2 x float>, float } %r, 0
  %z = extractvalue { <2 x float>, float } %r, 1
  call void @clobber()
  %r2 = call { <2 x float>, float } @mk3(float 10.0, float 20.0, float 30.0)
  %v2 = extractvalue { <2 x float>, float } %r2, 0
  call void @clobber()
  %s = fadd <2 x float> %v, %v2
  %s0 = extractelement <2 x float> %s, i32 0
  %s1 = extractelement <2 x float> %s, i32 1
  %s1b = fmul float %s1, 2.0
  %z3 = fmul float %z, 3.0
  %u1 = fadd float %s0, %s1b
  %u2 = fadd float %u1, %z3
  ret float %u2
}

; aggregate loads returned: from a frame temporary (deferred), through a
; pointer argument, and with a store between load and return
define { double, double } @t_load_ret(double %a, double %b) {
  %p = alloca { double, double }, align 8
  store double %a, ptr %p, align 8
  %p1 = getelementptr inbounds i8, ptr %p, i64 8
  store double %b, ptr %p1, align 8
  %l = load { double, double }, ptr %p, align 8
  ret { double, double } %l
}
define { double, double } @t_load_ret_ptr(ptr %q) {
  %l = load { double, double }, ptr %q, align 8
  ret { double, double } %l
}
define { double, double } @t_load_store_ret(double %a, double %b) {
  %p = alloca { double, double }, align 8
  store double %a, ptr %p, align 8
  %p1 = getelementptr inbounds i8, ptr %p, i64 8
  store double %b, ptr %p1, align 8
  %l = load { double, double }, ptr %p, align 8
  store double 0.0, ptr %p, align 8
  ret { double, double } %l
}
define { <2 x float>, <2 x float> } @t_load_ret4(float %a, float %b, float %c, float %d) {
  %p = alloca [4 x float], align 4
  store float %a, ptr %p, align 4
  %p1 = getelementptr inbounds float, ptr %p, i64 1
  store float %b, ptr %p1, align 4
  %p2 = getelementptr inbounds float, ptr %p, i64 2
  store float %c, ptr %p2, align 4
  %p3 = getelementptr inbounds float, ptr %p, i64 3
  store float %d, ptr %p3, align 4
  %l = load { <2 x float>, <2 x float> }, ptr %p, align 4
  ret { <2 x float>, <2 x float> } %l
}

; extractvalue from a loaded aggregate, from insertvalue chains, from a
; constant, and of an i1 field
define double @t_ev_sources(i64 %n, double %d, double %g, double %h) {
  %a1 = insertvalue { double, double } undef, double %g, 0
  %arg = insertvalue { double, double } %a1, double %h, 1
  %p = alloca { i64, double }, align 8
  store i64 %n, ptr %p, align 8
  %p1 = getelementptr inbounds i8, ptr %p, i64 8
  store double %d, ptr %p1, align 8
  %l = load { i64, double }, ptr %p, align 8
  %e1 = extractvalue { i64, double } %l, 1
  %i1 = insertvalue { double, i32 } undef, double %d, 0
  %i2 = insertvalue { double, i32 } %i1, i32 -5, 1
  %e2 = extractvalue { double, i32 } %i2, 0
  %e3 = extractvalue { double, i32 } %i2, 1
  %e4 = extractvalue { double, i32 } { double 1.25, i32 7 }, 0
  %e5 = extractvalue { double, double } %arg, 0
  %e6 = extractvalue { double, double } %arg, 1
  %c = icmp sgt i64 %n, 2
  %j1 = insertvalue { i64, i1 } undef, i64 %n, 0
  %j2 = insertvalue { i64, i1 } %j1, i1 %c, 1
  %e7 = extractvalue { i64, i1 } %j2, 1
  %e3f = sitofp i32 %e3 to double
  %e7z = zext i1 %e7 to i32
  %e7f = sitofp i32 %e7z to double
  %s1 = fadd double %e1, %e2
  %s2 = fadd double %s1, %e3f
  %s3 = fadd double %s2, %e4
  %e6b = fmul double %e6, 100.0
  %s4 = fadd double %s3, %e5
  %s5 = fadd double %s4, %e6b
  %e7b = fmul double %e7f, 1000.0
  %s6 = fadd double %s5, %e7b
  ret double %s6
}
