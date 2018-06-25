; NOTE: Assertions have been autogenerated by utils/update_test_checks.py
; RUN: opt < %s -instcombine -S | FileCheck %s

define i32 @select_0_or_1_from_bool(i1 %x) {
; CHECK-LABEL: @select_0_or_1_from_bool(
; CHECK-NEXT:    [[TMP1:%.*]] = xor i1 [[X:%.*]], true
; CHECK-NEXT:    [[ADD:%.*]] = zext i1 [[TMP1]] to i32
; CHECK-NEXT:    ret i32 [[ADD]]
;
  %ext = sext i1 %x to i32
  %add = add i32 %ext, 1
  ret i32 %add
}

define <2 x i32> @select_0_or_1_from_bool_vec(<2 x i1> %x) {
; CHECK-LABEL: @select_0_or_1_from_bool_vec(
; CHECK-NEXT:    [[TMP1:%.*]] = xor <2 x i1> [[X:%.*]], <i1 true, i1 true>
; CHECK-NEXT:    [[ADD:%.*]] = zext <2 x i1> [[TMP1]] to <2 x i32>
; CHECK-NEXT:    ret <2 x i32> [[ADD]]
;
  %ext = sext <2 x i1> %x to <2 x i32>
  %add = add <2 x i32> %ext, <i32 1, i32 1>
  ret <2 x i32> %add
}

define i32 @select_C_minus_1_or_C_from_bool(i1 %x) {
; CHECK-LABEL: @select_C_minus_1_or_C_from_bool(
; CHECK-NEXT:    [[EXT:%.*]] = sext i1 [[X:%.*]] to i32
; CHECK-NEXT:    [[ADD:%.*]] = add nsw i32 [[EXT]], 42
; CHECK-NEXT:    ret i32 [[ADD]]
;
  %ext = sext i1 %x to i32
  %add = add i32 %ext, 42
  ret i32 %add
}

define <2 x i32> @select_C_minus_1_or_C_from_bool_vec(<2 x i1> %x) {
; CHECK-LABEL: @select_C_minus_1_or_C_from_bool_vec(
; CHECK-NEXT:    [[EXT:%.*]] = sext <2 x i1> [[X:%.*]] to <2 x i32>
; CHECK-NEXT:    [[ADD:%.*]] = add nsw <2 x i32> [[EXT]], <i32 42, i32 43>
; CHECK-NEXT:    ret <2 x i32> [[ADD]]
;
  %ext = sext <2 x i1> %x to <2 x i32>
  %add = add <2 x i32> %ext, <i32 42, i32 43>
  ret <2 x i32> %add
}

; This is an 'andn' of the low bit.

define i32 @flip_and_mask(i32 %x) {
; CHECK-LABEL: @flip_and_mask(
; CHECK-NEXT:    [[TMP1:%.*]] = and i32 [[X:%.*]], 1
; CHECK-NEXT:    [[INC:%.*]] = xor i32 [[TMP1]], 1
; CHECK-NEXT:    ret i32 [[INC]]
;
  %shl = shl i32 %x, 31
  %shr = ashr i32 %shl, 31
  %inc = add i32 %shr, 1
  ret i32 %inc
}

define <2 x i8> @flip_and_mask_splat(<2 x i8> %x) {
; CHECK-LABEL: @flip_and_mask_splat(
; CHECK-NEXT:    [[TMP1:%.*]] = and <2 x i8> [[X:%.*]], <i8 1, i8 1>
; CHECK-NEXT:    [[INC:%.*]] = xor <2 x i8> [[TMP1]], <i8 1, i8 1>
; CHECK-NEXT:    ret <2 x i8> [[INC]]
;
  %shl = shl <2 x i8> %x, <i8 7, i8 7>
  %shr = ashr <2 x i8> %shl, <i8 7, i8 7>
  %inc = add <2 x i8> %shr, <i8 1, i8 1>
  ret <2 x i8> %inc
}

define i32 @test1(i32 %A) {
; CHECK-LABEL: @test1(
; CHECK-NEXT:    ret i32 [[A:%.*]]
;
  %B = add i32 %A, 0
  ret i32 %B
}

define i32 @test2(i32 %A) {
; CHECK-LABEL: @test2(
; CHECK-NEXT:    ret i32 [[A:%.*]]
;
  %B = add i32 %A, 5
  %C = add i32 %B, -5
  ret i32 %C
}

define i32 @test3(i32 %A) {
; CHECK-LABEL: @test3(
; CHECK-NEXT:    ret i32 [[A:%.*]]
;
  %B = add i32 %A, 5
  %C = sub i32 %B, 5
  ret i32 %C
}

; D = B + -A = B - A
define i32 @test4(i32 %A, i32 %B) {
; CHECK-LABEL: @test4(
; CHECK-NEXT:    [[D:%.*]] = sub i32 [[B:%.*]], [[A:%.*]]
; CHECK-NEXT:    ret i32 [[D]]
;
  %C = sub i32 0, %A
  %D = add i32 %B, %C
  ret i32 %D
}

; D = -A + B = B - A
define i32 @test5(i32 %A, i32 %B) {
; CHECK-LABEL: @test5(
; CHECK-NEXT:    [[D:%.*]] = sub i32 [[B:%.*]], [[A:%.*]]
; CHECK-NEXT:    ret i32 [[D]]
;
  %C = sub i32 0, %A
  %D = add i32 %C, %B
  ret i32 %D
}

; C = 7*A+A == 8*A == A << 3
define i32 @test6(i32 %A) {
; CHECK-LABEL: @test6(
; CHECK-NEXT:    [[C:%.*]] = shl i32 [[A:%.*]], 3
; CHECK-NEXT:    ret i32 [[C]]
;
  %B = mul i32 7, %A
  %C = add i32 %B, %A
  ret i32 %C
}

; C = A+7*A == 8*A == A << 3
define i32 @test7(i32 %A) {
; CHECK-LABEL: @test7(
; CHECK-NEXT:    [[C:%.*]] = shl i32 [[A:%.*]], 3
; CHECK-NEXT:    ret i32 [[C]]
;
  %B = mul i32 7, %A
  %C = add i32 %A, %B
  ret i32 %C
}

; (A & C1)+(B & C2) -> (A & C1)|(B & C2) iff C1&C2 == 0
define i32 @test8(i32 %A, i32 %B) {
; CHECK-LABEL: @test8(
; CHECK-NEXT:    [[A1:%.*]] = and i32 [[A:%.*]], 7
; CHECK-NEXT:    [[B1:%.*]] = and i32 [[B:%.*]], 128
; CHECK-NEXT:    [[C:%.*]] = or i32 [[A1]], [[B1]]
; CHECK-NEXT:    ret i32 [[C]]
;
  %A1 = and i32 %A, 7
  %B1 = and i32 %B, 128
  %C = add i32 %A1, %B1
  ret i32 %C
}

define i32 @test9(i32 %A) {
; CHECK-LABEL: @test9(
; CHECK-NEXT:    [[C:%.*]] = shl i32 [[A:%.*]], 5
; CHECK-NEXT:    ret i32 [[C]]
;
  %B = shl i32 %A, 4
  %C = add i32 %B, %B
  ret i32 %C
}

; a != -b
define i1 @test10(i8 %a, i8 %b) {
; CHECK-LABEL: @test10(
; CHECK-NEXT:    [[ADD:%.*]] = sub i8 0, [[B:%.*]]
; CHECK-NEXT:    [[C:%.*]] = icmp ne i8 [[ADD]], [[A:%.*]]
; CHECK-NEXT:    ret i1 [[C]]
;
  %add = add i8 %a, %b
  %c = icmp ne i8 %add, 0
  ret i1 %c
}

define <2 x i1> @test10vec(<2 x i8> %a, <2 x i8> %b) {
; CHECK-LABEL: @test10vec(
; CHECK-NEXT:    [[C:%.*]] = sub <2 x i8> zeroinitializer, [[B:%.*]]
; CHECK-NEXT:    [[D:%.*]] = icmp ne <2 x i8> [[C]], [[A:%.*]]
; CHECK-NEXT:    ret <2 x i1> [[D]]
;
  %c = add <2 x i8> %a, %b
  %d = icmp ne <2 x i8> %c, zeroinitializer
  ret <2 x i1> %d
}

define i1 @test11(i8 %A) {
; CHECK-LABEL: @test11(
; CHECK-NEXT:    [[C:%.*]] = icmp ne i8 [[A:%.*]], 1
; CHECK-NEXT:    ret i1 [[C]]
;
  %B = add i8 %A, -1
  %c = icmp ne i8 %B, 0
  ret i1 %c
}

define <2 x i1> @test11vec(<2 x i8> %a) {
; CHECK-LABEL: @test11vec(
; CHECK-NEXT:    [[C:%.*]] = icmp ne <2 x i8> [[A:%.*]], <i8 1, i8 1>
; CHECK-NEXT:    ret <2 x i1> [[C]]
;
  %b = add <2 x i8> %a, <i8 -1, i8 -1>
  %c = icmp ne <2 x i8> %b, zeroinitializer
  ret <2 x i1> %c
}

; Should be transformed into shl A, 1?

define i32 @test12(i32 %A, i32 %B) {
; CHECK-LABEL: @test12(
; CHECK-NEXT:    br label [[X:%.*]]
; CHECK:       X:
; CHECK-NEXT:    [[C_OK:%.*]] = add i32 [[B:%.*]], [[A:%.*]]
; CHECK-NEXT:    [[D:%.*]] = add i32 [[C_OK]], [[A]]
; CHECK-NEXT:    ret i32 [[D]]
;
  %C_OK = add i32 %B, %A
  br label %X

X:              ; preds = %0
  %D = add i32 %C_OK, %A
  ret i32 %D
}

;; TODO: shl A, 1?
define i32 @test13(i32 %A, i32 %B, i32 %C) {
; CHECK-LABEL: @test13(
; CHECK-NEXT:    [[D_OK:%.*]] = add i32 [[A:%.*]], [[B:%.*]]
; CHECK-NEXT:    [[E_OK:%.*]] = add i32 [[D_OK]], [[C:%.*]]
; CHECK-NEXT:    [[F:%.*]] = add i32 [[E_OK]], [[A]]
; CHECK-NEXT:    ret i32 [[F]]
;
  %D_OK = add i32 %A, %B
  %E_OK = add i32 %D_OK, %C
  %F = add i32 %E_OK, %A
  ret i32 %F
}

define i32 @test14(i32 %offset, i32 %difference) {
; CHECK-LABEL: @test14(
; CHECK-NEXT:    [[TMP_2:%.*]] = and i32 [[DIFFERENCE:%.*]], 3
; CHECK-NEXT:    [[TMP_3_OK:%.*]] = add i32 [[TMP_2]], [[OFFSET:%.*]]
; CHECK-NEXT:    [[TMP_5_MASK:%.*]] = and i32 [[DIFFERENCE]], -4
; CHECK-NEXT:    [[TMP_8:%.*]] = add i32 [[TMP_3_OK]], [[TMP_5_MASK]]
; CHECK-NEXT:    ret i32 [[TMP_8]]
;
  %tmp.2 = and i32 %difference, 3
  %tmp.3_OK = add i32 %tmp.2, %offset
  %tmp.5.mask = and i32 %difference, -4
  ; == add %offset, %difference
  %tmp.8 = add i32 %tmp.3_OK, %tmp.5.mask
  ret i32 %tmp.8
}

; Only one bit set
define i8 @test15(i8 %A) {
; CHECK-LABEL: @test15(
; CHECK-NEXT:    [[C:%.*]] = and i8 [[A:%.*]], 16
; CHECK-NEXT:    ret i8 [[C]]
;
  %B = add i8 %A, -64
  %C = and i8 %B, 16
  ret i8 %C
}

; Only one bit set
define i8 @test16(i8 %A) {
; CHECK-LABEL: @test16(
; CHECK-NEXT:    [[B:%.*]] = and i8 [[A:%.*]], 16
; CHECK-NEXT:    [[C:%.*]] = xor i8 [[B]], 16
; CHECK-NEXT:    ret i8 [[C]]
;
  %B = add i8 %A, 16
  %C = and i8 %B, 16
  ret i8 %C
}

define i32 @test17(i32 %A) {
; CHECK-LABEL: @test17(
; CHECK-NEXT:    [[C:%.*]] = sub i32 0, [[A:%.*]]
; CHECK-NEXT:    ret i32 [[C]]
;
  %B = xor i32 %A, -1
  %C = add i32 %B, 1
  ret i32 %C
}

define i8 @test18(i8 %A) {
; CHECK-LABEL: @test18(
; CHECK-NEXT:    [[C:%.*]] = sub i8 16, [[A:%.*]]
; CHECK-NEXT:    ret i8 [[C]]
;
  %B = xor i8 %A, -1
  %C = add i8 %B, 17
  ret i8 %C
}

define <2 x i64> @test18vec(<2 x i64> %A) {
; CHECK-LABEL: @test18vec(
; CHECK-NEXT:    [[ADD:%.*]] = sub <2 x i64> <i64 1, i64 2>, [[A:%.*]]
; CHECK-NEXT:    ret <2 x i64> [[ADD]]
;
  %xor = xor <2 x i64> %A, <i64 -1, i64 -1>
  %add = add <2 x i64> %xor, <i64 2, i64 3>
  ret <2 x i64> %add
}

define i32 @test19(i1 %C) {
; CHECK-LABEL: @test19(
; CHECK-NEXT:    [[V:%.*]] = select i1 [[C:%.*]], i32 1123, i32 133
; CHECK-NEXT:    ret i32 [[V]]
;
  %A = select i1 %C, i32 1000, i32 10
  %V = add i32 %A, 123
  ret i32 %V
}

define <2 x i32> @test19vec(i1 %C) {
; CHECK-LABEL: @test19vec(
; CHECK-NEXT:    [[V:%.*]] = select i1 [[C:%.*]], <2 x i32> <i32 1123, i32 1123>, <2 x i32> <i32 133, i32 133>
; CHECK-NEXT:    ret <2 x i32> [[V]]
;
  %A = select i1 %C, <2 x i32> <i32 1000, i32 1000>, <2 x i32> <i32 10, i32 10>
  %V = add <2 x i32> %A, <i32 123, i32 123>
  ret <2 x i32> %V
}

; This is an InstSimplify fold, but test it here to make sure that
; InstCombine does not prevent the fold.
; With NSW, add of sign bit -> or of sign bit.

define i32 @test20(i32 %x) {
; CHECK-LABEL: @test20(
; CHECK-NEXT:    ret i32 [[X:%.*]]
;
  %y = xor i32 %x, -2147483648
  %z = add nsw i32 %y, -2147483648
  ret i32 %z
}

define i32 @xor_sign_bit(i32 %x) {
; CHECK-LABEL: @xor_sign_bit(
; CHECK-NEXT:    [[ADD:%.*]] = add i32 [[X:%.*]], -2147483606
; CHECK-NEXT:    ret i32 [[ADD]]
;
  %xor = xor i32 %x, 2147483648
  %add = add i32 %xor, 42
  ret i32 %add
}

; No-wrap info allows converting the add to 'or'.

define i8 @add_nsw_signbit(i8 %x) {
; CHECK-LABEL: @add_nsw_signbit(
; CHECK-NEXT:    [[Y:%.*]] = or i8 [[X:%.*]], -128
; CHECK-NEXT:    ret i8 [[Y]]
;
  %y = add nsw i8 %x, -128
  ret i8 %y
}

; No-wrap info allows converting the add to 'or'.

define i8 @add_nuw_signbit(i8 %x) {
; CHECK-LABEL: @add_nuw_signbit(
; CHECK-NEXT:    [[Y:%.*]] = or i8 [[X:%.*]], -128
; CHECK-NEXT:    ret i8 [[Y]]
;
  %y = add nuw i8 %x, 128
  ret i8 %y
}

define i1 @test21(i32 %x) {
; CHECK-LABEL: @test21(
; CHECK-NEXT:    [[Y:%.*]] = icmp eq i32 [[X:%.*]], 119
; CHECK-NEXT:    ret i1 [[Y]]
;
  %t = add i32 %x, 4
  %y = icmp eq i32 %t, 123
  ret i1 %y
}

define <2 x i1> @test21vec(<2 x i32> %x) {
; CHECK-LABEL: @test21vec(
; CHECK-NEXT:    [[Y:%.*]] = icmp eq <2 x i32> [[X:%.*]], <i32 119, i32 119>
; CHECK-NEXT:    ret <2 x i1> [[Y]]
;
  %t = add <2 x i32> %x, <i32 4, i32 4>
  %y = icmp eq <2 x i32> %t, <i32 123, i32 123>
  ret <2 x i1> %y
}

define i32 @test22(i32 %V) {
; CHECK-LABEL: @test22(
; CHECK-NEXT:    switch i32 [[V:%.*]], label [[DEFAULT:%.*]] [
; CHECK-NEXT:    i32 10, label [[LAB1:%.*]]
; CHECK-NEXT:    i32 20, label [[LAB2:%.*]]
; CHECK-NEXT:    ]
; CHECK:       Default:
; CHECK-NEXT:    ret i32 123
; CHECK:       Lab1:
; CHECK-NEXT:    ret i32 12312
; CHECK:       Lab2:
; CHECK-NEXT:    ret i32 1231231
;
  %V2 = add i32 %V, 10
  switch i32 %V2, label %Default [
  i32 20, label %Lab1
  i32 30, label %Lab2
  ]

Default:                ; preds = %0
  ret i32 123

Lab1:           ; preds = %0
  ret i32 12312

Lab2:           ; preds = %0
  ret i32 1231231
}

define i32 @test23(i1 %C, i32 %a) {
; CHECK-LABEL: @test23(
; CHECK-NEXT:  entry:
; CHECK-NEXT:    br i1 [[C:%.*]], label [[ENDIF:%.*]], label [[ELSE:%.*]]
; CHECK:       else:
; CHECK-NEXT:    br label [[ENDIF]]
; CHECK:       endif:
; CHECK-NEXT:    [[B_0:%.*]] = phi i32 [ 1, [[ENTRY:%.*]] ], [ 2, [[ELSE]] ]
; CHECK-NEXT:    ret i32 [[B_0]]
;
entry:
  br i1 %C, label %endif, label %else

else:           ; preds = %entry
  br label %endif

endif:          ; preds = %else, %entry
  %b.0 = phi i32 [ 0, %entry ], [ 1, %else ]
  %tmp.4 = add i32 %b.0, 1
  ret i32 %tmp.4
}

define i32 @test24(i32 %A) {
; CHECK-LABEL: @test24(
; CHECK-NEXT:    [[B:%.*]] = shl i32 [[A:%.*]], 1
; CHECK-NEXT:    ret i32 [[B]]
;
  %B = add i32 %A, 1
  %C = shl i32 %B, 1
  %D = sub i32 %C, 2
  ret i32 %D
}

define i64 @test25(i64 %Y) {
; CHECK-LABEL: @test25(
; CHECK-NEXT:    [[TMP_8:%.*]] = shl i64 [[Y:%.*]], 3
; CHECK-NEXT:    ret i64 [[TMP_8]]
;
  %tmp.4 = shl i64 %Y, 2
  %tmp.12 = shl i64 %Y, 2
  %tmp.8 = add i64 %tmp.4, %tmp.12
  ret i64 %tmp.8
}

define i32 @test26(i32 %A, i32 %B) {
; CHECK-LABEL: @test26(
; CHECK-NEXT:    ret i32 [[A:%.*]]
;
  %C = add i32 %A, %B
  %D = sub i32 %C, %B
  ret i32 %D
}

; Fold add through select.
define i32 @test27(i1 %C, i32 %X, i32 %Y) {
; CHECK-LABEL: @test27(
; CHECK-NEXT:    [[C_UPGRD_1_V:%.*]] = select i1 [[C:%.*]], i32 [[X:%.*]], i32 123
; CHECK-NEXT:    ret i32 [[C_UPGRD_1_V]]
;
  %A = add i32 %X, %Y
  %B = add i32 %Y, 123
  %C.upgrd.1 = select i1 %C, i32 %A, i32 %B
  %D = sub i32 %C.upgrd.1, %Y
  ret i32 %D
}

define i32 @test28(i32 %X) {
; CHECK-LABEL: @test28(
; CHECK-NEXT:    [[Z:%.*]] = sub i32 -1192, [[X:%.*]]
; CHECK-NEXT:    ret i32 [[Z]]
;
  %Y = add i32 %X, 1234
  %Z = sub i32 42, %Y
  ret i32 %Z
}

define i32 @test29(i32 %x, i32 %y) {
; CHECK-LABEL: @test29(
; CHECK-NEXT:    [[TMP_2:%.*]] = sub i32 [[X:%.*]], [[Y:%.*]]
; CHECK-NEXT:    [[TMP_7:%.*]] = and i32 [[X]], 63
; CHECK-NEXT:    [[TMP_9:%.*]] = and i32 [[TMP_2]], -64
; CHECK-NEXT:    [[TMP_10:%.*]] = or i32 [[TMP_7]], [[TMP_9]]
; CHECK-NEXT:    ret i32 [[TMP_10]]
;
  %tmp.2 = sub i32 %x, %y
  %tmp.2.mask = and i32 %tmp.2, 63
  %tmp.6 = add i32 %tmp.2.mask, %y
  %tmp.7 = and i32 %tmp.6, 63
  %tmp.9 = and i32 %tmp.2, -64
  %tmp.10 = or i32 %tmp.7, %tmp.9
  ret i32 %tmp.10
}

; Add of sign bit -> xor of sign bit.
define i64 @test30(i64 %x) {
; CHECK-LABEL: @test30(
; CHECK-NEXT:    ret i64 [[X:%.*]]
;
  %tmp.2 = xor i64 %x, -9223372036854775808
  %tmp.4 = add i64 %tmp.2, -9223372036854775808
  ret i64 %tmp.4
}

define i32 @test31(i32 %A) {
; CHECK-LABEL: @test31(
; CHECK-NEXT:    [[TMP1:%.*]] = mul i32 [[A:%.*]], 5
; CHECK-NEXT:    ret i32 [[TMP1]]
;
  %B = add i32 %A, 4
  %C = mul i32 %B, 5
  %D = sub i32 %C, 20
  ret i32 %D
}

define i32 @test32(i32 %A) {
; CHECK-LABEL: @test32(
; CHECK-NEXT:    [[B:%.*]] = shl i32 [[A:%.*]], 2
; CHECK-NEXT:    ret i32 [[B]]
;
  %B = add i32 %A, 4
  %C = shl i32 %B, 2
  %D = sub i32 %C, 16
  ret i32 %D
}

define i8 @test33(i8 %A) {
; CHECK-LABEL: @test33(
; CHECK-NEXT:    [[C:%.*]] = or i8 [[A:%.*]], 1
; CHECK-NEXT:    ret i8 [[C]]
;
  %B = and i8 %A, -2
  %C = add i8 %B, 1
  ret i8 %C
}

define i8 @test34(i8 %A) {
; CHECK-LABEL: @test34(
; CHECK-NEXT:    [[C:%.*]] = and i8 [[A:%.*]], 12
; CHECK-NEXT:    ret i8 [[C]]
;
  %B = add i8 %A, 64
  %C = and i8 %B, 12
  ret i8 %C
}

; If all bits affected by the add are included
; in the mask, do the add before the mask op.

define i8 @masked_add(i8 %x) {
; CHECK-LABEL: @masked_add(
; CHECK-NEXT:    [[AND1:%.*]] = add i8 [[X:%.*]], 96
; CHECK-NEXT:    [[R:%.*]] = and i8 [[AND1]], -16
; CHECK-NEXT:    ret i8 [[R]]
;
  %and = and i8 %x, 240 ; 0xf0
  %r = add i8 %and, 96  ; 0x60
  ret i8 %r
}

define <2 x i8> @masked_add_splat(<2 x i8> %x) {
; CHECK-LABEL: @masked_add_splat(
; CHECK-NEXT:    [[AND:%.*]] = and <2 x i8> [[X:%.*]], <i8 -64, i8 -64>
; CHECK-NEXT:    [[R:%.*]] = add <2 x i8> [[AND]], <i8 64, i8 64>
; CHECK-NEXT:    ret <2 x i8> [[R]]
;
  %and = and <2 x i8> %x, <i8 192, i8 192> ; 0xc0
  %r = add <2 x i8> %and, <i8 64, i8 64>  ; 0x40
  ret <2 x i8> %r
}

define i8 @not_masked_add(i8 %x) {
; CHECK-LABEL: @not_masked_add(
; CHECK-NEXT:    [[AND:%.*]] = and i8 [[X:%.*]], 112
; CHECK-NEXT:    [[R:%.*]] = add nuw i8 [[AND]], 96
; CHECK-NEXT:    ret i8 [[R]]
;
  %and = and i8 %x, 112 ; 0x70
  %r = add i8 %and, 96  ; 0x60
  ret i8 %r
}

define i32 @test35(i32 %a) {
; CHECK-LABEL: @test35(
; CHECK-NEXT:    ret i32 -1
;
  %tmpnot = xor i32 %a, -1
  %tmp2 = add i32 %tmpnot, %a
  ret i32 %tmp2
}

define i32 @test36(i32 %a) {
; CHECK-LABEL: @test36(
; CHECK-NEXT:    ret i32 0
;
  %x = and i32 %a, -2
  %y = and i32 %a, -126
  %z = add i32 %x, %y
  %q = and i32 %z, 1  ; always zero
  ret i32 %q
}

define i1 @test37(i32 %a, i32 %b) {
; CHECK-LABEL: @test37(
; CHECK-NEXT:    [[CMP:%.*]] = icmp eq i32 [[B:%.*]], 0
; CHECK-NEXT:    ret i1 [[CMP]]
;
  %add = add i32 %a, %b
  %cmp = icmp eq i32 %add, %a
  ret i1 %cmp
}

define i1 @test38(i32 %a, i32 %b) {
; CHECK-LABEL: @test38(
; CHECK-NEXT:    [[CMP:%.*]] = icmp eq i32 [[A:%.*]], 0
; CHECK-NEXT:    ret i1 [[CMP]]
;
  %add = add i32 %a, %b
  %cmp = icmp eq i32 %add, %b
  ret i1 %cmp
}

define i1 @test39(i32 %a, i32 %b) {
; CHECK-LABEL: @test39(
; CHECK-NEXT:    [[CMP:%.*]] = icmp eq i32 [[B:%.*]], 0
; CHECK-NEXT:    ret i1 [[CMP]]
;
  %add = add i32 %b, %a
  %cmp = icmp eq i32 %add, %a
  ret i1 %cmp
}

define i1 @test40(i32 %a, i32 %b) {
; CHECK-LABEL: @test40(
; CHECK-NEXT:    [[CMP:%.*]] = icmp eq i32 [[A:%.*]], 0
; CHECK-NEXT:    ret i1 [[CMP]]
;
  %add = add i32 %b, %a
  %cmp = icmp eq i32 %add, %b
  ret i1 %cmp
}

; (add (zext (add nuw X, C2)), C) --> (zext (add nuw X, C2 + C))

define i64 @test41(i32 %a) {
; CHECK-LABEL: @test41(
; CHECK-NEXT:    [[TMP1:%.*]] = add nuw i32 [[A:%.*]], 15
; CHECK-NEXT:    [[SUB:%.*]] = zext i32 [[TMP1]] to i64
; CHECK-NEXT:    ret i64 [[SUB]]
;
  %add = add nuw i32 %a, 16
  %zext = zext i32 %add to i64
  %sub = add i64 %zext, -1
  ret i64 %sub
}

; (add (zext (add nuw X, C2)), C) --> (zext (add nuw X, C2 + C))

define <2 x i64> @test41vec(<2 x i32> %a) {
; CHECK-LABEL: @test41vec(
; CHECK-NEXT:    [[TMP1:%.*]] = add nuw <2 x i32> [[A:%.*]], <i32 15, i32 15>
; CHECK-NEXT:    [[SUB:%.*]] = zext <2 x i32> [[TMP1]] to <2 x i64>
; CHECK-NEXT:    ret <2 x i64> [[SUB]]
;
  %add = add nuw <2 x i32> %a, <i32 16, i32 16>
  %zext = zext <2 x i32> %add to <2 x i64>
  %sub = add <2 x i64> %zext, <i64 -1, i64 -1>
  ret <2 x i64> %sub
}

define <2 x i64> @test41vec_and_multiuse(<2 x i32> %a) {
; CHECK-LABEL: @test41vec_and_multiuse(
; CHECK-NEXT:    [[ADD:%.*]] = add nuw <2 x i32> [[A:%.*]], <i32 16, i32 16>
; CHECK-NEXT:    [[ZEXT:%.*]] = zext <2 x i32> [[ADD]] to <2 x i64>
; CHECK-NEXT:    [[SUB:%.*]] = add nsw <2 x i64> [[ZEXT]], <i64 -1, i64 -1>
; CHECK-NEXT:    [[EXTRAUSE:%.*]] = add nsw <2 x i64> [[SUB]], [[ZEXT]]
; CHECK-NEXT:    ret <2 x i64> [[EXTRAUSE]]
;
  %add = add nuw <2 x i32> %a, <i32 16, i32 16>
  %zext = zext <2 x i32> %add to <2 x i64>
  %sub = add <2 x i64> %zext, <i64 -1, i64 -1>
  %extrause = add <2 x i64> %zext, %sub
  ret <2 x i64> %extrause
}

define i32 @test42(i1 %C) {
; CHECK-LABEL: @test42(
; CHECK-NEXT:    [[V:%.*]] = select i1 [[C:%.*]], i32 1123, i32 133
; CHECK-NEXT:    ret i32 [[V]]
;
  %A = select i1 %C, i32 1000, i32 10
  %V = add i32 123, %A
  ret i32 %V
}

define <2 x i32> @test42vec(i1 %C) {
; CHECK-LABEL: @test42vec(
; CHECK-NEXT:    [[V:%.*]] = select i1 [[C:%.*]], <2 x i32> <i32 1123, i32 1123>, <2 x i32> <i32 133, i32 133>
; CHECK-NEXT:    ret <2 x i32> [[V]]
;
  %A = select i1 %C, <2 x i32> <i32 1000, i32 1000>, <2 x i32> <i32 10, i32 10>
  %V = add <2 x i32> <i32 123, i32 123>, %A
  ret <2 x i32> %V
}

define <2 x i32> @test42vec2(i1 %C) {
; CHECK-LABEL: @test42vec2(
; CHECK-NEXT:    [[V:%.*]] = select i1 [[C:%.*]], <2 x i32> <i32 1123, i32 2833>, <2 x i32> <i32 133, i32 363>
; CHECK-NEXT:    ret <2 x i32> [[V]]
;
  %A = select i1 %C, <2 x i32> <i32 1000, i32 2500>, <2 x i32> <i32 10, i32 30>
  %V = add <2 x i32> <i32 123, i32 333>, %A
  ret <2 x i32> %V
}

define i32 @test55(i1 %which) {
; CHECK-LABEL: @test55(
; CHECK-NEXT:  entry:
; CHECK-NEXT:    br i1 [[WHICH:%.*]], label [[FINAL:%.*]], label [[DELAY:%.*]]
; CHECK:       delay:
; CHECK-NEXT:    br label [[FINAL]]
; CHECK:       final:
; CHECK-NEXT:    [[A:%.*]] = phi i32 [ 1123, [[ENTRY:%.*]] ], [ 133, [[DELAY]] ]
; CHECK-NEXT:    ret i32 [[A]]
;
entry:
  br i1 %which, label %final, label %delay

delay:
  br label %final

final:
  %A = phi i32 [ 1000, %entry ], [ 10, %delay ]
  %value = add i32 123, %A
  ret i32 %value
}

define <2 x i32> @test43vec(i1 %which) {
; CHECK-LABEL: @test43vec(
; CHECK-NEXT:  entry:
; CHECK-NEXT:    br i1 [[WHICH:%.*]], label [[FINAL:%.*]], label [[DELAY:%.*]]
; CHECK:       delay:
; CHECK-NEXT:    br label [[FINAL]]
; CHECK:       final:
; CHECK-NEXT:    [[A:%.*]] = phi <2 x i32> [ <i32 1123, i32 1123>, [[ENTRY:%.*]] ], [ <i32 133, i32 133>, [[DELAY]] ]
; CHECK-NEXT:    ret <2 x i32> [[A]]
;
entry:
  br i1 %which, label %final, label %delay

delay:
  br label %final

final:
  %A = phi <2 x i32> [ <i32 1000, i32 1000>, %entry ], [ <i32 10, i32 10>, %delay ]
  %value = add <2 x i32> <i32 123, i32 123>, %A
  ret <2 x i32> %value
}

define <2 x i32> @test43vec2(i1 %which) {
; CHECK-LABEL: @test43vec2(
; CHECK-NEXT:  entry:
; CHECK-NEXT:    br i1 [[WHICH:%.*]], label [[FINAL:%.*]], label [[DELAY:%.*]]
; CHECK:       delay:
; CHECK-NEXT:    br label [[FINAL]]
; CHECK:       final:
; CHECK-NEXT:    [[A:%.*]] = phi <2 x i32> [ <i32 1123, i32 2833>, [[ENTRY:%.*]] ], [ <i32 133, i32 363>, [[DELAY]] ]
; CHECK-NEXT:    ret <2 x i32> [[A]]
;
entry:
  br i1 %which, label %final, label %delay

delay:
  br label %final

final:
  %A = phi <2 x i32> [ <i32 1000, i32 2500>, %entry ], [ <i32 10, i32 30>, %delay ]
  %value = add <2 x i32> <i32 123, i32 333>, %A
  ret <2 x i32> %value
}
