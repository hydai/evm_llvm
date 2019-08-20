; NOTE: Assertions have been autogenerated by utils/update_test_checks.py
; RUN: opt < %s -instcombine -S | FileCheck %s

; This tests the InstructionCombining optimization that reduces things like:
;   %Y = sext i8 %X to i32
;   %C = icmp ult i32 %Y, 1024
; to
;   %C = i1 true
; It includes test cases for different constant values, signedness of the
; cast operands, and types of setCC operators. In all cases, the cast should
; be eliminated. In many cases the setCC is also eliminated based on the
; constant value and the range of the casted value.
;

define i1 @lt_signed_to_large_unsigned(i8 %SB) {
; CHECK-LABEL: @lt_signed_to_large_unsigned(
; CHECK-NEXT:    [[C:%.*]] = icmp sgt i8 [[SB:%.*]], -1
; CHECK-NEXT:    ret i1 [[C]]
;
  %Y = sext i8 %SB to i32
  %C = icmp ult i32 %Y, 1024
  ret i1 %C
}

; PR28011 - https://llvm.org/bugs/show_bug.cgi?id=28011
; The above transform only applies to scalar integers; it shouldn't be attempted for constant expressions or vectors.

@a = common global i32** null
@b = common global [1 x i32] zeroinitializer

define i1 @PR28011(i16 %a) {
; CHECK-LABEL: @PR28011(
; CHECK-NEXT:    [[CONV:%.*]] = sext i16 [[A:%.*]] to i32
; CHECK-NEXT:    [[CMP:%.*]] = icmp ne i32 [[CONV]], or (i32 zext (i1 icmp ne (i32*** bitcast ([1 x i32]* @b to i32***), i32*** @a) to i32), i32 1)
; CHECK-NEXT:    ret i1 [[CMP]]
;
  %conv = sext i16 %a to i32
  %cmp = icmp ne i32 %conv, or (i32 zext (i1 icmp ne (i32*** bitcast ([1 x i32]* @b to i32***), i32*** @a) to i32), i32 1)
  ret i1 %cmp
}

define <2 x i1> @lt_signed_to_large_unsigned_vec(<2 x i8> %SB) {
; CHECK-LABEL: @lt_signed_to_large_unsigned_vec(
; CHECK-NEXT:    [[Y:%.*]] = sext <2 x i8> [[SB:%.*]] to <2 x i32>
; CHECK-NEXT:    [[C:%.*]] = icmp ult <2 x i32> [[Y]], <i32 1024, i32 2>
; CHECK-NEXT:    ret <2 x i1> [[C]]
;
  %Y = sext <2 x i8> %SB to <2 x i32>
  %C = icmp ult <2 x i32> %Y, <i32 1024, i32 2>
  ret <2 x i1> %C
}

define i1 @lt_signed_to_large_signed(i8 %SB) {
; CHECK-LABEL: @lt_signed_to_large_signed(
; CHECK-NEXT:    ret i1 true
;
  %Y = sext i8 %SB to i32
  %C = icmp slt i32 %Y, 1024
  ret i1 %C
}

define i1 @lt_signed_to_large_negative(i8 %SB) {
; CHECK-LABEL: @lt_signed_to_large_negative(
; CHECK-NEXT:    ret i1 false
;
  %Y = sext i8 %SB to i32
  %C = icmp slt i32 %Y, -1024
  ret i1 %C
}

define i1 @lt_signed_to_small_unsigned(i8 %SB) {
; CHECK-LABEL: @lt_signed_to_small_unsigned(
; CHECK-NEXT:    [[C:%.*]] = icmp ult i8 [[SB:%.*]], 17
; CHECK-NEXT:    ret i1 [[C]]
;
  %Y = sext i8 %SB to i32
  %C = icmp ult i32 %Y, 17
  ret i1 %C
}

define i1 @lt_signed_to_small_signed(i8 %SB) {
; CHECK-LABEL: @lt_signed_to_small_signed(
; CHECK-NEXT:    [[C:%.*]] = icmp slt i8 [[SB:%.*]], 17
; CHECK-NEXT:    ret i1 [[C]]
;
  %Y = sext i8 %SB to i32
  %C = icmp slt i32 %Y, 17
  ret i1 %C
}
define i1 @lt_signed_to_small_negative(i8 %SB) {
; CHECK-LABEL: @lt_signed_to_small_negative(
; CHECK-NEXT:    [[C:%.*]] = icmp slt i8 [[SB:%.*]], -17
; CHECK-NEXT:    ret i1 [[C]]
;
  %Y = sext i8 %SB to i32
  %C = icmp slt i32 %Y, -17
  ret i1 %C
}

define i1 @lt_unsigned_to_large_unsigned(i8 %SB) {
; CHECK-LABEL: @lt_unsigned_to_large_unsigned(
; CHECK-NEXT:    ret i1 true
;
  %Y = zext i8 %SB to i32
  %C = icmp ult i32 %Y, 1024
  ret i1 %C
}

define i1 @lt_unsigned_to_large_signed(i8 %SB) {
; CHECK-LABEL: @lt_unsigned_to_large_signed(
; CHECK-NEXT:    ret i1 true
;
  %Y = zext i8 %SB to i32
  %C = icmp slt i32 %Y, 1024
  ret i1 %C
}

define i1 @lt_unsigned_to_large_negative(i8 %SB) {
; CHECK-LABEL: @lt_unsigned_to_large_negative(
; CHECK-NEXT:    ret i1 false
;
  %Y = zext i8 %SB to i32
  %C = icmp slt i32 %Y, -1024
  ret i1 %C
}

define i1 @lt_unsigned_to_small_unsigned(i8 %SB) {
; CHECK-LABEL: @lt_unsigned_to_small_unsigned(
; CHECK-NEXT:    [[C:%.*]] = icmp ult i8 [[SB:%.*]], 17
; CHECK-NEXT:    ret i1 [[C]]
;
  %Y = zext i8 %SB to i32
  %C = icmp ult i32 %Y, 17
  ret i1 %C
}

define i1 @lt_unsigned_to_small_signed(i8 %SB) {
; CHECK-LABEL: @lt_unsigned_to_small_signed(
; CHECK-NEXT:    [[C:%.*]] = icmp ult i8 [[SB:%.*]], 17
; CHECK-NEXT:    ret i1 [[C]]
;
  %Y = zext i8 %SB to i32
  %C = icmp slt i32 %Y, 17
  ret i1 %C
}

define i1 @lt_unsigned_to_small_negative(i8 %SB) {
; CHECK-LABEL: @lt_unsigned_to_small_negative(
; CHECK-NEXT:    ret i1 false
;
  %Y = zext i8 %SB to i32
  %C = icmp slt i32 %Y, -17
  ret i1 %C
}

define i1 @gt_signed_to_large_unsigned(i8 %SB) {
; CHECK-LABEL: @gt_signed_to_large_unsigned(
; CHECK-NEXT:    [[C:%.*]] = icmp slt i8 [[SB:%.*]], 0
; CHECK-NEXT:    ret i1 [[C]]
;
  %Y = sext i8 %SB to i32
  %C = icmp ugt i32 %Y, 1024
  ret i1 %C
}

define i1 @gt_signed_to_large_signed(i8 %SB) {
; CHECK-LABEL: @gt_signed_to_large_signed(
; CHECK-NEXT:    ret i1 false
;
  %Y = sext i8 %SB to i32
  %C = icmp sgt i32 %Y, 1024
  ret i1 %C
}

define i1 @gt_signed_to_large_negative(i8 %SB) {
; CHECK-LABEL: @gt_signed_to_large_negative(
; CHECK-NEXT:    ret i1 true
;
  %Y = sext i8 %SB to i32
  %C = icmp sgt i32 %Y, -1024
  ret i1 %C
}

define i1 @gt_signed_to_small_unsigned(i8 %SB) {
; CHECK-LABEL: @gt_signed_to_small_unsigned(
; CHECK-NEXT:    [[C:%.*]] = icmp ugt i8 [[SB:%.*]], 17
; CHECK-NEXT:    ret i1 [[C]]
;
  %Y = sext i8 %SB to i32
  %C = icmp ugt i32 %Y, 17
  ret i1 %C
}

define i1 @gt_signed_to_small_signed(i8 %SB) {
; CHECK-LABEL: @gt_signed_to_small_signed(
; CHECK-NEXT:    [[C:%.*]] = icmp sgt i8 [[SB:%.*]], 17
; CHECK-NEXT:    ret i1 [[C]]
;
  %Y = sext i8 %SB to i32
  %C = icmp sgt i32 %Y, 17
  ret i1 %C
}

define i1 @gt_signed_to_small_negative(i8 %SB) {
; CHECK-LABEL: @gt_signed_to_small_negative(
; CHECK-NEXT:    [[C:%.*]] = icmp sgt i8 [[SB:%.*]], -17
; CHECK-NEXT:    ret i1 [[C]]
;
  %Y = sext i8 %SB to i32
  %C = icmp sgt i32 %Y, -17
  ret i1 %C
}

define i1 @gt_unsigned_to_large_unsigned(i8 %SB) {
; CHECK-LABEL: @gt_unsigned_to_large_unsigned(
; CHECK-NEXT:    ret i1 false
;
  %Y = zext i8 %SB to i32
  %C = icmp ugt i32 %Y, 1024
  ret i1 %C
}

define i1 @gt_unsigned_to_large_signed(i8 %SB) {
; CHECK-LABEL: @gt_unsigned_to_large_signed(
; CHECK-NEXT:    ret i1 false
;
  %Y = zext i8 %SB to i32
  %C = icmp sgt i32 %Y, 1024
  ret i1 %C
}

define i1 @gt_unsigned_to_large_negative(i8 %SB) {
; CHECK-LABEL: @gt_unsigned_to_large_negative(
; CHECK-NEXT:    ret i1 true
;
  %Y = zext i8 %SB to i32
  %C = icmp sgt i32 %Y, -1024
  ret i1 %C
}

define i1 @gt_unsigned_to_small_unsigned(i8 %SB) {
; CHECK-LABEL: @gt_unsigned_to_small_unsigned(
; CHECK-NEXT:    [[C:%.*]] = icmp ugt i8 [[SB:%.*]], 17
; CHECK-NEXT:    ret i1 [[C]]
;
  %Y = zext i8 %SB to i32
  %C = icmp ugt i32 %Y, 17
  ret i1 %C
}

define i1 @gt_unsigned_to_small_signed(i8 %SB) {
; CHECK-LABEL: @gt_unsigned_to_small_signed(
; CHECK-NEXT:    [[C:%.*]] = icmp ugt i8 [[SB:%.*]], 17
; CHECK-NEXT:    ret i1 [[C]]
;
  %Y = zext i8 %SB to i32
  %C = icmp sgt i32 %Y, 17
  ret i1 %C
}

define i1 @gt_unsigned_to_small_negative(i8 %SB) {
; CHECK-LABEL: @gt_unsigned_to_small_negative(
; CHECK-NEXT:    ret i1 true
;
  %Y = zext i8 %SB to i32
  %C = icmp sgt i32 %Y, -17
  ret i1 %C
}

define i1 @different_size_zext_zext_ugt(i7 %x, i4 %y) {
; CHECK-LABEL: @different_size_zext_zext_ugt(
; CHECK-NEXT:    [[ZX:%.*]] = zext i7 [[X:%.*]] to i25
; CHECK-NEXT:    [[ZY:%.*]] = zext i4 [[Y:%.*]] to i25
; CHECK-NEXT:    [[R:%.*]] = icmp ugt i25 [[ZX]], [[ZY]]
; CHECK-NEXT:    ret i1 [[R]]
;
  %zx = zext i7 %x to i25
  %zy = zext i4 %y to i25
  %r = icmp ugt i25 %zx, %zy
  ret i1 %r
}

define <2 x i1> @different_size_zext_zext_ugt_commute(<2 x i4> %x, <2 x i7> %y) {
; CHECK-LABEL: @different_size_zext_zext_ugt_commute(
; CHECK-NEXT:    [[ZX:%.*]] = zext <2 x i4> [[X:%.*]] to <2 x i25>
; CHECK-NEXT:    [[ZY:%.*]] = zext <2 x i7> [[Y:%.*]] to <2 x i25>
; CHECK-NEXT:    [[R:%.*]] = icmp ugt <2 x i25> [[ZX]], [[ZY]]
; CHECK-NEXT:    ret <2 x i1> [[R]]
;
  %zx = zext <2 x i4> %x to <2 x i25>
  %zy = zext <2 x i7> %y to <2 x i25>
  %r = icmp ugt <2 x i25> %zx, %zy
  ret <2 x i1> %r
}

define i1 @different_size_zext_zext_ult(i4 %x, i7 %y) {
; CHECK-LABEL: @different_size_zext_zext_ult(
; CHECK-NEXT:    [[ZX:%.*]] = zext i4 [[X:%.*]] to i25
; CHECK-NEXT:    [[ZY:%.*]] = zext i7 [[Y:%.*]] to i25
; CHECK-NEXT:    [[R:%.*]] = icmp ult i25 [[ZX]], [[ZY]]
; CHECK-NEXT:    ret i1 [[R]]
;
  %zx = zext i4 %x to i25
  %zy = zext i7 %y to i25
  %r = icmp ult i25 %zx, %zy
  ret i1 %r
}

define i1 @different_size_zext_zext_eq(i4 %x, i7 %y) {
; CHECK-LABEL: @different_size_zext_zext_eq(
; CHECK-NEXT:    [[ZX:%.*]] = zext i4 [[X:%.*]] to i25
; CHECK-NEXT:    [[ZY:%.*]] = zext i7 [[Y:%.*]] to i25
; CHECK-NEXT:    [[R:%.*]] = icmp eq i25 [[ZX]], [[ZY]]
; CHECK-NEXT:    ret i1 [[R]]
;
  %zx = zext i4 %x to i25
  %zy = zext i7 %y to i25
  %r = icmp eq i25 %zx, %zy
  ret i1 %r
}

define i1 @different_size_zext_zext_ne_commute(i7 %x, i4 %y) {
; CHECK-LABEL: @different_size_zext_zext_ne_commute(
; CHECK-NEXT:    [[ZX:%.*]] = zext i7 [[X:%.*]] to i25
; CHECK-NEXT:    [[ZY:%.*]] = zext i4 [[Y:%.*]] to i25
; CHECK-NEXT:    [[R:%.*]] = icmp ne i25 [[ZX]], [[ZY]]
; CHECK-NEXT:    ret i1 [[R]]
;
  %zx = zext i7 %x to i25
  %zy = zext i4 %y to i25
  %r = icmp ne i25 %zx, %zy
  ret i1 %r
}

define i1 @different_size_zext_zext_slt(i7 %x, i4 %y) {
; CHECK-LABEL: @different_size_zext_zext_slt(
; CHECK-NEXT:    [[ZX:%.*]] = zext i7 [[X:%.*]] to i25
; CHECK-NEXT:    [[ZY:%.*]] = zext i4 [[Y:%.*]] to i25
; CHECK-NEXT:    [[R:%.*]] = icmp ult i25 [[ZX]], [[ZY]]
; CHECK-NEXT:    ret i1 [[R]]
;
  %zx = zext i7 %x to i25
  %zy = zext i4 %y to i25
  %r = icmp slt i25 %zx, %zy
  ret i1 %r
}

define i1 @different_size_zext_zext_sgt(i7 %x, i4 %y) {
; CHECK-LABEL: @different_size_zext_zext_sgt(
; CHECK-NEXT:    [[ZX:%.*]] = zext i7 [[X:%.*]] to i25
; CHECK-NEXT:    [[ZY:%.*]] = zext i4 [[Y:%.*]] to i25
; CHECK-NEXT:    [[R:%.*]] = icmp ugt i25 [[ZX]], [[ZY]]
; CHECK-NEXT:    ret i1 [[R]]
;
  %zx = zext i7 %x to i25
  %zy = zext i4 %y to i25
  %r = icmp sgt i25 %zx, %zy
  ret i1 %r
}

define i1 @different_size_sext_sext_sgt(i7 %x, i4 %y) {
; CHECK-LABEL: @different_size_sext_sext_sgt(
; CHECK-NEXT:    [[SX:%.*]] = sext i7 [[X:%.*]] to i25
; CHECK-NEXT:    [[SY:%.*]] = sext i4 [[Y:%.*]] to i25
; CHECK-NEXT:    [[R:%.*]] = icmp sgt i25 [[SX]], [[SY]]
; CHECK-NEXT:    ret i1 [[R]]
;
  %sx = sext i7 %x to i25
  %sy = sext i4 %y to i25
  %r = icmp sgt i25 %sx, %sy
  ret i1 %r
}

define i1 @different_size_sext_sext_sle(i7 %x, i4 %y) {
; CHECK-LABEL: @different_size_sext_sext_sle(
; CHECK-NEXT:    [[SX:%.*]] = sext i7 [[X:%.*]] to i25
; CHECK-NEXT:    [[SY:%.*]] = sext i4 [[Y:%.*]] to i25
; CHECK-NEXT:    [[R:%.*]] = icmp sle i25 [[SX]], [[SY]]
; CHECK-NEXT:    ret i1 [[R]]
;
  %sx = sext i7 %x to i25
  %sy = sext i4 %y to i25
  %r = icmp sle i25 %sx, %sy
  ret i1 %r
}

define i1 @different_size_sext_sext_eq(i7 %x, i4 %y) {
; CHECK-LABEL: @different_size_sext_sext_eq(
; CHECK-NEXT:    [[SX:%.*]] = sext i7 [[X:%.*]] to i25
; CHECK-NEXT:    [[SY:%.*]] = sext i4 [[Y:%.*]] to i25
; CHECK-NEXT:    [[R:%.*]] = icmp eq i25 [[SX]], [[SY]]
; CHECK-NEXT:    ret i1 [[R]]
;
  %sx = sext i7 %x to i25
  %sy = sext i4 %y to i25
  %r = icmp eq i25 %sx, %sy
  ret i1 %r
}

define i1 @different_size_sext_sext_ule(i7 %x, i4 %y) {
; CHECK-LABEL: @different_size_sext_sext_ule(
; CHECK-NEXT:    [[SX:%.*]] = sext i7 [[X:%.*]] to i25
; CHECK-NEXT:    [[SY:%.*]] = sext i4 [[Y:%.*]] to i25
; CHECK-NEXT:    [[R:%.*]] = icmp ule i25 [[SX]], [[SY]]
; CHECK-NEXT:    ret i1 [[R]]
;
  %sx = sext i7 %x to i25
  %sy = sext i4 %y to i25
  %r = icmp ule i25 %sx, %sy
  ret i1 %r
}

define i1 @different_size_sext_zext_ne(i7 %x, i4 %y) {
; CHECK-LABEL: @different_size_sext_zext_ne(
; CHECK-NEXT:    [[SX:%.*]] = sext i7 [[X:%.*]] to i25
; CHECK-NEXT:    [[ZY:%.*]] = zext i4 [[Y:%.*]] to i25
; CHECK-NEXT:    [[R:%.*]] = icmp ne i25 [[SX]], [[ZY]]
; CHECK-NEXT:    ret i1 [[R]]
;
  %sx = sext i7 %x to i25
  %zy = zext i4 %y to i25
  %r = icmp ne i25 %sx, %zy
  ret i1 %r
}

declare void @use(i25)

define i1 @different_size_sext_sext_ule_extra_use(i7 %x, i4 %y) {
; CHECK-LABEL: @different_size_sext_sext_ule_extra_use(
; CHECK-NEXT:    [[SX:%.*]] = sext i7 [[X:%.*]] to i25
; CHECK-NEXT:    [[SY:%.*]] = sext i4 [[Y:%.*]] to i25
; CHECK-NEXT:    call void @use(i25 [[SY]])
; CHECK-NEXT:    [[R:%.*]] = icmp ule i25 [[SX]], [[SY]]
; CHECK-NEXT:    ret i1 [[R]]
;
  %sx = sext i7 %x to i25
  %sy = sext i4 %y to i25
  call void @use(i25 %sy)
  %r = icmp ule i25 %sx, %sy
  ret i1 %r
}
