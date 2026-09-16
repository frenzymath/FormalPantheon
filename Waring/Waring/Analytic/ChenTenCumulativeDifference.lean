import Waring.Analytic.ChenTenSingularIntegralLowerBound

/-!
# Finite differences of Chen's cumulative count

This file estimates the cubic finite difference arising from the double shift
average and relates the resulting cumulative-count difference to
`scratchShiftSquareCount`.
-/

set_option autoImplicit false

namespace Waring.Analytic

open scoped BigOperators

noncomputable section

private theorem cube_step_error
    {n a m : Real} (hm : 0 ≤ m) (ha : m ≤ a) (han : a ≤ n)
    (hshift : n - a ≤ 2 * m) :
    |(a ^ 3 - (a - m) ^ 3) - 3 * n ^ 2 * m| ≤
      20 * n * m ^ 2 := by
  have hn : 0 ≤ n := hm.trans (ha.trans han)
  have ha0 : 0 ≤ a := hm.trans ha
  have hna : 0 ≤ n - a := sub_nonneg.mpr han
  have hsum : a + n ≤ 2 * n := by linarith
  have hsum0 : 0 ≤ a + n := add_nonneg ha0 hn
  have hsquare : n ^ 2 - a ^ 2 ≤ 4 * n * m := by
    have hprod : (n - a) * (a + n) ≤ (2 * m) * (2 * n) := by
      gcongr
    nlinarith
  have hsq0 : 0 ≤ n ^ 2 - a ^ 2 := by nlinarith
  have hfirst : (n ^ 2 - a ^ 2) * m ≤ 4 * n * m ^ 2 := by
    calc
      (n ^ 2 - a ^ 2) * m ≤ (4 * n * m) * m :=
        mul_le_mul_of_nonneg_right hsquare hm
      _ = 4 * n * m ^ 2 := by ring
  have hcubic : m ^ 3 ≤ a * m ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sq_nonneg m)]
  have hid :
      (a ^ 3 - (a - m) ^ 3) - 3 * n ^ 2 * m =
        -(3 * (n ^ 2 - a ^ 2) * m + 3 * a * m ^ 2 - m ^ 3) := by
    ring
  have hnonpos :
      (a ^ 3 - (a - m) ^ 3) - 3 * n ^ 2 * m ≤ 0 := by
    rw [hid]
    have : 0 ≤ 3 * (n ^ 2 - a ^ 2) * m := by positivity
    have hsecond : 0 ≤ 3 * a * m ^ 2 - m ^ 3 := by
      nlinarith [hcubic, mul_nonneg ha0 (sq_nonneg m)]
    linarith
  rw [abs_of_nonpos hnonpos, hid]
  have haBound : a * m ^ 2 ≤ n * m ^ 2 :=
    mul_le_mul_of_nonneg_right han (sq_nonneg m)
  nlinarith

/-- The sum of cubic finite differences over the positive shift range. -/
def scratchCubeDifferenceSum (N M : Nat) : Real :=
  ∑ v ∈ scratchShiftSet M,
    (((N - v - 1 : Nat) : Real) ^ 3 -
      ((N - v - M - 1 : Nat) : Real) ^ 3)

/-- The cubic difference sum is close to `3 * N ^ 2 * M ^ 2`. -/
theorem scratch_cubeDifferenceSum_error
    {N M : Nat} (hM : 0 < M) (hMN : 2 * M + 2 ≤ N) :
    |scratchCubeDifferenceSum N M -
        3 * (N : Real) ^ 2 * (M : Real) ^ 2| ≤
      20 * (N : Real) * (M : Real) ^ 3 := by
  have hpoint : ∀ v ∈ scratchShiftSet M,
      |(((N - v - 1 : Nat) : Real) ^ 3 -
          ((N - v - M - 1 : Nat) : Real) ^ 3) -
        3 * (N : Real) ^ 2 * (M : Real)| ≤
      20 * (N : Real) * (M : Real) ^ 2 := by
    intro v hv
    have hv' := Finset.mem_Icc.mp hv
    have hvM : v ≤ M := hv'.2
    have hsub : M ≤ N - v - 1 := by omega
    have hcastA : ((N - v - 1 : Nat) : Real) =
        (N : Real) - v - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ N - v),
        Nat.cast_sub (by omega : v ≤ N)]
      push_cast
      ring
    have hcastB : ((N - v - M - 1 : Nat) : Real) =
        ((N - v - 1 : Nat) : Real) - M := by
      rw [Nat.cast_sub (by omega : 1 ≤ N - v - M),
        Nat.cast_sub (by omega : M ≤ N - v),
        Nat.cast_sub (by omega : v ≤ N), hcastA]
      push_cast
      ring
    rw [hcastB]
    apply cube_step_error
    · positivity
    · exact_mod_cast hsub
    · rw [hcastA]
      linarith
    · rw [hcastA]
      have hv1 : (v : Real) + 1 ≤ 2 * M := by
        exact_mod_cast (show v + 1 ≤ 2 * M by omega)
      linarith
  have hrewrite :
      scratchCubeDifferenceSum N M -
          3 * (N : Real) ^ 2 * (M : Real) ^ 2 =
        ∑ v ∈ scratchShiftSet M,
          ((((N - v - 1 : Nat) : Real) ^ 3 -
              ((N - v - M - 1 : Nat) : Real) ^ 3) -
            3 * (N : Real) ^ 2 * (M : Real)) := by
    unfold scratchCubeDifferenceSum
    have hconst :
        3 * (N : Real) ^ 2 * (M : Real) ^ 2 =
          ∑ _v ∈ scratchShiftSet M,
            3 * (N : Real) ^ 2 * (M : Real) := by
      simp [scratchShiftSet, Nat.card_Icc]
      ring
    rw [hconst, ← Finset.sum_sub_distrib]
  rw [hrewrite]
  calc
    |∑ v ∈ scratchShiftSet M,
        ((((N - v - 1 : Nat) : Real) ^ 3 -
            ((N - v - M - 1 : Nat) : Real) ^ 3) -
          3 * (N : Real) ^ 2 * (M : Real))| ≤
      ∑ v ∈ scratchShiftSet M,
        |(((N - v - 1 : Nat) : Real) ^ 3 -
            ((N - v - M - 1 : Nat) : Real) ^ 3) -
          3 * (N : Real) ^ 2 * (M : Real)| := by
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v ∈ scratchShiftSet M,
        20 * (N : Real) * (M : Real) ^ 2 := by
      apply Finset.sum_le_sum
      intro v hv
      exact hpoint v hv
    _ = 20 * (N : Real) * (M : Real) ^ 3 := by
      simp [scratchShiftSet, Nat.card_Icc]
      ring

private theorem K15_error_bound_mono
    {X N : Nat} (hXN : X ≤ N)
    (hroot : (15 : Real) ≤ (X : Real) ^ (1 / (5 : Real))) :
    |(K15 X : Real) - chenTenT15 * (X : Real) ^ 3| ≤
      1000 * chenTenT15 * (N : Real) ^ (14 / (5 : Real)) := by
  have hraw := K15_error_bound X hroot
  have hpow : (X : Real) ^ (14 / (5 : Real)) ≤
      (N : Real) ^ (14 / (5 : Real)) := by
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hXN) (by norm_num)
  have hT : 0 ≤ chenTenT15 := by
    dsimp [chenTenT15]
    positivity
  exact hraw.trans (mul_le_mul_of_nonneg_left hpow (by positivity))

/-- The shift-square count differs from its cubic `K15` model by the cumulative error. -/
theorem scratch_shiftSquareCount_sub_cubicSum_le
    {P N M : Nat} (hMN : 2 * M + 2 ≤ N)
    (hNPow : N ≤ (P + 1) ^ 5)
    (hrootA : ∀ v ∈ scratchShiftSet M,
      (15 : Real) ≤ ((N - v - 1 : Nat) : Real) ^ (1 / (5 : Real)))
    (hrootB : ∀ v ∈ scratchShiftSet M,
      (15 : Real) ≤ ((N - v - M - 1 : Nat) : Real) ^ (1 / (5 : Real))) :
    |(scratchShiftSquareCount P N M : Real) -
        chenTenT15 * scratchCubeDifferenceSum N M| ≤
      2000 * chenTenT15 * (N : Real) ^ (14 / (5 : Real)) *
        (M : Real) := by
  rw [scratch_shift_square_count_cast_eq_K15_difference P N M hMN hNPow]
  have hrewrite :
      (∑ v ∈ scratchShiftSet M,
          ((K15 (N - v - 1) : Real) -
            (K15 (N - v - M - 1) : Real))) -
          chenTenT15 * scratchCubeDifferenceSum N M =
        ∑ v ∈ scratchShiftSet M,
          (((K15 (N - v - 1) : Real) -
              chenTenT15 * ((N - v - 1 : Nat) : Real) ^ 3) -
            ((K15 (N - v - M - 1) : Real) -
              chenTenT15 * ((N - v - M - 1 : Nat) : Real) ^ 3)) := by
    unfold scratchCubeDifferenceSum
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    ring
  rw [hrewrite]
  calc
    |∑ v ∈ scratchShiftSet M,
        (((K15 (N - v - 1) : Real) -
            chenTenT15 * ((N - v - 1 : Nat) : Real) ^ 3) -
          ((K15 (N - v - M - 1) : Real) -
            chenTenT15 * ((N - v - M - 1 : Nat) : Real) ^ 3))| ≤
      ∑ v ∈ scratchShiftSet M,
        |((K15 (N - v - 1) : Real) -
            chenTenT15 * ((N - v - 1 : Nat) : Real) ^ 3) -
          ((K15 (N - v - M - 1) : Real) -
            chenTenT15 * ((N - v - M - 1 : Nat) : Real) ^ 3)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v ∈ scratchShiftSet M,
        2000 * chenTenT15 * (N : Real) ^ (14 / (5 : Real)) := by
      apply Finset.sum_le_sum
      intro v hv
      have hA := K15_error_bound_mono
        (show N - v - 1 ≤ N by omega) (hrootA v hv)
      have hB := K15_error_bound_mono
        (show N - v - M - 1 ≤ N by omega) (hrootB v hv)
      calc
        |((K15 (N - v - 1) : Real) -
              chenTenT15 * ((N - v - 1 : Nat) : Real) ^ 3) -
            ((K15 (N - v - M - 1) : Real) -
              chenTenT15 * ((N - v - M - 1 : Nat) : Real) ^ 3)| ≤
          |(K15 (N - v - 1) : Real) -
              chenTenT15 * ((N - v - 1 : Nat) : Real) ^ 3| +
            |(K15 (N - v - M - 1) : Real) -
              chenTenT15 * ((N - v - M - 1 : Nat) : Real) ^ 3| :=
          abs_sub _ _
        _ ≤ 1000 * chenTenT15 * (N : Real) ^ (14 / (5 : Real)) +
            1000 * chenTenT15 * (N : Real) ^ (14 / (5 : Real)) :=
          add_le_add hA hB
        _ = 2000 * chenTenT15 * (N : Real) ^ (14 / (5 : Real)) := by ring
    _ = 2000 * chenTenT15 * (N : Real) ^ (14 / (5 : Real)) *
        (M : Real) := by
      simp [scratchShiftSet, Nat.card_Icc]
      ring

/-- Scale hypotheses turn the cumulative and cubic errors into the common Chen error bound. -/
theorem scratch_shiftSquareCount_cumulative_error
    {P N M : Nat} (hM : 0 < M) (hMN : 2 * M + 2 ≤ N)
    (hNPow : N ≤ (P + 1) ^ 5)
    (hrootA : ∀ v ∈ scratchShiftSet M,
      (15 : Real) ≤ ((N - v - 1 : Nat) : Real) ^ (1 / (5 : Real)))
    (hrootB : ∀ v ∈ scratchShiftSet M,
      (15 : Real) ≤ ((N - v - M - 1 : Nat) : Real) ^ (1 / (5 : Real)))
    (hKscale :
      (N : Real) ^ (14 / (5 : Real)) * (M : Real) ≤
        (N : Real) ^ 2 * (M : Real) ^ 2 *
          (P : Real) ^ (-1 / 5 : Real))
    (hCubeScale :
      (N : Real) * (M : Real) ^ 3 ≤
        (N : Real) ^ 2 * (M : Real) ^ 2 *
          (P : Real) ^ (-1 / 5 : Real)) :
    |(scratchShiftSquareCount P N M : Real) -
        (3 * chenTenT15 * (N : Real) ^ 2) * (M : Real) ^ 2| ≤
      (3000 * chenTenT15 * (N : Real) ^ 2 *
        (P : Real) ^ (-1 / 5 : Real)) * (M : Real) ^ 2 := by
  have hK := scratch_shiftSquareCount_sub_cubicSum_le hMN hNPow hrootA hrootB
  have hCube := scratch_cubeDifferenceSum_error hM hMN
  have hT : 0 ≤ chenTenT15 := by
    dsimp [chenTenT15]
    positivity
  have hsplit :
      (scratchShiftSquareCount P N M : Real) -
          (3 * chenTenT15 * (N : Real) ^ 2) * (M : Real) ^ 2 =
        ((scratchShiftSquareCount P N M : Real) -
          chenTenT15 * scratchCubeDifferenceSum N M) +
        chenTenT15 * (scratchCubeDifferenceSum N M -
          3 * (N : Real) ^ 2 * (M : Real) ^ 2) := by ring
  rw [hsplit]
  calc
    |((scratchShiftSquareCount P N M : Real) -
          chenTenT15 * scratchCubeDifferenceSum N M) +
        chenTenT15 * (scratchCubeDifferenceSum N M -
          3 * (N : Real) ^ 2 * (M : Real) ^ 2)| ≤
      |(scratchShiftSquareCount P N M : Real) -
          chenTenT15 * scratchCubeDifferenceSum N M| +
        chenTenT15 * |scratchCubeDifferenceSum N M -
          3 * (N : Real) ^ 2 * (M : Real) ^ 2| := by
      calc
        |((scratchShiftSquareCount P N M : Real) -
              chenTenT15 * scratchCubeDifferenceSum N M) +
            chenTenT15 * (scratchCubeDifferenceSum N M -
              3 * (N : Real) ^ 2 * (M : Real) ^ 2)| ≤
          |(scratchShiftSquareCount P N M : Real) -
              chenTenT15 * scratchCubeDifferenceSum N M| +
            |chenTenT15 *
            (scratchCubeDifferenceSum N M -
              3 * (N : Real) ^ 2 * (M : Real) ^ 2)| := abs_add_le _ _
        _ = _ := by rw [abs_mul, abs_of_nonneg hT]
    _ ≤ 2000 * chenTenT15 * (N : Real) ^ (14 / (5 : Real)) *
          (M : Real) +
        chenTenT15 * (20 * (N : Real) * (M : Real) ^ 3) := by
      exact add_le_add hK (mul_le_mul_of_nonneg_left hCube hT)
    _ ≤ 2000 * chenTenT15 *
          ((N : Real) ^ 2 * (M : Real) ^ 2 *
            (P : Real) ^ (-1 / 5 : Real)) +
        20 * chenTenT15 *
          ((N : Real) ^ 2 * (M : Real) ^ 2 *
            (P : Real) ^ (-1 / 5 : Real)) := by
      have hK' := mul_le_mul_of_nonneg_left hKscale (by positivity :
        0 ≤ 2000 * chenTenT15)
      have hC' := mul_le_mul_of_nonneg_left hCubeScale (by positivity :
        0 ≤ 20 * chenTenT15)
      nlinarith
    _ ≤ (3000 * chenTenT15 * (N : Real) ^ 2 *
        (P : Real) ^ (-1 / 5 : Real)) * (M : Real) ^ 2 := by
      have hscale : 0 ≤ (N : Real) ^ 2 * (M : Real) ^ 2 *
          (P : Real) ^ (-1 / 5 : Real) := by positivity
      nlinarith

end

end Waring.Analytic
