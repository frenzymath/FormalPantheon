import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The reciprocal norm on a Perron vertical line

The vertical integral in the proof of `MAYNARD-PRD-PUBLISHED`, Proposition
9.3, has height `X ^ 4`.  Its reciprocal denominator must therefore be
integrated with logarithmic cost rather than bounded by the interval length.
-/

open Complex MeasureTheory Set
open scoped Interval

namespace PrimesRestrictedDigits

private lemma verticalLine_ne_zero {sigma t : Real} (hsigma : 0 < sigma) :
    (sigma : Complex) + Complex.I * t ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp at hre
  exact hsigma.ne' hre

private lemma verticalNormIntegrand_continuous {sigma : Real} (hsigma : 0 < sigma) :
    Continuous (fun t : Real =>
      1 / norm ((sigma : Complex) + Complex.I * t)) := by
  apply continuous_const.div₀
  · fun_prop
  · intro t
    exact norm_ne_zero_iff.mpr (verticalLine_ne_zero hsigma)

private lemma verticalNormIntegrand_le_real {sigma t : Real} (hsigma : 0 < sigma) :
    1 / norm ((sigma : Complex) + Complex.I * t) ≤ 1 / sigma := by
  apply one_div_le_one_div_of_le hsigma
  simpa [abs_of_pos hsigma] using
    Complex.abs_re_le_norm ((sigma : Complex) + Complex.I * t)

private lemma verticalNormIntegrand_le_im_of_pos {sigma t : Real} (ht : 0 < t) :
    1 / norm ((sigma : Complex) + Complex.I * t) ≤ 1 / t := by
  apply one_div_le_one_div_of_le ht
  simpa [abs_of_pos ht] using
    Complex.abs_im_le_norm ((sigma : Complex) + Complex.I * t)

/-- The reciprocal of a positive vertical line has only logarithmic `L1` cost. -/
theorem integral_norm_inv_vertical_le_two_div_add_two_log
    {sigma T : Real} (hsigma : 0 < sigma) (hT : 1 ≤ T) :
    (∫ t in -T..T,
      1 / norm ((sigma : Complex) + Complex.I * t)) ≤
      2 / sigma + 2 * Real.log T := by
  let f : Real → Real := fun t =>
    1 / norm ((sigma : Complex) + Complex.I * t)
  have hf : Continuous f := verticalNormIntegrand_continuous hsigma
  have hnegOne_le_one : (-1 : Real) ≤ 1 := by norm_num
  have hleftInt : IntervalIntegrable f volume (-T) (-1) :=
    hf.intervalIntegrable _ _
  have hmidInt : IntervalIntegrable f volume (-1) 1 :=
    hf.intervalIntegrable _ _
  have hrightInt : IntervalIntegrable f volume 1 T :=
    hf.intervalIntegrable _ _
  have hmid : (∫ t in (-1 : Real)..1, f t) ≤ 2 / sigma := by
    have hconst : IntervalIntegrable (fun _ : Real => 1 / sigma) volume (-1) 1 :=
      intervalIntegrable_const
    calc
      (∫ t in (-1 : Real)..1, f t) ≤
          ∫ _t in (-1 : Real)..1, 1 / sigma := by
        exact intervalIntegral.integral_mono_on hnegOne_le_one hmidInt hconst
          (fun t _ => verticalNormIntegrand_le_real hsigma)
      _ = 2 / sigma := by
        rw [intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring
  have hright : (∫ t in (1 : Real)..T, f t) ≤ Real.log T := by
    have hinv : IntervalIntegrable (fun t : Real => 1 / t) volume 1 T := by
      exact (continuousOn_const.div continuousOn_id (fun t ht => by
        exact ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1))).intervalIntegrable_of_Icc hT
    calc
      (∫ t in (1 : Real)..T, f t) ≤
          ∫ t in (1 : Real)..T, 1 / t := by
        exact intervalIntegral.integral_mono_on hT hrightInt hinv
          (fun t ht => verticalNormIntegrand_le_im_of_pos
            (lt_of_lt_of_le zero_lt_one ht.1))
      _ = Real.log T := by
        rw [integral_one_div_of_pos zero_lt_one (lt_of_lt_of_le zero_lt_one hT)]
        simp
  have heven (t : Real) : f (-t) = f t := by
    simp only [f]
    apply congrArg (fun x : Real => 1 / x)
    rw [← Complex.norm_conj]
    apply congrArg norm
    apply Complex.ext <;> simp
  have hleftEq : (∫ t in -T..(-1 : Real), f t) = ∫ t in (1 : Real)..T, f t := by
    rw [← intervalIntegral.integral_comp_neg (a := 1) (b := T) f]
    apply intervalIntegral.integral_congr
    intro t ht
    exact heven t
  have hleft : (∫ t in -T..(-1 : Real), f t) ≤ Real.log T := by
    rw [hleftEq]
    exact hright
  have hsplitLeft :=
    intervalIntegral.integral_add_adjacent_intervals hleftInt hmidInt
  have hsplitAll :=
    intervalIntegral.integral_add_adjacent_intervals (hleftInt.trans hmidInt) hrightInt
  change (∫ t in -T..T, f t) ≤ _
  rw [← hsplitAll, ← hsplitLeft]
  linarith

/-- On the Perron line used at scale `X`, the reciprocal denominator costs at
most one explicit logarithm. -/
theorem integral_norm_inv_logLine_le {X : Nat} (hX : 4 ≤ X) :
    (∫ t in -((X : Real) ^ 4)..((X : Real) ^ 4),
      1 / norm ((((Real.log (X : Real))⁻¹ : Real) : Complex) +
        Complex.I * t)) ≤
      10 * Real.log (X : Real) := by
  have hXOne : (1 : Real) ≤ X := by
    exact_mod_cast (show 1 ≤ X by omega)
  have hXOneStrict : (1 : Real) < X := by
    exact_mod_cast (show 1 < X by omega)
  have hlogPos : 0 < Real.log (X : Real) := Real.log_pos hXOneStrict
  have hline := integral_norm_inv_vertical_le_two_div_add_two_log
    (sigma := (Real.log (X : Real))⁻¹) (T := (X : Real) ^ 4)
    (inv_pos.mpr hlogPos) (one_le_pow₀ hXOne)
  calc
    (∫ t in -((X : Real) ^ 4)..((X : Real) ^ 4),
      1 / norm ((((Real.log (X : Real))⁻¹ : Real) : Complex) +
        Complex.I * t)) ≤
        2 / (Real.log (X : Real))⁻¹ +
          2 * Real.log ((X : Real) ^ 4) := hline
    _ = 10 * Real.log (X : Real) := by
      rw [Real.log_pow]
      field_simp [hlogPos.ne']
      ring

end PrimesRestrictedDigits
