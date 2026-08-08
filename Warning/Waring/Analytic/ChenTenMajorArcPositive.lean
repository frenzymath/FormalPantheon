import Waring.Analytic.ChenTenMajorArcSingularBridge
import Waring.Analytic.ChenTenGlobalProduct
import Waring.Analytic.ChenTenSingularIntegralLowerBound
import Waring.Analytic.ChenTenSingularIntegralLowerSource

/-!
# Positivity of Chen's major-arc contribution

This file combines the major-arc approximation, singular-series product, and
singular-integral lower bounds. Explicit numerical absorption yields the
positive lower bound used by the large-number representation theorem.
-/

set_option autoImplicit false

namespace Waring.Analytic

open Set MeasureTheory
open scoped BigOperators

noncomputable section

private theorem ten_pow_fifty_le_rpow_half
    {P : Nat} (hPbig : (10 : Nat) ^ 100 ≤ P) :
    (10 : Real) ^ 50 ≤ (P : Real) ^ (1 / 2 : Real) := by
  have hPcast : (10 : Real) ^ 100 ≤ (P : Real) := by
    exact_mod_cast hPbig
  have hpow := Real.rpow_le_rpow (by positivity) hPcast
    (by norm_num : (0 : Real) ≤ 1 / 2)
  calc
    (10 : Real) ^ 50 = ((10 : Real) ^ 100) ^ (1 / 2 : Real) := by
      calc
        (10 : Real) ^ 50 = (10 : Real) ^ (50 : Real) :=
          (Real.rpow_natCast 10 50).symm
        _ = (10 : Real) ^ ((100 : Real) * (1 / 2 : Real)) := by norm_num
        _ = ((10 : Real) ^ (100 : Real)) ^ (1 / 2 : Real) := by
          rw [Real.rpow_mul (by positivity)]
        _ = ((10 : Real) ^ 100) ^ (1 / 2 : Real) := by
          congr 1
          exact Real.rpow_natCast 10 100
    _ ≤ (P : Real) ^ (1 / 2 : Real) := hpow

private theorem chenTen_series_tail_factor_le
    {P : Nat} (hPbig : (10 : Nat) ^ 100 ≤ P) :
    (10 : Real) ^ 30 * (P : Real) ^ (-1 / 2 : Real) ≤ 1 / 100000 := by
  have hP : 0 < P := lt_of_lt_of_le (by norm_num) hPbig
  have hPR : (0 : Real) < P := by exact_mod_cast hP
  have hroot := ten_pow_fifty_le_rpow_half hPbig
  have hinv :
      ((P : Real) ^ (1 / 2 : Real))⁻¹ ≤ ((10 : Real) ^ 50)⁻¹ :=
    (inv_le_inv₀ (by positivity) (by positivity)).2 hroot
  calc
    (10 : Real) ^ 30 * (P : Real) ^ (-1 / 2 : Real) =
        (10 : Real) ^ 30 * ((P : Real) ^ (1 / 2 : Real))⁻¹ := by
      rw [← Real.rpow_neg hPR.le]
      congr 2
      ring
    _ ≤ (10 : Real) ^ 30 * ((10 : Real) ^ 50)⁻¹ := by gcongr
    _ ≤ 1 / 100000 := by norm_num

private theorem ten_pow_seventy_le_rpow_seven_tenths
    {P : Nat} (hPbig : (10 : Nat) ^ 100 ≤ P) :
    (10 : Real) ^ 70 ≤ (P : Real) ^ (7 / 10 : Real) := by
  have hPcast : (10 : Real) ^ 100 ≤ (P : Real) := by
    exact_mod_cast hPbig
  have hpow := Real.rpow_le_rpow (by positivity) hPcast
    (by norm_num : (0 : Real) ≤ 7 / 10)
  calc
    (10 : Real) ^ 70 = ((10 : Real) ^ 100) ^ (7 / 10 : Real) := by
      calc
        (10 : Real) ^ 70 = (10 : Real) ^ (70 : Real) :=
          (Real.rpow_natCast 10 70).symm
        _ = (10 : Real) ^ ((100 : Real) * (7 / 10 : Real)) := by norm_num
        _ = ((10 : Real) ^ (100 : Real)) ^ (7 / 10 : Real) := by
          rw [Real.rpow_mul (by positivity)]
        _ = ((10 : Real) ^ 100) ^ (7 / 10 : Real) := by
          congr 1
          exact Real.rpow_natCast 10 100
    _ ≤ (P : Real) ^ (7 / 10 : Real) := hpow

private theorem chenTen_first_majorArc_error_le
    {P : Nat} (hPbig : (10 : Nat) ^ 100 ≤ P) :
    (10 : Real) ^ 25 * (P : Real) ^ (93 / 10 : Real) ≤
      (1 / 100000 : Real) * (P : Real) ^ 10 := by
  have hP : 0 < P := lt_of_lt_of_le (by norm_num) hPbig
  have hPR : (0 : Real) < P := by exact_mod_cast hP
  have h70 := ten_pow_seventy_le_rpow_seven_tenths hPbig
  have hcoef : (10 : Real) ^ 25 ≤
      (1 / 100000 : Real) * (P : Real) ^ (7 / 10 : Real) := by
    calc
      (10 : Real) ^ 25 ≤ (1 / 100000 : Real) * (10 : Real) ^ 70 := by
        norm_num
      _ ≤ (1 / 100000 : Real) * (P : Real) ^ (7 / 10 : Real) := by
        gcongr
  calc
    (10 : Real) ^ 25 * (P : Real) ^ (93 / 10 : Real) ≤
        ((1 / 100000 : Real) * (P : Real) ^ (7 / 10 : Real)) *
          (P : Real) ^ (93 / 10 : Real) := by gcongr
    _ = (1 / 100000 : Real) * (P : Real) ^ 10 := by
      rw [show (1 / 100000 : Real) * (P : Real) ^ (7 / 10 : Real) *
          (P : Real) ^ (93 / 10 : Real) =
        (1 / 100000 : Real) * ((P : Real) ^ (7 / 10 : Real) *
          (P : Real) ^ (93 / 10 : Real)) by ring]
      rw [← Real.rpow_add hPR]
      norm_num [Real.rpow_natCast]

/-- The singular lower bound and major-arc errors yield the exact positive real-part constant. -/
theorem chenTenMajorArc_re_lower_exact
    {P N : Nat} (hPbig : (10 : Nat) ^ 100 ≤ P)
    (hNlower : (P : Real) ^ 5 / 2 ≤ (N : Real))
    (hRlower :
      (2999 / 1000 : Real) * chenTenT15 * (N : Real) ^ 2 ≤
        (chenTenSingularIntegral P N).re) :
    (22089501 / 40000000000 : Real) * (P : Real) ^ 10 ≤
      (∑ i : ChenTenArcIndex P,
        ∫ alpha in chenTenArc P i,
          chenTenRepresentationIntegrand P N alpha).re := by
  let A : Complex := ∑ i : ChenTenArcIndex P,
    ∫ alpha in chenTenArc P i,
      chenTenRepresentationIntegrand P N alpha
  let R : Complex := chenTenSingularIntegral P N
  let S : Complex := chenTenSingularSeries N
  change (22089501 / 40000000000 : Real) * (P : Real) ^ 10 ≤ A.re
  have hPcast : (10 : Real) ^ 100 ≤ (P : Real) := by
    exact_mod_cast hPbig
  have hPbridge : (10 : Real) ^ 30 ≤ (P : Real) := by
    exact (by norm_num : (10 : Real) ^ 30 ≤ 10 ^ 100).trans hPcast
  have happrox :
      ‖A - R * S‖ ≤
        (10 : Real) ^ 25 * (P : Real) ^ (93 / 10 : Real) +
          (10 : Real) ^ 30 * (P : Real) ^ (-1 / 2 : Real) * ‖R‖ := by
    simpa [A, R, S] using
      norm_sum_chenTenMajorArcs_sub_singularIntegral_mul_series_le_source
        (P := P) (N := N) hPbridge
  have hTnonneg : (0 : Real) ≤ chenTenT15 :=
    (by norm_num : (0 : Real) ≤ 1 / 100).trans
      one_hundredth_le_chenTenT15
  have hRmain_nonneg :
      0 ≤ (2999 / 1000 : Real) * chenTenT15 * (N : Real) ^ 2 := by
    positivity
  have hRnonneg : 0 ≤ R.re := by
    dsimp [R]
    exact hRmain_nonneg.trans hRlower
  have hRnorm : ‖R‖ = R.re := by
    dsimp [R]
    exact scratch_norm_chenTenSingularIntegral_eq_re_of_nonneg hRnonneg
  rw [hRnorm] at happrox
  have happroxRe :
      |A.re - (R * S).re| ≤
        (10 : Real) ^ 25 * (P : Real) ^ (93 / 10 : Real) +
          (10 : Real) ^ 30 * (P : Real) ^ (-1 / 2 : Real) * R.re := by
    have hre := (Complex.abs_re_le_norm (A - R * S)).trans happrox
    simpa only [Complex.sub_re] using hre
  have hAraw :
      (R * S).re -
          (10 : Real) ^ 25 * (P : Real) ^ (93 / 10 : Real) -
          (10 : Real) ^ 30 * (P : Real) ^ (-1 / 2 : Real) * R.re ≤
        A.re := by
    linarith [(abs_le.mp happroxRe).1]
  have hRim : R.im = 0 := by
    dsimp [R]
    exact chenTenSingularIntegral_im_eq_zero P N
  have hproduct : (R * S).re = R.re * S.re := by
    rw [Complex.mul_re, hRim]
    ring
  have hS : (3 / 40 : Real) ≤ S.re := by
    dsimp [S]
    exact three_fortieths_le_chenTenSingularSeries_re N
  have htail := chenTen_series_tail_factor_le hPbig
  have hfactor :
      (7499 / 100000 : Real) ≤
        S.re - (10 : Real) ^ 30 * (P : Real) ^ (-1 / 2 : Real) := by
    linarith
  have hproductTail :
      R.re * (7499 / 100000 : Real) ≤
        (R * S).re -
          (10 : Real) ^ 30 * (P : Real) ^ (-1 / 2 : Real) * R.re := by
    rw [hproduct]
    calc
      R.re * (7499 / 100000 : Real) ≤
          R.re *
            (S.re - (10 : Real) ^ 30 *
              (P : Real) ^ (-1 / 2 : Real)) := by
        exact mul_le_mul_of_nonneg_left hfactor hRnonneg
      _ = R.re * S.re -
          (10 : Real) ^ 30 * (P : Real) ^ (-1 / 2 : Real) * R.re := by
        ring
  have hNsquare : (P : Real) ^ 10 / 4 ≤ (N : Real) ^ 2 := by
    calc
      (P : Real) ^ 10 / 4 = ((P : Real) ^ 5 / 2) ^ 2 := by ring
      _ ≤ (N : Real) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hNlower 2
  have hTN :
      (1 / 100 : Real) * ((P : Real) ^ 10 / 4) ≤
        chenTenT15 * (N : Real) ^ 2 := by
    exact mul_le_mul one_hundredth_le_chenTenT15 hNsquare
      (by positivity) hTnonneg
  have hRmain :
      (2999 / 1000 : Real) * (1 / 100 : Real) * (1 / 4 : Real) *
          (7499 / 100000 : Real) * (P : Real) ^ 10 ≤
        R.re * (7499 / 100000 : Real) := by
    calc
      (2999 / 1000 : Real) * (1 / 100 : Real) * (1 / 4 : Real) *
          (7499 / 100000 : Real) * (P : Real) ^ 10 =
        ((2999 / 1000 : Real) * (7499 / 100000 : Real)) *
          ((1 / 100 : Real) * ((P : Real) ^ 10 / 4)) := by ring
      _ ≤ ((2999 / 1000 : Real) * (7499 / 100000 : Real)) *
          (chenTenT15 * (N : Real) ^ 2) := by
        exact mul_le_mul_of_nonneg_left hTN (by positivity)
      _ = ((2999 / 1000 : Real) * chenTenT15 * (N : Real) ^ 2) *
          (7499 / 100000 : Real) := by ring
      _ ≤ R.re * (7499 / 100000 : Real) := by
        dsimp [R]
        exact mul_le_mul_of_nonneg_right hRlower (by norm_num)
  have hfirst := chenTen_first_majorArc_error_le hPbig
  have hpre :
      (2999 / 1000 : Real) * (1 / 100 : Real) * (1 / 4 : Real) *
          (7499 / 100000 : Real) * (P : Real) ^ 10 -
        (10 : Real) ^ 25 * (P : Real) ^ (93 / 10 : Real) ≤ A.re := by
    linarith [hRmain, hproductTail, hAraw]
  calc
    (22089501 / 40000000000 : Real) * (P : Real) ^ 10 =
        ((2999 / 1000 : Real) * (1 / 100 : Real) * (1 / 4 : Real) *
          (7499 / 100000 : Real) - 1 / 100000) * (P : Real) ^ 10 := by
      norm_num
    _ ≤ (2999 / 1000 : Real) * (1 / 100 : Real) * (1 / 4 : Real) *
          (7499 / 100000 : Real) * (P : Real) ^ 10 -
        (10 : Real) ^ 25 * (P : Real) ^ (93 / 10 : Real) := by
      linarith
    _ ≤ A.re := hpre

/-- The exact estimate implies the convenient non-strict `P ^ 10 / 2000` lower bound. -/
theorem one_2000_mul_P_pow_ten_le_chenTenMajorArc_re
    {P N : Nat} (hPbig : (10 : Nat) ^ 100 ≤ P)
    (hNlower : (P : Real) ^ 5 / 2 ≤ (N : Real))
    (hRlower :
      (2999 / 1000 : Real) * chenTenT15 * (N : Real) ^ 2 ≤
        (chenTenSingularIntegral P N).re) :
    (1 / 2000 : Real) * (P : Real) ^ 10 ≤
      (∑ i : ChenTenArcIndex P,
        ∫ alpha in chenTenArc P i,
          chenTenRepresentationIntegrand P N alpha).re := by
  have hexact := chenTenMajorArc_re_lower_exact hPbig hNlower hRlower
  have hPnonneg : (0 : Real) ≤ (P : Real) ^ 10 := by positivity
  exact (mul_le_mul_of_nonneg_right
    (by norm_num : (1 / 2000 : Real) ≤ 22089501 / 40000000000)
    hPnonneg).trans hexact

/-- Positivity of `P` strengthens the convenient major-arc lower bound to a strict inequality. -/
theorem one_2000_mul_P_pow_ten_lt_chenTenMajorArc_re
    {P N : Nat} (hPbig : (10 : Nat) ^ 100 ≤ P)
    (hNlower : (P : Real) ^ 5 / 2 ≤ (N : Real))
    (hRlower :
      (2999 / 1000 : Real) * chenTenT15 * (N : Real) ^ 2 ≤
        (chenTenSingularIntegral P N).re) :
    (1 / 2000 : Real) * (P : Real) ^ 10 <
      (∑ i : ChenTenArcIndex P,
        ∫ alpha in chenTenArc P i,
          chenTenRepresentationIntegrand P N alpha).re := by
  have hexact := chenTenMajorArc_re_lower_exact hPbig hNlower hRlower
  have hP : 0 < P := lt_of_lt_of_le (by norm_num) hPbig
  have hPpow : (0 : Real) < (P : Real) ^ 10 := by positivity
  exact (mul_lt_mul_of_pos_right
    (by norm_num : (1 / 2000 : Real) < 22089501 / 40000000000)
    hPpow).trans_le hexact

/-- The source singular-integral estimate supplies the strict positive major-arc bound. -/
theorem one_2000_mul_P_pow_ten_lt_chenTenMajorArc_re_source
    {P N : Nat} (hPbig : (10 : Nat) ^ 100 ≤ P)
    (hNlower : (P : Real) ^ 5 / 2 ≤ (N : Real))
    (hNupper : N ≤ (P + 1) ^ 5) :
    (1 / 2000 : Real) * (P : Real) ^ 10 <
      (∑ i : ChenTenArcIndex P,
        ∫ alpha in chenTenArc P i,
          chenTenRepresentationIntegrand P N alpha).re := by
  exact one_2000_mul_P_pow_ten_lt_chenTenMajorArc_re hPbig hNlower
    (chenTen_singularIntegral_re_lower_source hPbig hNlower hNupper)

end

end Waring.Analytic
