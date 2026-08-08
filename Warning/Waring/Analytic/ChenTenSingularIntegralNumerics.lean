import Waring.Analytic.ChenTenCumulativeParameters
import Waring.Analytic.ChenTenSingularIntegralLowerBound

/-!
# Numerical absorption in the singular-integral estimate

This file proves that the cumulative and analytic error terms fit inside the
explicit fraction of Chen's main singular-integral term at the chosen large
parameter threshold.
-/

set_option autoImplicit false

namespace Waring.Analytic

noncomputable section

private theorem tenPowEleven_le_rpow_one_fifth
    {P : Nat} (hPbig : (10 : Nat) ^ 100 ≤ P) :
    (10 : Real) ^ 11 ≤ (P : Real) ^ (1 / 5 : Real) := by
  have hPcast : (10 : Real) ^ 100 ≤ (P : Real) := by
    exact_mod_cast hPbig
  have hpow := Real.rpow_le_rpow (by positivity) hPcast
    (by norm_num : (0 : Real) ≤ 1 / 5)
  calc
    (10 : Real) ^ 11 ≤ (10 : Real) ^ 20 := by norm_num
    _ = ((10 : Real) ^ 100) ^ (1 / 5 : Real) := by
      calc
        (10 : Real) ^ 20 = (10 : Real) ^ (20 : Real) :=
          (Real.rpow_natCast 10 20).symm
        _ = (10 : Real) ^ ((100 : Real) * (1 / 5 : Real)) := by
          norm_num
        _ = ((10 : Real) ^ (100 : Real)) ^ (1 / 5 : Real) := by
          rw [Real.rpow_mul (by positivity)]
        _ = ((10 : Real) ^ 100) ^ (1 / 5 : Real) := by
          congr 1
          exact Real.rpow_natCast 10 100
    _ ≤ (P : Real) ^ (1 / 5 : Real) := hpow

/-- The cumulative and analytic errors occupy at most one thousandth of the main term. -/
theorem chenTen_source_errors_absorbed
    {P N : Nat} (hPbig : (10 : Nat) ^ 100 ≤ P)
    (hNlower : (P : Real) ^ 5 / 2 ≤ (N : Real)) :
    3000 * chenTenT15 * (N : Real) ^ 2 *
          (P : Real) ^ (-1 / 5 : Real) +
        3 * (10 : Real) ^ 4 * (P : Real) ^ (49 / 5 : Real) ≤
      (1 / 1000 : Real) * chenTenT15 * (N : Real) ^ 2 := by
  have hP : 0 < P := lt_of_lt_of_le (by norm_num) hPbig
  have hPR : (0 : Real) < P := by exact_mod_cast hP
  have hroot := tenPowEleven_le_rpow_one_fifth hPbig
  have hrootPos : (0 : Real) < (P : Real) ^ (1 / 5 : Real) := by
    positivity
  have hinv :
      ((P : Real) ^ (1 / 5 : Real))⁻¹ ≤
        ((10 : Real) ^ 11)⁻¹ :=
    (inv_le_inv₀ hrootPos (by positivity)).2 hroot
  have hneg :
      (P : Real) ^ (-1 / 5 : Real) ≤ ((10 : Real) ^ 11)⁻¹ := by
    rw [show (-1 / 5 : Real) = -(1 / 5 : Real) by norm_num,
      Real.rpow_neg hPR.le]
    exact hinv
  have hcumulativeCoefficient :
      3000 * (P : Real) ^ (-1 / 5 : Real) ≤ (1 / 2000 : Real) := by
    calc
      3000 * (P : Real) ^ (-1 / 5 : Real) ≤
          3000 * ((10 : Real) ^ 11)⁻¹ := by gcongr
      _ ≤ (1 / 2000 : Real) := by norm_num
  have hTnonneg : (0 : Real) ≤ chenTenT15 :=
    (by norm_num : (0 : Real) ≤ 1 / 100).trans
      one_hundredth_le_chenTenT15
  have hNnonneg : (0 : Real) ≤ N := by positivity
  have hcumulative :
      3000 * chenTenT15 * (N : Real) ^ 2 *
          (P : Real) ^ (-1 / 5 : Real) ≤
        (1 / 2000 : Real) * chenTenT15 * (N : Real) ^ 2 := by
    calc
      3000 * chenTenT15 * (N : Real) ^ 2 *
          (P : Real) ^ (-1 / 5 : Real) =
        (3000 * (P : Real) ^ (-1 / 5 : Real)) *
          (chenTenT15 * (N : Real) ^ 2) := by ring
      _ ≤ (1 / 2000 : Real) *
          (chenTenT15 * (N : Real) ^ 2) := by
        gcongr
      _ = (1 / 2000 : Real) * chenTenT15 * (N : Real) ^ 2 := by
        ring
  have hNsquare :
      ((P : Real) ^ 5 / 2) ^ 2 ≤ (N : Real) ^ 2 := by
    exact pow_le_pow_left₀ (by positivity) hNlower 2
  have hmainLower :
      (P : Real) ^ 10 / 800000 ≤
        (1 / 2000 : Real) * chenTenT15 * (N : Real) ^ 2 := by
    calc
      (P : Real) ^ 10 / 800000 =
          (1 / 2000 : Real) * (1 / 100 : Real) *
            (((P : Real) ^ 5 / 2) ^ 2) := by ring
      _ ≤ (1 / 2000 : Real) * chenTenT15 *
          (((P : Real) ^ 5 / 2) ^ 2) := by
        gcongr
        exact one_hundredth_le_chenTenT15
      _ ≤ (1 / 2000 : Real) * chenTenT15 * (N : Real) ^ 2 := by
        gcongr
  have hcoefficient :
      3 * (10 : Real) ^ 4 ≤
        (1 / 800000 : Real) * (P : Real) ^ (1 / 5 : Real) := by
    calc
      3 * (10 : Real) ^ 4 ≤
          (1 / 800000 : Real) * (10 : Real) ^ 11 := by norm_num
      _ ≤ (1 / 800000 : Real) *
          (P : Real) ^ (1 / 5 : Real) := by gcongr
  have hanalytic :
      3 * (10 : Real) ^ 4 * (P : Real) ^ (49 / 5 : Real) ≤
        (1 / 2000 : Real) * chenTenT15 * (N : Real) ^ 2 := by
    calc
      3 * (10 : Real) ^ 4 * (P : Real) ^ (49 / 5 : Real) ≤
          ((1 / 800000 : Real) * (P : Real) ^ (1 / 5 : Real)) *
            (P : Real) ^ (49 / 5 : Real) := by gcongr
      _ = (P : Real) ^ 10 / 800000 := by
        have hpow : (P : Real) ^ (1 / 5 : Real) *
            (P : Real) ^ (49 / 5 : Real) = (P : Real) ^ 10 := by
          rw [← Real.rpow_add hPR]
          norm_num [Real.rpow_natCast]
        rw [show (1 / 800000 : Real) * (P : Real) ^ (1 / 5 : Real) *
            (P : Real) ^ (49 / 5 : Real) =
          (1 / 800000 : Real) * ((P : Real) ^ (1 / 5 : Real) *
            (P : Real) ^ (49 / 5 : Real)) by ring, hpow]
        ring
      _ ≤ (1 / 2000 : Real) * chenTenT15 * (N : Real) ^ 2 :=
        hmainLower
  linarith

end

end Waring.Analytic
