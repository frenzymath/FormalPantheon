import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
/-! # CayleyLogUpper -/

open scoped BigOperators
open Set

namespace PrimesRestrictedDigits

noncomputable section

def cayleyLogSeriesUpper (x : Real) (n : Nat) : Real :=
  2 * ((Finset.range n).sum
      (fun i => x ^ (2 * i + 1) / (2 * i + 1)) +
    x ^ (2 * n + 1) / (1 - x ^ 2))

theorem log_cayley_le_cayleyLogSeriesUpper
    {x : Real} (hxNonneg : 0 <= x) (hxOne : x < 1) (n : Nat) :
    Real.log ((1 + x) / (1 - x)) <= cayleyLogSeriesUpper x n := by
  have h := Real.log_div_le_sum_range_add hxNonneg hxOne n
  unfold cayleyLogSeriesUpper
  linarith

private theorem tightCayleyDifference_hasDerivAt
    {y : Real} (hyNegOne : -1 < y) (hyOne : y < 1) :
    HasDerivAt
      (fun t : Real =>
        2 * (t + t ^ 3 / (3 * (1 - t ^ 2))) -
          Real.log ((1 + t) / (1 - t)))
      (4 * y ^ 4 / (3 * (1 - y ^ 2) ^ 2)) y := by
  have hOneSub : HasDerivAt (fun t : Real => 1 - t ^ 2) (-2 * y) y := by
    simpa using HasDerivAt.const_sub 1 (hasDerivAt_pow 2 y)
  have hDen : HasDerivAt (fun t : Real => 3 * (1 - t ^ 2))
      (3 * (-2 * y)) y := hOneSub.const_mul 3
  have hSqLt : y ^ 2 < 1 := by
    nlinarith [mul_pos (show 0 < 1 + y by linarith)
      (show 0 < 1 - y by linarith)]
  have hSqNe : 1 - y ^ 2 ≠ 0 := sub_ne_zero.mpr hSqLt.ne'
  have hDenNe : 3 * (1 - y ^ 2) ≠ 0 := mul_ne_zero (by norm_num) hSqNe
  have hTail : HasDerivAt (fun t : Real => t ^ 3 / (3 * (1 - t ^ 2)))
      (((3 * y ^ 2) * (3 * (1 - y ^ 2)) - y ^ 3 * (3 * (-2 * y))) /
        (3 * (1 - y ^ 2)) ^ 2) y :=
    (hasDerivAt_pow 3 y).div hDen hDenNe
  have hUpper := ((hasDerivAt_id y).add hTail).const_mul 2
  have hRatio : HasDerivAt (fun t : Real => (1 + t) / (1 - t))
      ((1 * (1 - y) - (1 + y) * (-1)) / (1 - y) ^ 2) y := by
    have hNumerator : HasDerivAt (fun t : Real => 1 + t) 1 y :=
      (hasDerivAt_id y).const_add 1
    have hDenominator : HasDerivAt (fun t : Real => 1 - t) (-1) y :=
      HasDerivAt.const_sub 1 (hasDerivAt_id y)
    exact hNumerator.div hDenominator (by dsimp; linarith)
  have hRatioNe : (1 + y) / (1 - y) ≠ 0 :=
    div_ne_zero (by linarith) (by linarith)
  apply (hUpper.sub (hRatio.log hRatioNe)).congr_deriv
  field_simp [hDenNe, hSqNe, show 1 - y ≠ 0 by linarith,
    show 1 + y ≠ 0 by linarith]
  ring

theorem log_cayley_le_tight_n_one
    {x : Real} (hxNonneg : 0 <= x) (hxOne : x < 1) :
    Real.log ((1 + x) / (1 - x)) <=
      2 * (x + x ^ 3 / (3 * (1 - x ^ 2))) := by
  let F : Real -> Real := fun t =>
    2 * (t + t ^ 3 / (3 * (1 - t ^ 2))) -
      Real.log ((1 + t) / (1 - t))
  have hDeriv : ∀ y ∈ Icc (0 : Real) x,
      HasDerivAt F (4 * y ^ 4 / (3 * (1 - y ^ 2) ^ 2)) y := by
    intro y hy
    exact tightCayleyDifference_hasDerivAt (by linarith [hy.1])
      (lt_of_le_of_lt hy.2 hxOne)
  have hContinuous : ContinuousOn F (Icc (0 : Real) x) := by
    intro y hy
    exact (hDeriv y hy).continuousAt.continuousWithinAt
  have hMonotone : MonotoneOn F (Icc (0 : Real) x) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 x) hContinuous
      (fun y hy => (hDeriv y (interior_subset hy)).hasDerivWithinAt)
      (fun y _ => by positivity)
  have h := hMonotone (left_mem_Icc.mpr hxNonneg) (right_mem_Icc.mpr hxNonneg) hxNonneg
  simpa [F] using h

end

end PrimesRestrictedDigits
