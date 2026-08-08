import Waring.Analytic.ProductFiberCauchy
import Waring.Analytic.RestrictedTripleDivisorSecondMoment

/-!
# Cauchy over restricted triple-product fibers

This file applies the direct product-fiber Cauchy bound at the support scale
used in Chen's fourth differencing step.
-/

namespace Waring.Analytic

open scoped BigOperators

/-- If every value in the restricted product fiber over `z` has square at
most `majorant z`, then the complete fiber sum is controlled by the proved
restricted second moment. -/
theorem sq_sum_restrictedTripleFiber_le {P : Nat} (hP : 3 ≤ P)
    (value : Nat → (Sigma fun _ : Nat ↦ Nat) → Real)
    (majorant : Nat → Real)
    (hmajorant : ∀ z ∈ Finset.Icc 1 (P ^ 3 / 27), 0 ≤ majorant z)
    (hvalue : ∀ z ∈ Finset.Icc 1 (P ^ 3 / 27),
      ∀ x ∈ restrictedTripleDivisorChoices P z,
        (value z x) ^ 2 ≤ majorant z) :
    (∑ z ∈ Finset.Icc 1 (P ^ 3 / 27),
        ∑ x ∈ restrictedTripleDivisorChoices P z, value z x) ^ 2 ≤
      ((81 : Real) / 16 * (P : Real) ^ 3 *
          (Real.log P + 2) ^ 8) *
        ∑ z ∈ Finset.Icc 1 (P ^ 3 / 27), majorant z := by
  have hCauchy := sq_sum_fiberSum_le_sum_card_sq_mul_sum_majorant
    (Finset.Icc 1 (P ^ 3 / 27))
    (restrictedTripleDivisorChoices P) value majorant hmajorant hvalue
  have hmajorantSum :
      0 ≤ ∑ z ∈ Finset.Icc 1 (P ^ 3 / 27), majorant z :=
    Finset.sum_nonneg hmajorant
  have hmoment :
      ∑ z ∈ Finset.Icc 1 (P ^ 3 / 27),
          (restrictedTripleDivisorCount P z : Real) ^ 2 ≤
        (81 : Real) / 16 * (P : Real) ^ 3 *
          (Real.log P + 2) ^ 8 := by
    simpa only [Nat.cast_sum, Nat.cast_pow] using
      sum_restrictedTripleDivisorCount_sq_le hP
  calc
    (∑ z ∈ Finset.Icc 1 (P ^ 3 / 27),
        ∑ x ∈ restrictedTripleDivisorChoices P z, value z x) ^ 2 ≤
        (∑ z ∈ Finset.Icc 1 (P ^ 3 / 27),
          (restrictedTripleDivisorCount P z : Real) ^ 2) *
            ∑ z ∈ Finset.Icc 1 (P ^ 3 / 27), majorant z := by
      simpa [restrictedTripleDivisorCount] using hCauchy
    _ ≤ ((81 : Real) / 16 * (P : Real) ^ 3 *
          (Real.log P + 2) ^ 8) *
        ∑ z ∈ Finset.Icc 1 (P ^ 3 / 27), majorant z := by
      exact mul_le_mul_of_nonneg_right
        hmoment hmajorantSum

end Waring.Analytic
