import PrimesRestrictedDigits.MajorArcs.Phase

/-!
# Finite weighted phase sums

This is the shared finite exponential sum used by the major-arc classes in
`MAYNARD-PRD-PUBLISHED`, Sections 9 and 11.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- A finite weighted exponential sum in the analytic-number-theory phase. -/
noncomputable def majorArcWeightedPhaseSum
    (s : Finset Nat) (w : Nat → Complex) (theta : Real) : Complex :=
  ∑ n ∈ s, w n * majorArcPhase ((n : Real) * theta)

/-- A nonnegative real weighted phase sum is bounded by its total mass. -/
theorem norm_majorArcWeightedPhaseSum_real_le_sum
    (s : Finset Nat) (w : Nat → Real)
    (hw : ∀ n ∈ s, 0 ≤ w n) (theta : Real) :
    ‖majorArcWeightedPhaseSum s (fun n => (w n : Complex)) theta‖ ≤
      ∑ n ∈ s, w n := by
  unfold majorArcWeightedPhaseSum
  calc
    ‖∑ n ∈ s, (w n : Complex) *
        majorArcPhase ((n : Real) * theta)‖ ≤
        ∑ n ∈ s, ‖(w n : Complex) *
          majorArcPhase ((n : Real) * theta)‖ :=
      norm_sum_le _ _
    _ = ∑ n ∈ s, w n := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw n hn),
        majorArcPhase, Complex.norm_exp_ofReal_mul_I, mul_one]

end PrimesRestrictedDigits
