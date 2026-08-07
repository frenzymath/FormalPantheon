import BoundedGaps.Maynard.ImprovedGPY.S2TrivialDiscrepancy

noncomputable section

/-!
# Tau-weighted indexed S2 distribution

Maynard2013v3, in the error part of `lmm:S2Expression1` (source lines
363--370), combines the `tau_{3k}` fiber multiplicity, a trivial pointwise
progression bound, Cauchy--Schwarz, and a level-of-distribution estimate.  This
file composes the checked finite versions for the exact pair/shift index.
-/

namespace BoundedGaps.Maynard

open scoped ArithmeticFunction.omega BigOperators

theorem PrimeLevelWitness.sum_maxProgressionDiscrepancy_compatiblePairShift_tau
    {θ A C : ℝ} {X₀ x Q : ℕ}
    {H : Finset ℕ} {D : Finset (H → ℕ)} {R W : ℕ}
    (hw : PrimeLevelWitness θ A C X₀) (hx : X₀ ≤ x)
    (hH : H.Nonempty) (hW : Squarefree W)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (hSQ : (compatiblePairShiftIndex H D).image
      (compatiblePairShiftModulus H W) ⊆ Finset.Icc 1 Q)
    (hQx : Q ≤ x + 1)
    (hcut : (compatiblePairShiftIndex H D).image
      (compatiblePairShiftModulus H W) ⊆
        Finset.Icc 1 (modulusCutoff θ x)) :
    (∑ i ∈ compatiblePairShiftIndex H D,
        maxProgressionDiscrepancy x (compatiblePairShiftModulus H W i)) ≤
      (Fintype.card H : ℝ) *
        (Real.sqrt
            ((3 : ℝ) * ((x + 1 : ℕ) : ℝ) *
              (1 + Real.log Q) ^
                (2 * (3 * Fintype.card H) ^ 2)) *
          Real.sqrt
            (C * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) A)) := by
  let S := (compatiblePairShiftIndex H D).image
    (compatiblePairShiftModulus H W)
  have hfiber := sum_maxProgressionDiscrepancy_comp_le_tauPow hH hW hD x
  have hweighted :=
    hw.sum_tauPow_mul_maxProgressionDiscrepancy_explicit hx
      (d := 3 * Fintype.card H) S hSQ
      (fun q hq => squarefree_of_mem_compatiblePairShiftModulus_image
        hW hD hq) hQx hcut
  calc
    (∑ i ∈ compatiblePairShiftIndex H D,
        maxProgressionDiscrepancy x (compatiblePairShiftModulus H W i)) ≤
        ∑ m ∈ S,
          (((3 * Fintype.card H) ^ ω m * Fintype.card H : ℕ) : ℝ) *
            maxProgressionDiscrepancy x m := hfiber
    _ = (Fintype.card H : ℝ) *
        ∑ m ∈ S, (((3 * Fintype.card H) ^ ω m : ℕ) : ℝ) *
          maxProgressionDiscrepancy x m := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      push_cast
      ring
    _ ≤ (Fintype.card H : ℝ) *
        (Real.sqrt
            ((3 : ℝ) * ((x + 1 : ℕ) : ℝ) *
              (1 + Real.log Q) ^
                (2 * (3 * Fintype.card H) ^ 2)) *
          Real.sqrt
            (C * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) A)) := by
      exact mul_le_mul_of_nonneg_left hweighted (Nat.cast_nonneg _)

end BoundedGaps.Maynard
