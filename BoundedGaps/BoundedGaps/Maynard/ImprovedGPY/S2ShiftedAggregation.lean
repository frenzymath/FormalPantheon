import BoundedGaps.Maynard.ImprovedGPY.S2ReducedResidue
import BoundedGaps.Maynard.ImprovedGPY.S2ConcreteDistribution

noncomputable section

/-!
# Aggregating the shifted S2 endpoint discrepancies

Maynard2013v3, in the error estimate for `lmm:S2Expression1` (source lines
363--370), applies a uniform distribution estimate to the finitely many shifted
prime progressions. This file retains each shifted endpoint and performs that
finite aggregation explicitly.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

def compatiblePairShiftShiftedEndpointDiscrepancySum
    (H : Finset ℕ) (D : Finset (H → ℕ)) (W N : ℕ) : ℝ :=
  ∑ i ∈ compatiblePairShiftIndex H D,
    (maxProgressionDiscrepancy (2 * N + i.2.1 - 1)
        (compatiblePairShiftModulus H W i) +
      maxProgressionDiscrepancy (N + i.2.1 - 1)
        (compatiblePairShiftModulus H W i))

theorem compatiblePairShiftShiftedEndpointDiscrepancySum_le_shift_sum
    (H : Finset ℕ) (D : Finset (H → ℕ)) (W N : ℕ) :
    compatiblePairShiftShiftedEndpointDiscrepancySum H D W N ≤
      (∑ h : H, ∑ i ∈ compatiblePairShiftIndex H D,
        maxProgressionDiscrepancy (2 * N + h.1 - 1)
          (compatiblePairShiftModulus H W i)) +
      ∑ h : H, ∑ i ∈ compatiblePairShiftIndex H D,
        maxProgressionDiscrepancy (N + h.1 - 1)
          (compatiblePairShiftModulus H W i) := by
  classical
  unfold compatiblePairShiftShiftedEndpointDiscrepancySum
  calc
    (∑ i ∈ compatiblePairShiftIndex H D,
        (maxProgressionDiscrepancy (2 * N + i.2.1 - 1)
            (compatiblePairShiftModulus H W i) +
          maxProgressionDiscrepancy (N + i.2.1 - 1)
            (compatiblePairShiftModulus H W i))) ≤
        ∑ i ∈ compatiblePairShiftIndex H D,
          ((∑ h : H, maxProgressionDiscrepancy (2 * N + h.1 - 1)
              (compatiblePairShiftModulus H W i)) +
            ∑ h : H, maxProgressionDiscrepancy (N + h.1 - 1)
              (compatiblePairShiftModulus H W i)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply add_le_add
      · exact Finset.single_le_sum
          (f := fun h : H => maxProgressionDiscrepancy (2 * N + h.1 - 1)
            (compatiblePairShiftModulus H W i))
          (fun h hh => maxProgressionDiscrepancy_nonneg _ _) (Finset.mem_univ i.2)
      · exact Finset.single_le_sum
          (f := fun h : H => maxProgressionDiscrepancy (N + h.1 - 1)
            (compatiblePairShiftModulus H W i))
          (fun h hh => maxProgressionDiscrepancy_nonneg _ _) (Finset.mem_univ i.2)
    _ = (∑ h : H, ∑ i ∈ compatiblePairShiftIndex H D,
          maxProgressionDiscrepancy (2 * N + h.1 - 1)
            (compatiblePairShiftModulus H W i)) +
        ∑ h : H, ∑ i ∈ compatiblePairShiftIndex H D,
          maxProgressionDiscrepancy (N + h.1 - 1)
            (compatiblePairShiftModulus H W i) := by
      rw [Finset.sum_add_distrib]
      congr 1 <;> rw [Finset.sum_comm]

theorem PrimeLevelWitness.bound_compatiblePairShiftShiftedEndpointDiscrepancySum
    {θ A C : ℝ} {X₀ : ℕ} (hw : PrimeLevelWitness θ A C X₀)
    {H : Finset ℕ} {D : Finset (H → ℕ)} {R W N : ℕ}
    (hW : 0 < W)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (hupper : ∀ h : H, X₀ ≤ 2 * N + h.1 - 1)
    (hlower : ∀ h : H, X₀ ≤ N + h.1 - 1)
    (hcutUpper : ∀ h : H, W * R * R ≤
      modulusCutoff θ (2 * N + h.1 - 1))
    (hcutLower : ∀ h : H, W * R * R ≤
      modulusCutoff θ (N + h.1 - 1)) :
    compatiblePairShiftShiftedEndpointDiscrepancySum H D W N ≤
      (∑ h : H, (D.card * D.card * H.card : ℝ) *
        (C * ((2 * N + h.1 - 1 : ℕ) : ℝ) /
          Real.rpow (Real.log ((2 * N + h.1 - 1 : ℕ) : ℝ)) A)) +
      ∑ h : H, (D.card * D.card * H.card : ℝ) *
        (C * ((N + h.1 - 1 : ℕ) : ℝ) /
          Real.rpow (Real.log ((N + h.1 - 1 : ℕ) : ℝ)) A) := by
  calc
    compatiblePairShiftShiftedEndpointDiscrepancySum H D W N ≤
        (∑ h : H, ∑ i ∈ compatiblePairShiftIndex H D,
          maxProgressionDiscrepancy (2 * N + h.1 - 1)
            (compatiblePairShiftModulus H W i)) +
        ∑ h : H, ∑ i ∈ compatiblePairShiftIndex H D,
          maxProgressionDiscrepancy (N + h.1 - 1)
            (compatiblePairShiftModulus H W i) :=
      compatiblePairShiftShiftedEndpointDiscrepancySum_le_shift_sum H D W N
    _ ≤ (∑ h : H, (D.card * D.card * H.card : ℝ) *
          (C * ((2 * N + h.1 - 1 : ℕ) : ℝ) /
            Real.rpow (Real.log ((2 * N + h.1 - 1 : ℕ) : ℝ)) A)) +
        ∑ h : H, (D.card * D.card * H.card : ℝ) *
          (C * ((N + h.1 - 1 : ℕ) : ℝ) /
            Real.rpow (Real.log ((N + h.1 - 1 : ℕ) : ℝ)) A) := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro h _
        exact hw.sum_maxProgressionDiscrepancy_compatiblePairShiftModulus_trivial
          (hupper h) hW hD (hcutUpper h)
      · apply Finset.sum_le_sum
        intro h _
        exact hw.sum_maxProgressionDiscrepancy_compatiblePairShiftModulus_trivial
          (hlower h) hW hD (hcutLower h)

theorem hasPrimeLevel_compatiblePairShiftShiftedEndpointDiscrepancySum
    {θ : ℝ} (hlevel : hasPrimeLevel θ)
    (A : ℝ) (hA : 0 < A)
    {H : Finset ℕ} {D : Finset (H → ℕ)} {R W : ℕ}
    (hW : 0 < W)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, 3 ≤ X₀ ∧
      ∀ N : ℕ,
        (∀ h : H, X₀ ≤ 2 * N + h.1 - 1) →
        (∀ h : H, X₀ ≤ N + h.1 - 1) →
        (∀ h : H, W * R * R ≤
          modulusCutoff θ (2 * N + h.1 - 1)) →
        (∀ h : H, W * R * R ≤
          modulusCutoff θ (N + h.1 - 1)) →
        compatiblePairShiftShiftedEndpointDiscrepancySum H D W N ≤
          (∑ h : H, (D.card * D.card * H.card : ℝ) *
            (C * ((2 * N + h.1 - 1 : ℕ) : ℝ) /
              Real.rpow (Real.log ((2 * N + h.1 - 1 : ℕ) : ℝ)) A)) +
          ∑ h : H, (D.card * D.card * H.card : ℝ) *
            (C * ((N + h.1 - 1 : ℕ) : ℝ) /
              Real.rpow (Real.log ((N + h.1 - 1 : ℕ) : ℝ)) A) := by
  obtain ⟨C, hC, X₀, hX₀, hdist⟩ :=
    hasPrimeLevel_sum_maxProgressionDiscrepancy_compatiblePairShiftModulus_trivial
      hlevel A hA hW hD
  refine ⟨C, hC, X₀, hX₀, ?_⟩
  intro N hupper hlower hcutUpper hcutLower
  calc
    compatiblePairShiftShiftedEndpointDiscrepancySum H D W N ≤
        (∑ h : H, ∑ i ∈ compatiblePairShiftIndex H D,
          maxProgressionDiscrepancy (2 * N + h.1 - 1)
            (compatiblePairShiftModulus H W i)) +
        ∑ h : H, ∑ i ∈ compatiblePairShiftIndex H D,
          maxProgressionDiscrepancy (N + h.1 - 1)
            (compatiblePairShiftModulus H W i) :=
      compatiblePairShiftShiftedEndpointDiscrepancySum_le_shift_sum H D W N
    _ ≤ (∑ h : H, (D.card * D.card * H.card : ℝ) *
          (C * ((2 * N + h.1 - 1 : ℕ) : ℝ) /
            Real.rpow (Real.log ((2 * N + h.1 - 1 : ℕ) : ℝ)) A)) +
        ∑ h : H, (D.card * D.card * H.card : ℝ) *
          (C * ((N + h.1 - 1 : ℕ) : ℝ) /
            Real.rpow (Real.log ((N + h.1 - 1 : ℕ) : ℝ)) A) := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro h hh
        exact hdist (2 * N + h.1 - 1) (hupper h) (hcutUpper h)
      · apply Finset.sum_le_sum
        intro h hh
        exact hdist (N + h.1 - 1) (hlower h) (hcutLower h)

end BoundedGaps.Maynard
