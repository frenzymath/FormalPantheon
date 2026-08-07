import BoundedGaps.Maynard.ImprovedGPY.S2TauDistribution
import BoundedGaps.Maynard.ImprovedGPY.S2UniformWitness

noncomputable section

/-!
# Tau-weighted shifted S2 endpoint aggregation

Maynard2013v3, in the error part of `lmm:S2Expression1` (source lines
351--370), applies the weighted distribution estimate uniformly to the shifted
prime endpoints. This file threads the checked tau estimate through those
varying endpoints and the existing coefficient-weighted error bridge.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

def tauIndexedEndpointEnvelope
    (H : Finset ℕ) (Q : ℕ) (C A : ℝ) (x : ℕ) : ℝ :=
  (Fintype.card H : ℝ) *
    (Real.sqrt
        ((3 : ℝ) * ((x + 1 : ℕ) : ℝ) *
          (1 + Real.log Q) ^ (2 * (3 * Fintype.card H) ^ 2)) *
      Real.sqrt
        (C * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) A))

theorem compatiblePairShiftModulus_image_subset_radius
    {H : Finset ℕ} {D : Finset (H → ℕ)} {R W : ℕ}
    (hW : 0 < W)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d) :
    (compatiblePairShiftIndex H D).image
        (compatiblePairShiftModulus H W) ⊆
      Finset.Icc 1 (W * R * R) := by
  classical
  intro q hq
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
  have hiData := compatiblePairShiftIndex_data hi
  exact Finset.mem_Icc.mpr
    ⟨divisorPairModulus_pos hW (hD i.1.1 hiData.1)
      (hD i.1.2 hiData.2.1),
    (divisorPairModulus_lt_W_mul_R_sq hW
      (hD i.1.1 hiData.1) (hD i.1.2 hiData.2.1)).le⟩

theorem PrimeLevelWitness.bound_compatiblePairShiftShiftedEndpointDiscrepancySum_tau
    {θ A C : ℝ} {X₀ : ℕ} (hw : PrimeLevelWitness θ A C X₀)
    {H : Finset ℕ} {D : Finset (H → ℕ)} {R W N : ℕ}
    (hH : H.Nonempty) (hW : Squarefree W)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (hupper : ∀ h : H, X₀ ≤ 2 * N + h.1 - 1)
    (hlower : ∀ h : H, X₀ ≤ N + h.1 - 1)
    (hcutUpper : ∀ h : H, W * R * R ≤
      modulusCutoff θ (2 * N + h.1 - 1))
    (hcutLower : ∀ h : H, W * R * R ≤
      modulusCutoff θ (N + h.1 - 1))
    (hsizeUpper : ∀ h : H, W * R * R ≤
      (2 * N + h.1 - 1) + 1)
    (hsizeLower : ∀ h : H, W * R * R ≤
      (N + h.1 - 1) + 1) :
    compatiblePairShiftShiftedEndpointDiscrepancySum H D W N ≤
      (∑ h : H, tauIndexedEndpointEnvelope H (W * R * R) C A
        (2 * N + h.1 - 1)) +
      ∑ h : H, tauIndexedEndpointEnvelope H (W * R * R) C A
        (N + h.1 - 1) := by
  have hWpos : 0 < W := Nat.pos_of_ne_zero hW.ne_zero
  have hSQ := compatiblePairShiftModulus_image_subset_radius hWpos hD
  calc
    compatiblePairShiftShiftedEndpointDiscrepancySum H D W N ≤
        (∑ h : H, ∑ i ∈ compatiblePairShiftIndex H D,
          maxProgressionDiscrepancy (2 * N + h.1 - 1)
            (compatiblePairShiftModulus H W i)) +
        ∑ h : H, ∑ i ∈ compatiblePairShiftIndex H D,
          maxProgressionDiscrepancy (N + h.1 - 1)
            (compatiblePairShiftModulus H W i) :=
      compatiblePairShiftShiftedEndpointDiscrepancySum_le_shift_sum H D W N
    _ ≤ (∑ h : H, tauIndexedEndpointEnvelope H (W * R * R) C A
          (2 * N + h.1 - 1)) +
        ∑ h : H, tauIndexedEndpointEnvelope H (W * R * R) C A
          (N + h.1 - 1) := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro h hh
        simpa [tauIndexedEndpointEnvelope] using
          (hw.sum_maxProgressionDiscrepancy_compatiblePairShift_tau
            (x := 2 * N + h.1 - 1) (Q := W * R * R)
            (hupper h) hH hW hD hSQ (hsizeUpper h)
            (compatiblePairShiftModulus_image_subset_cutoff hWpos hD
              (hcutUpper h)))
      · apply Finset.sum_le_sum
        intro h hh
        simpa [tauIndexedEndpointEnvelope] using
          (hw.sum_maxProgressionDiscrepancy_compatiblePairShift_tau
            (x := N + h.1 - 1) (Q := W * R * R)
            (hlower h) hH hW hD hSQ (hsizeLower h)
            (compatiblePairShiftModulus_image_subset_cutoff hWpos hD
              (hcutLower h)))

theorem PrimeLevelWitness.bound_compatiblePairShiftWeightedShiftedErrorSum_tau
    {θ A C : ℝ} {X₀ : ℕ} (hw : PrimeLevelWitness θ A C X₀)
    {H : Finset ℕ} {D : Finset (H → ℕ)} {R W v N : ℕ}
    (hH : H.Nonempty) (hW : Squarefree W)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (hcoverage : CoversShiftDifferencePrimes H W)
    (hv : ∀ h ∈ H, Nat.Coprime (v + h) W)
    (lambda : (H → ℕ) → ℝ) (L : ℝ)
    (hN : 0 < N) (hL : 0 ≤ L)
    (hbound : ∀ d ∈ D, |lambda d| ≤ L)
    (hupper : ∀ h : H, X₀ ≤ 2 * N + h.1 - 1)
    (hlower : ∀ h : H, X₀ ≤ N + h.1 - 1)
    (hcutUpper : ∀ h : H, W * R * R ≤
      modulusCutoff θ (2 * N + h.1 - 1))
    (hcutLower : ∀ h : H, W * R * R ≤
      modulusCutoff θ (N + h.1 - 1))
    (hsizeUpper : ∀ h : H, W * R * R ≤
      (2 * N + h.1 - 1) + 1)
    (hsizeLower : ∀ h : H, W * R * R ≤
      (N + h.1 - 1) + 1) :
    compatiblePairShiftWeightedShiftedErrorSum H D R W v N lambda hD ≤
      L ^ 2 *
        ((∑ h : H, tauIndexedEndpointEnvelope H (W * R * R) C A
          (2 * N + h.1 - 1)) +
        ∑ h : H, tauIndexedEndpointEnvelope H (W * R * R) C A
          (N + h.1 - 1)) := by
  exact (compatiblePairShiftWeightedShiftedErrorSum_le
      (Nat.pos_of_ne_zero hW.ne_zero) hD hcoverage hv hN hL hbound).trans
    (mul_le_mul_of_nonneg_left
      (hw.bound_compatiblePairShiftShiftedEndpointDiscrepancySum_tau
        hH hW hD hupper hlower hcutUpper hcutLower hsizeUpper hsizeLower)
      (sq_nonneg L))

theorem PrimeLevelWitness.bound_abs_compatiblePairRestrictedErrorOuter_tau
    {θ A C : ℝ} {X₀ : ℕ} (hw : PrimeLevelWitness θ A C X₀)
    {H : Finset ℕ} {D : Finset (H → ℕ)} {R W v N : ℕ}
    (hH : H.Nonempty) (hW : Squarefree W)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (hcoverage : CoversShiftDifferencePrimes H W)
    (hv : ∀ h ∈ H, Nat.Coprime (v + h) W)
    (lambda : (H → ℕ) → ℝ) (L : ℝ)
    (hN : 0 < N) (hL : 0 ≤ L)
    (hbound : ∀ d ∈ D, |lambda d| ≤ L)
    (hupper : ∀ h : H, X₀ ≤ 2 * N + h.1 - 1)
    (hlower : ∀ h : H, X₀ ≤ N + h.1 - 1)
    (hcutUpper : ∀ h : H, W * R * R ≤
      modulusCutoff θ (2 * N + h.1 - 1))
    (hcutLower : ∀ h : H, W * R * R ≤
      modulusCutoff θ (N + h.1 - 1))
    (hsizeUpper : ∀ h : H, W * R * R ≤
      (2 * N + h.1 - 1) + 1)
    (hsizeLower : ∀ h : H, W * R * R ≤
      (N + h.1 - 1) + 1) :
    |compatiblePairRestrictedErrorOuter H D R W v N lambda hD| ≤
      L ^ 2 *
        ((∑ h : H, tauIndexedEndpointEnvelope H (W * R * R) C A
          (2 * N + h.1 - 1)) +
        ∑ h : H, tauIndexedEndpointEnvelope H (W * R * R) C A
          (N + h.1 - 1)) := by
  calc
    |compatiblePairRestrictedErrorOuter H D R W v N lambda hD| ≤
        compatiblePairRestrictedAbsoluteErrorOuter H D R W v N lambda hD :=
      abs_compatiblePairRestrictedErrorOuter_le_absoluteErrorOuter hD
    _ = compatiblePairShiftWeightedShiftedErrorSum H D R W v N lambda hD :=
      compatiblePairRestrictedAbsoluteErrorOuter_eq_weightedShiftedErrorSum hD
    _ ≤ _ := hw.bound_compatiblePairShiftWeightedShiftedErrorSum_tau
      hH hW hD hcoverage hv lambda L hN hL hbound hupper hlower
      hcutUpper hcutLower hsizeUpper hsizeLower

end BoundedGaps.Maynard
