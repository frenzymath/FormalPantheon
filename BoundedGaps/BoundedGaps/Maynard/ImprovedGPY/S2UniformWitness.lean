import BoundedGaps.Maynard.ImprovedGPY.S2ActualError

noncomputable section

/-!
# Fixed-witness S2 error bounds

This module threads one `PrimeLevelWitness` through the shifted endpoint and
actual restricted-error bounds. The fixed witness preserves the uniformity in
Maynard2013v3, Section 5, source lines 353--370.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

theorem PrimeLevelWitness.bound_compatiblePairShiftWeightedShiftedErrorSum
    {θ A C : ℝ} {X₀ : ℕ} (hw : PrimeLevelWitness θ A C X₀)
    {H : Finset ℕ} {D : Finset (H → ℕ)} {R W v N : ℕ}
    (hW : 0 < W)
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
      modulusCutoff θ (N + h.1 - 1)) :
    compatiblePairShiftWeightedShiftedErrorSum H D R W v N lambda hD ≤
      L ^ 2 * ((∑ h : H, (D.card * D.card * H.card : ℝ) *
        (C * ((2 * N + h.1 - 1 : ℕ) : ℝ) /
          Real.rpow (Real.log ((2 * N + h.1 - 1 : ℕ) : ℝ)) A)) +
      ∑ h : H, (D.card * D.card * H.card : ℝ) *
        (C * ((N + h.1 - 1 : ℕ) : ℝ) /
          Real.rpow (Real.log ((N + h.1 - 1 : ℕ) : ℝ)) A)) := by
  exact (compatiblePairShiftWeightedShiftedErrorSum_le
      hW hD hcoverage hv hN hL hbound).trans
    (mul_le_mul_of_nonneg_left
      (hw.bound_compatiblePairShiftShiftedEndpointDiscrepancySum
        hW hD hupper hlower hcutUpper hcutLower)
      (sq_nonneg L))

theorem PrimeLevelWitness.bound_abs_compatiblePairRestrictedErrorOuter
    {θ A C : ℝ} {X₀ : ℕ} (hw : PrimeLevelWitness θ A C X₀)
    {H : Finset ℕ} {D : Finset (H → ℕ)} {R W v N : ℕ}
    (hW : 0 < W)
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
      modulusCutoff θ (N + h.1 - 1)) :
    |compatiblePairRestrictedErrorOuter H D R W v N lambda hD| ≤
      L ^ 2 * ((∑ h : H, (D.card * D.card * H.card : ℝ) *
        (C * ((2 * N + h.1 - 1 : ℕ) : ℝ) /
          Real.rpow (Real.log ((2 * N + h.1 - 1 : ℕ) : ℝ)) A)) +
      ∑ h : H, (D.card * D.card * H.card : ℝ) *
        (C * ((N + h.1 - 1 : ℕ) : ℝ) /
          Real.rpow (Real.log ((N + h.1 - 1 : ℕ) : ℝ)) A)) := by
  calc
    |compatiblePairRestrictedErrorOuter H D R W v N lambda hD| ≤
        compatiblePairRestrictedAbsoluteErrorOuter H D R W v N lambda hD :=
      abs_compatiblePairRestrictedErrorOuter_le_absoluteErrorOuter hD
    _ = compatiblePairShiftWeightedShiftedErrorSum H D R W v N lambda hD :=
      compatiblePairRestrictedAbsoluteErrorOuter_eq_weightedShiftedErrorSum hD
    _ ≤ _ := hw.bound_compatiblePairShiftWeightedShiftedErrorSum
      hW hD hcoverage hv lambda L hN hL hbound hupper hlower
      hcutUpper hcutLower

end BoundedGaps.Maynard
