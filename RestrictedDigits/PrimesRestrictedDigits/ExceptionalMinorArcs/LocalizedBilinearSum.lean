import PrimesRestrictedDigits.ExceptionalMinorArcs.SplitProductCoordinateFibers
import PrimesRestrictedDigits.ExceptionalMinorArcs.RationalBandCover
import PrimesRestrictedDigits.ExceptionalMinorArcs.BilinearSum

/-!
# Canonically localized exceptional bilinear sums

This file gives the exact zero-mask bridge from the disjoint rational and product fibers to
the source intervals of repaired Lemma 13.1.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- Extend a coefficient on one product-coordinate fiber by zero. -/
def splitProductCoordinateMask
    (length i : Nat) (alpha : Nat → Complex) (n : Nat) : Complex :=
  if n ∈ splitProductCoordinateFiber length i then alpha n else 0

/-- Extend a frequency coefficient on one canonical rational fiber by zero. -/
def exceptionalDirichletBandMask
    {length : Nat} (S : Finset (Fin (10 ^ length))) (key : Nat × Nat)
    (gamma : Fin (10 ^ length) → Complex)
    (h : Fin (10 ^ length)) : Complex :=
  if h ∈ exceptionalDirichletBandFiber S key then gamma h else 0

/-- The bilinear sum on one disjoint rational-band and two-product cell. -/
def localizedExceptionalBilinearSum
    (digit : Fin 10) (length : Nat)
    (S : Finset (Fin (10 ^ length)))
    (bandKey productKey : Nat × Nat)
    (alpha beta : Nat → Complex)
    (gamma : Fin (10 ^ length) → Complex) : Complex :=
  ∑ h ∈ exceptionalDirichletBandFiber S bandKey,
    ∑ n ∈ splitProductCoordinateFiber length productKey.1,
      ∑ m ∈ splitProductCoordinateFiber length productKey.2,
        (normalizedPaddedDigitFourierMagnitude
            digit length h.val : Complex) *
          alpha n * beta m * gamma h *
            majorArcPhase
              (-((h.val : Real) * (n : Real) * (m : Real) /
                ((10 ^ length : Nat) : Real)))

theorem norm_splitProductCoordinateMask_le_one
    {length i : Nat} {alpha : Nat → Complex}
    (halpha : ∀ n ∈ splitProductCoordinateFiber length i,
      ‖alpha n‖ ≤ 1) (n : Nat) :
    ‖splitProductCoordinateMask length i alpha n‖ ≤ 1 := by
  by_cases hn : n ∈ splitProductCoordinateFiber length i
  · simpa [splitProductCoordinateMask, hn] using halpha n hn
  · simp [splitProductCoordinateMask, hn]

theorem norm_exceptionalDirichletBandMask_le_one
    {length : Nat} {S : Finset (Fin (10 ^ length))} {key : Nat × Nat}
    {gamma : Fin (10 ^ length) → Complex}
    (hgamma : ∀ h ∈ exceptionalDirichletBandFiber S key,
      ‖gamma h‖ ≤ 1) (h : Fin (10 ^ length)) :
    ‖exceptionalDirichletBandMask S key gamma h‖ ≤ 1 := by
  by_cases hh : h ∈ exceptionalDirichletBandFiber S key
  · simpa [exceptionalDirichletBandMask, hh] using hgamma h hh
  · simp [exceptionalDirichletBandMask, hh]

/-- A canonical rational fiber inside the high-Fourier carrier is contained
in the frequency carrier of repaired Lemma 13.1. -/
theorem exceptionalDirichletBandFiber_subset_exceptionalRationalFrequencies
    {digit : Fin 10} {length : Nat} (hlength : 0 < length)
    {S : Finset (Fin (10 ^ length))} {key : Nat × Nat}
    (hS : S ⊆ genericExceptionalFrequencies digit length) :
    exceptionalDirichletBandFiber S key ⊆
      exceptionalRationalFrequencies digit length
        (exceptionalDirichletDenominatorScaleAt (10 ^ length) key.1)
        (exceptionalDirichletErrorScaleAt (10 ^ length) key.2) := by
  intro h hh
  rw [mem_exceptionalRationalFrequencies_iff]
  exact ⟨mem_latticeRationalApproximationBand_of_mem_fiber hlength hh,
    hS (mem_exceptionalDirichletBandFiber_iff.mp hh).1⟩

/-- Zero masking turns the source-facing bilinear sum into exactly one
canonical rational/product cell. -/
theorem localizedExceptionalBilinearSum_eq_exceptionalBilinearSum
    {digit : Fin 10} {length : Nat} (hlength : 0 < length)
    {S : Finset (Fin (10 ^ length))} {bandKey productKey : Nat × Nat}
    {alpha beta : Nat → Complex}
    {gamma : Fin (10 ^ length) → Complex}
    (hS : S ⊆ genericExceptionalFrequencies digit length) :
    localizedExceptionalBilinearSum digit length S bandKey productKey
        alpha beta gamma =
      exceptionalBilinearSum digit length
        (splitProductScaleAt productKey.1)
        (splitProductScaleAt productKey.2)
        (exceptionalDirichletDenominatorScaleAt
          (10 ^ length) bandKey.1)
        (exceptionalDirichletErrorScaleAt (10 ^ length) bandKey.2)
        (splitProductCoordinateMask length productKey.1 alpha)
        (splitProductCoordinateMask length productKey.2 beta)
        (exceptionalDirichletBandMask S bandKey gamma) := by
  let A := exceptionalDirichletBandFiber S bandKey
  let F := exceptionalRationalFrequencies digit length
    (exceptionalDirichletDenominatorScaleAt (10 ^ length) bandKey.1)
    (exceptionalDirichletErrorScaleAt (10 ^ length) bandKey.2)
  let N := splitProductCoordinateFiber length productKey.1
  let N' := sourceFactorTenNaturalInterval
    (splitProductScaleAt productKey.1)
  let M := splitProductCoordinateFiber length productKey.2
  let M' := sourceFactorTenNaturalInterval
    (splitProductScaleAt productKey.2)
  have hAF : A ⊆ F :=
    exceptionalDirichletBandFiber_subset_exceptionalRationalFrequencies
      hlength hS
  have hNN : N ⊆ N' := by
    intro n hn
    exact splitProductCoordinateFiber_mem_sourceInterval hn
  have hMM : M ⊆ M' := by
    intro m hm
    exact splitProductCoordinateFiber_mem_sourceInterval hm
  unfold localizedExceptionalBilinearSum exceptionalBilinearSum
  change (∑ h ∈ A, ∑ n ∈ N, ∑ m ∈ M, _) =
    ∑ h ∈ F, ∑ n ∈ N', ∑ m ∈ M', _
  have hmasks (h : Fin (10 ^ length)) (n m : Nat)
      (hh : h ∈ A) (hn : n ∈ N) (hm : m ∈ M) :
      (normalizedPaddedDigitFourierMagnitude digit length h.val : Complex) *
          alpha n * beta m * gamma h *
            majorArcPhase
              (-((h.val : Real) * (n : Real) * (m : Real) /
                ((10 ^ length : Nat) : Real))) =
        (normalizedPaddedDigitFourierMagnitude digit length h.val : Complex) *
          splitProductCoordinateMask length productKey.1 alpha n *
            splitProductCoordinateMask length productKey.2 beta m *
              exceptionalDirichletBandMask S bandKey gamma h *
                majorArcPhase
                  (-((h.val : Real) * (n : Real) * (m : Real) /
                    ((10 ^ length : Nat) : Real))) := by
    simp [splitProductCoordinateMask, exceptionalDirichletBandMask,
      A, N, M, hh, hn, hm]
  apply Finset.sum_subset_zero_on_sdiff hAF
  · intro h hh
    have hhA : h ∉ A := (Finset.mem_sdiff.mp hh).2
    simp [exceptionalDirichletBandMask, A, hhA]
  · intro h hhA
    apply Finset.sum_subset_zero_on_sdiff hNN
    · intro n hn
      have hnN : n ∉ N := (Finset.mem_sdiff.mp hn).2
      simp [splitProductCoordinateMask, N, hnN]
    · intro n hnN
      apply Finset.sum_subset_zero_on_sdiff hMM
      · intro m hm
        have hmM : m ∉ M := (Finset.mem_sdiff.mp hm).2
        simp [splitProductCoordinateMask, M, hmM]
      · intro m hmM
        exact hmasks h n m hhA hnN hmM

/-- Commuting the two coordinate sums swaps the product key and coefficient
sequences without changing the multiplicative phase. -/
theorem localizedExceptionalBilinearSum_swap
    (digit : Fin 10) (length : Nat)
    (S : Finset (Fin (10 ^ length))) (bandKey productKey : Nat × Nat)
    (alpha beta : Nat → Complex)
    (gamma : Fin (10 ^ length) → Complex) :
    localizedExceptionalBilinearSum digit length S bandKey productKey
        alpha beta gamma =
      localizedExceptionalBilinearSum digit length S bandKey productKey.swap
        beta alpha gamma := by
  rcases productKey with ⟨i, j⟩
  unfold localizedExceptionalBilinearSum
  apply Finset.sum_congr rfl
  intro h hh
  simp only [Prod.swap_prod_mk]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  · ring
  · congr 2
    push_cast
    ring

end

end PrimesRestrictedDigits
