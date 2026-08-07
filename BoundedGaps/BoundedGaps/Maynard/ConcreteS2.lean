import BoundedGaps.Maynard.ConcreteS1
import BoundedGaps.Maynard.ImprovedGPY.S2ActualError

/-!
# Concrete S2 decomposition

This module instantiates the finite prime-weighted pair expansion and the
restricted main/error split from Maynard2013v3, Section 5
(`lmm:S2Expression1`, source lines 339--370).
-/

namespace BoundedGaps.Maynard

open Filter Set

set_option maxRecDepth 2000 in
theorem engelsmaMaynardS2SupportProof
    (alpha : ℝ) (N : ℕ) :
    ∀ d ∈ maynardSupportFamily BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha) engelsmaMaynardModulus N,
      IsMaynardDivisorTuple BoundedGaps.engelsmaTuple
        (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N) d := by
  classical
  intro d hd
  unfold maynardSupportFamily at hd
  unfold maynardDivisorTupleSupport at hd
  exact (Finset.mem_filter.mp hd).2

noncomputable def engelsmaMaynardS2Main (alpha : ℝ) (N : ℕ) : ℝ :=
  compatiblePairRestrictedMainOuter BoundedGaps.engelsmaTuple
    (maynardSupportFamily BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha) engelsmaMaynardModulus N)
    (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N)
    (engelsmaPreSieveResidue N) N
    (maynardCoefficientFamily BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha) engelsmaMaynardModulus
      engelsmaSmallKCandidate N)
    (engelsmaMaynardS2SupportProof alpha N)

noncomputable def engelsmaMaynardS2Error (alpha : ℝ) (N : ℕ) : ℝ :=
  compatiblePairRestrictedErrorOuter BoundedGaps.engelsmaTuple
    (maynardSupportFamily BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha) engelsmaMaynardModulus N)
    (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N)
    (engelsmaPreSieveResidue N) N
    (maynardCoefficientFamily BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha) engelsmaMaynardModulus
      engelsmaSmallKCandidate N)
    (engelsmaMaynardS2SupportProof alpha N)

theorem eventually_engelsmaMaynardS2_eq_main_add_error
    {theta delta : ℝ} (hthetaHalf : theta < 1 / 2)
    (hdelta : 0 < delta) (hdeltaTheta : delta < theta / 2) :
    ∀ᶠ N : ℕ in atTop,
      primeWeightedSieveSum BoundedGaps.engelsmaTuple N
        (maynardPreSievedWeightFamily BoundedGaps.engelsmaTuple
          (engelsmaMaynardRadius (theta / 2 - delta))
          engelsmaMaynardModulus engelsmaPreSieveResidue
          engelsmaSmallKCandidate N) =
        engelsmaMaynardS2Main (theta / 2 - delta) N +
          engelsmaMaynardS2Error (theta / 2 - delta) N := by
  filter_upwards [eventually_engelsmaMaynard_coverage,
    eventually_engelsmaMaynardRadius_le hthetaHalf hdelta hdeltaTheta] with
    N hcoverage hRN
  have hD := engelsmaMaynardS2SupportProof (theta / 2 - delta) N
  change primeWeightedSieveSum BoundedGaps.engelsmaTuple N
      (preSievedSquareDivisorWeight BoundedGaps.engelsmaTuple
        (maynardSupportFamily BoundedGaps.engelsmaTuple
          (engelsmaMaynardRadius (theta / 2 - delta))
          engelsmaMaynardModulus N)
        (maynardCoefficientFamily BoundedGaps.engelsmaTuple
          (engelsmaMaynardRadius (theta / 2 - delta))
          engelsmaMaynardModulus engelsmaSmallKCandidate N)
        (engelsmaPreSieveResidue N) (engelsmaMaynardModulus N)) = _
  rw [primeWeightedSieveSum_preSieved_eq_compatiblePrimeWeightedPairSum
    hD hcoverage]
  rw [compatiblePrimeWeightedPairSum_eq_restrictedOuterMain_addError
    hD hRN]
  rfl

theorem tendsto_engelsmaMaynardS2_of_main_error
    {theta delta I : ℝ} (hthetaHalf : theta < 1 / 2)
    (hdelta : 0 < delta) (hdeltaTheta : delta < theta / 2)
    (hmain : Tendsto
      (fun N : ℕ => engelsmaMaynardS2Main (theta / 2 - delta) N /
        engelsmaMaynardScale (theta / 2 - delta) N)
      atTop (nhds I))
    (herror : Tendsto
      (fun N : ℕ => engelsmaMaynardS2Error (theta / 2 - delta) N /
        engelsmaMaynardScale (theta / 2 - delta) N)
      atTop (nhds 0)) :
    Tendsto
      (fun N : ℕ => primeWeightedSieveSum BoundedGaps.engelsmaTuple N
        (maynardPreSievedWeightFamily BoundedGaps.engelsmaTuple
          (engelsmaMaynardRadius (theta / 2 - delta))
          engelsmaMaynardModulus engelsmaPreSieveResidue
          engelsmaSmallKCandidate N) /
            engelsmaMaynardScale (theta / 2 - delta) N)
      atTop (nhds I) := by
  have hdiff : Tendsto
      (fun N : ℕ =>
        (primeWeightedSieveSum BoundedGaps.engelsmaTuple N
          (maynardPreSievedWeightFamily BoundedGaps.engelsmaTuple
            (engelsmaMaynardRadius (theta / 2 - delta))
            engelsmaMaynardModulus engelsmaPreSieveResidue
            engelsmaSmallKCandidate N) -
          engelsmaMaynardS2Main (theta / 2 - delta) N) /
            engelsmaMaynardScale (theta / 2 - delta) N)
      atTop (nhds 0) := by
    apply herror.congr'
    filter_upwards [eventually_engelsmaMaynardS2_eq_main_add_error
      hthetaHalf hdelta hdeltaTheta] with N hN
    rw [hN]
    ring
  apply tendsto_normalized_sum_of_error
    (main := engelsmaMaynardS2Main (theta / 2 - delta))
    (scale := engelsmaMaynardScale (theta / 2 - delta))
  · exact (eventually_engelsmaMaynardScale_pos
      (sub_pos.mpr hdeltaTheta)).mono (fun _ h => ne_of_gt h)
  · exact hmain
  · exact hdiff

set_option maxRecDepth 2000 in
theorem exists_engelsmaMaynardS2Error_conditional_envelope
    {theta alpha A : ℝ} (hlevel : hasPrimeLevel theta) (hA : 0 < A)
    (N : ℕ)
    (hcoverage : CoversShiftDifferencePrimes BoundedGaps.engelsmaTuple
      (engelsmaMaynardModulus N)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, 3 ≤ X₀ ∧
      (0 < N →
        (∀ h : BoundedGaps.engelsmaTuple,
          X₀ ≤ 2 * N + h.1 - 1) →
        (∀ h : BoundedGaps.engelsmaTuple,
          X₀ ≤ N + h.1 - 1) →
        (∀ h : BoundedGaps.engelsmaTuple,
          engelsmaMaynardModulus N * engelsmaMaynardRadius alpha N *
              engelsmaMaynardRadius alpha N ≤
            modulusCutoff theta (2 * N + h.1 - 1)) →
        (∀ h : BoundedGaps.engelsmaTuple,
          engelsmaMaynardModulus N * engelsmaMaynardRadius alpha N *
              engelsmaMaynardRadius alpha N ≤
            modulusCutoff theta (N + h.1 - 1)) →
        |engelsmaMaynardS2Error alpha N| ≤
          ((engelsmaMaynardRadius alpha N : ℝ) * smallKCandidateBound *
            (1 + Real.log (engelsmaMaynardRadius alpha N)) ^
              (2 * Fintype.card BoundedGaps.engelsmaTuple)) ^ 2 *
            ((∑ h : BoundedGaps.engelsmaTuple,
              ((maynardSupportFamily BoundedGaps.engelsmaTuple
                (engelsmaMaynardRadius alpha) engelsmaMaynardModulus N).card *
                (maynardSupportFamily BoundedGaps.engelsmaTuple
                  (engelsmaMaynardRadius alpha) engelsmaMaynardModulus N).card *
                BoundedGaps.engelsmaTuple.card : ℝ) *
                (C * ((2 * N + h.1 - 1 : ℕ) : ℝ) /
                  Real.rpow (Real.log ((2 * N + h.1 - 1 : ℕ) : ℝ)) A)) +
            ∑ h : BoundedGaps.engelsmaTuple,
              ((maynardSupportFamily BoundedGaps.engelsmaTuple
                (engelsmaMaynardRadius alpha) engelsmaMaynardModulus N).card *
                (maynardSupportFamily BoundedGaps.engelsmaTuple
                  (engelsmaMaynardRadius alpha) engelsmaMaynardModulus N).card *
                BoundedGaps.engelsmaTuple.card : ℝ) *
                (C * ((N + h.1 - 1 : ℕ) : ℝ) /
                  Real.rpow (Real.log ((N + h.1 - 1 : ℕ) : ℝ)) A))) := by
  classical
  let D := maynardSupportFamily BoundedGaps.engelsmaTuple
    (engelsmaMaynardRadius alpha) engelsmaMaynardModulus N
  let lambda := maynardCoefficientFamily BoundedGaps.engelsmaTuple
    (engelsmaMaynardRadius alpha) engelsmaMaynardModulus
    engelsmaSmallKCandidate N
  let L : ℝ := (engelsmaMaynardRadius alpha N : ℝ) * smallKCandidateBound *
    (1 + Real.log (engelsmaMaynardRadius alpha N)) ^
      (2 * Fintype.card BoundedGaps.engelsmaTuple)
  have hD : ∀ d ∈ D,
      IsMaynardDivisorTuple BoundedGaps.engelsmaTuple
        (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N) d := by
    intro d hd
    exact engelsmaMaynardS2SupportProof alpha N d (by simpa [D] using hd)
  have hW : 0 < engelsmaMaynardModulus N := primorial_pos _
  have hL : 0 ≤ L := by
    dsimp [L]
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) smallKCandidateBound_nonneg)
      (by positivity)
  have hbound : ∀ d ∈ D, |lambda d| ≤ L := by
    intro d hd
    exact abs_engelsmaMaynardCoefficient_le_log_envelope (alpha := alpha) N
      (by simpa [D] using hd)
  have hv : ∀ h ∈ BoundedGaps.engelsmaTuple,
      Nat.Coprime (engelsmaPreSieveResidue N + h)
        (engelsmaMaynardModulus N) := by
    intro h hh
    exact engelsmaPreSieveResidue_coprime N hh
  obtain ⟨C, hC, X₀, hX₀, herror⟩ :=
    abs_compatiblePairRestrictedErrorOuter_le_conditionalShiftedError
      hlevel A hA hW hD hcoverage hv lambda L hL hbound
  refine ⟨C, hC, X₀, hX₀, ?_⟩
  intro hN hupper hlower hcutUpper hcutLower
  have hN' := herror N hN hupper hlower hcutUpper hcutLower
  simpa [engelsmaMaynardS2Error, D, lambda, L] using hN'

end BoundedGaps.Maynard
