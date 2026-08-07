import BoundedGaps.Maynard.ConcreteS2
import BoundedGaps.Maynard.ImprovedGPY.S2UniformWitness

/-!
# Explicit support-free concrete S2 envelope

This module removes the residual filtered-support cardinality from the
conditional S2 error estimate. The endpoint distribution and all cutoff
hypotheses remain conditional, as in the source-shaped theorem.
-/

namespace BoundedGaps.Maynard

open Filter

noncomputable def engelsmaMaynardSupportCardLogEnvelope
    (alpha : ℝ) (N : ℕ) : ℝ :=
  (engelsmaMaynardRadius alpha N : ℝ) *
    (1 + Real.log (engelsmaMaynardRadius alpha N)) ^
      Fintype.card BoundedGaps.engelsmaTuple

theorem engelsmaMaynardSupport_card_le_named_log_envelope
    {alpha : ℝ} (N : ℕ) :
    ((maynardSupportFamily BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha) engelsmaMaynardModulus N).card : ℝ) ≤
      engelsmaMaynardSupportCardLogEnvelope alpha N := by
  exact engelsmaMaynardSupport_card_le_log (alpha := alpha) N

theorem eventually_engelsmaMaynardS2_endpoint_cutoffs
    {theta delta : ℝ} (htheta : 0 ≤ theta) (hdelta : 0 < delta) :
    ∀ᶠ N : ℕ in atTop, ∀ h : BoundedGaps.engelsmaTuple,
      engelsmaMaynardModulus N * engelsmaMaynardRadius (theta / 2 - delta) N *
          engelsmaMaynardRadius (theta / 2 - delta) N ≤
          modulusCutoff theta (N + h.1 - 1) ∧
        engelsmaMaynardModulus N * engelsmaMaynardRadius (theta / 2 - delta) N *
            engelsmaMaynardRadius (theta / 2 - delta) N ≤
          modulusCutoff theta (2 * N + h.1 - 1) := by
  have hbase := eventually_engelsmaMaynard_modulus_radius_cutoff htheta hdelta
  filter_upwards [hbase] with N hN h
  refine ⟨hN h, ?_⟩
  have hshift := hN (N + h.1)
  rw [show N + (N + h.1) - 1 = 2 * N + h.1 - 1 by omega] at hshift
  exact hshift

theorem eventually_engelsmaMaynardS2_endpoint_thresholds
    (X₀ : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ h : BoundedGaps.engelsmaTuple,
      X₀ ≤ N + h.1 - 1 ∧ X₀ ≤ 2 * N + h.1 - 1 := by
  filter_upwards [eventually_ge_atTop (X₀ + 1)] with N hN h
  omega

set_option maxRecDepth 3000 in
theorem PrimeLevelWitness.bound_abs_engelsmaMaynardS2Error
    {theta alpha A C : ℝ} {X₀ : ℕ}
    (hw : PrimeLevelWitness theta A C X₀)
    (N : ℕ)
    (hcoverage : CoversShiftDifferencePrimes BoundedGaps.engelsmaTuple
      (engelsmaMaynardModulus N))
    (hN : 0 < N)
    (hupper : ∀ h : BoundedGaps.engelsmaTuple,
      X₀ ≤ 2 * N + h.1 - 1)
    (hlower : ∀ h : BoundedGaps.engelsmaTuple,
      X₀ ≤ N + h.1 - 1)
    (hcutUpper : ∀ h : BoundedGaps.engelsmaTuple,
      engelsmaMaynardModulus N * engelsmaMaynardRadius alpha N *
          engelsmaMaynardRadius alpha N ≤
        modulusCutoff theta (2 * N + h.1 - 1))
    (hcutLower : ∀ h : BoundedGaps.engelsmaTuple,
      engelsmaMaynardModulus N * engelsmaMaynardRadius alpha N *
          engelsmaMaynardRadius alpha N ≤
        modulusCutoff theta (N + h.1 - 1)) :
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
              Real.rpow (Real.log ((N + h.1 - 1 : ℕ) : ℝ)) A)) := by
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
  have herror := hw.bound_abs_compatiblePairRestrictedErrorOuter
    hW hD hcoverage hv lambda L hN hL hbound hupper hlower
      hcutUpper hcutLower
  simpa [engelsmaMaynardS2Error, D, lambda, L] using herror

set_option maxRecDepth 3000 in
theorem exists_engelsmaMaynardS2Error_conditional_explicit_envelope
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
              (engelsmaMaynardSupportCardLogEnvelope alpha N) ^ 2 *
                (BoundedGaps.engelsmaTuple.card : ℝ) *
                (C * ((2 * N + h.1 - 1 : ℕ) : ℝ) /
                  Real.rpow (Real.log ((2 * N + h.1 - 1 : ℕ) : ℝ)) A)) +
            ∑ h : BoundedGaps.engelsmaTuple,
              (engelsmaMaynardSupportCardLogEnvelope alpha N) ^ 2 *
                (BoundedGaps.engelsmaTuple.card : ℝ) *
                (C * ((N + h.1 - 1 : ℕ) : ℝ) /
                  Real.rpow (Real.log ((N + h.1 - 1 : ℕ) : ℝ)) A))) := by
  classical
  let D := maynardSupportFamily BoundedGaps.engelsmaTuple
    (engelsmaMaynardRadius alpha) engelsmaMaynardModulus N
  let B : ℝ := engelsmaMaynardSupportCardLogEnvelope alpha N
  obtain ⟨C, hC, X₀, hX₀, herror⟩ :=
    exists_engelsmaMaynardS2Error_conditional_envelope
      hlevel hA N hcoverage
  refine ⟨C, hC, X₀, hX₀, ?_⟩
  intro hN hupper hlower hcutUpper hcutLower
  have hbase := herror hN hupper hlower hcutUpper hcutLower
  have hcard : ((D.card : ℝ)) ≤ B := by
    dsimp [D, B]
    exact engelsmaMaynardSupport_card_le_named_log_envelope (alpha := alpha) N
  have hcardpow : (D.card : ℝ) ^ 2 ≤ B ^ 2 := by
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2
  have hfactor :
      ((D.card * D.card * BoundedGaps.engelsmaTuple.card : ℕ) : ℝ) ≤
        B ^ 2 * (BoundedGaps.engelsmaTuple.card : ℝ) := by
    simpa [Nat.cast_mul, pow_two, mul_assoc] using
      (mul_le_mul_of_nonneg_right hcardpow
        (by positivity : 0 ≤ (BoundedGaps.engelsmaTuple.card : ℝ)))
  have htermUpper : ∀ h : BoundedGaps.engelsmaTuple,
      ((D.card * D.card * BoundedGaps.engelsmaTuple.card : ℕ) : ℝ) *
          (C * ((2 * N + h.1 - 1 : ℕ) : ℝ) /
            Real.rpow (Real.log ((2 * N + h.1 - 1 : ℕ) : ℝ)) A) ≤
        (B ^ 2 * (BoundedGaps.engelsmaTuple.card : ℝ)) *
          (C * ((2 * N + h.1 - 1 : ℕ) : ℝ) /
            Real.rpow (Real.log ((2 * N + h.1 - 1 : ℕ) : ℝ)) A) := by
    intro h
    apply mul_le_mul_of_nonneg_right hfactor
    exact div_nonneg
      (mul_nonneg hC (by positivity))
      (Real.rpow_nonneg (by positivity) _)
  have htermLower : ∀ h : BoundedGaps.engelsmaTuple,
      ((D.card * D.card * BoundedGaps.engelsmaTuple.card : ℕ) : ℝ) *
          (C * ((N + h.1 - 1 : ℕ) : ℝ) /
            Real.rpow (Real.log ((N + h.1 - 1 : ℕ) : ℝ)) A) ≤
        (B ^ 2 * (BoundedGaps.engelsmaTuple.card : ℝ)) *
          (C * ((N + h.1 - 1 : ℕ) : ℝ) /
            Real.rpow (Real.log ((N + h.1 - 1 : ℕ) : ℝ)) A) := by
    intro h
    apply mul_le_mul_of_nonneg_right hfactor
    exact div_nonneg
      (mul_nonneg hC (by positivity))
      (Real.rpow_nonneg (by positivity) _)
  have hsumUpper :
      (∑ h : BoundedGaps.engelsmaTuple,
          ((D.card * D.card * BoundedGaps.engelsmaTuple.card : ℕ) : ℝ) *
            (C * ((2 * N + h.1 - 1 : ℕ) : ℝ) /
              Real.rpow (Real.log ((2 * N + h.1 - 1 : ℕ) : ℝ)) A)) ≤
        ∑ h : BoundedGaps.engelsmaTuple,
          (B ^ 2 * (BoundedGaps.engelsmaTuple.card : ℝ)) *
            (C * ((2 * N + h.1 - 1 : ℕ) : ℝ) /
              Real.rpow (Real.log ((2 * N + h.1 - 1 : ℕ) : ℝ)) A) := by
    apply Finset.sum_le_sum
    intro h _
    exact htermUpper h
  have hsumLower :
      (∑ h : BoundedGaps.engelsmaTuple,
          ((D.card * D.card * BoundedGaps.engelsmaTuple.card : ℕ) : ℝ) *
            (C * ((N + h.1 - 1 : ℕ) : ℝ) /
              Real.rpow (Real.log ((N + h.1 - 1 : ℕ) : ℝ)) A)) ≤
        ∑ h : BoundedGaps.engelsmaTuple,
          (B ^ 2 * (BoundedGaps.engelsmaTuple.card : ℝ)) *
            (C * ((N + h.1 - 1 : ℕ) : ℝ) /
              Real.rpow (Real.log ((N + h.1 - 1 : ℕ) : ℝ)) A) := by
    apply Finset.sum_le_sum
    intro h _
    exact htermLower h
  have hsum := add_le_add hsumUpper hsumLower
  have houter : 0 ≤
      ((engelsmaMaynardRadius alpha N : ℝ) * smallKCandidateBound *
        (1 + Real.log (engelsmaMaynardRadius alpha N)) ^
          (2 * Fintype.card BoundedGaps.engelsmaTuple)) ^ 2 :=
    sq_nonneg _
  calc
    |engelsmaMaynardS2Error alpha N| ≤
        ((engelsmaMaynardRadius alpha N : ℝ) * smallKCandidateBound *
          (1 + Real.log (engelsmaMaynardRadius alpha N)) ^
            (2 * Fintype.card BoundedGaps.engelsmaTuple)) ^ 2 *
          ((∑ h : BoundedGaps.engelsmaTuple,
              ((D.card * D.card * BoundedGaps.engelsmaTuple.card : ℕ) : ℝ) *
                (C * ((2 * N + h.1 - 1 : ℕ) : ℝ) /
                  Real.rpow (Real.log ((2 * N + h.1 - 1 : ℕ) : ℝ)) A)) +
            ∑ h : BoundedGaps.engelsmaTuple,
              ((D.card * D.card * BoundedGaps.engelsmaTuple.card : ℕ) : ℝ) *
                (C * ((N + h.1 - 1 : ℕ) : ℝ) /
                  Real.rpow (Real.log ((N + h.1 - 1 : ℕ) : ℝ)) A)) := by
      simpa [D] using hbase
    _ ≤
        ((engelsmaMaynardRadius alpha N : ℝ) * smallKCandidateBound *
          (1 + Real.log (engelsmaMaynardRadius alpha N)) ^
            (2 * Fintype.card BoundedGaps.engelsmaTuple)) ^ 2 *
          ((∑ h : BoundedGaps.engelsmaTuple,
              (B ^ 2 * (BoundedGaps.engelsmaTuple.card : ℝ)) *
                (C * ((2 * N + h.1 - 1 : ℕ) : ℝ) /
                  Real.rpow (Real.log ((2 * N + h.1 - 1 : ℕ) : ℝ)) A)) +
            ∑ h : BoundedGaps.engelsmaTuple,
              (B ^ 2 * (BoundedGaps.engelsmaTuple.card : ℝ)) *
                (C * ((N + h.1 - 1 : ℕ) : ℝ) /
                  Real.rpow (Real.log ((N + h.1 - 1 : ℕ) : ℝ)) A)) := by
      exact mul_le_mul_of_nonneg_left hsum houter
    _ =
        ((engelsmaMaynardRadius alpha N : ℝ) * smallKCandidateBound *
          (1 + Real.log (engelsmaMaynardRadius alpha N)) ^
            (2 * Fintype.card BoundedGaps.engelsmaTuple)) ^ 2 *
          ((∑ h : BoundedGaps.engelsmaTuple,
              (engelsmaMaynardSupportCardLogEnvelope alpha N) ^ 2 *
                (BoundedGaps.engelsmaTuple.card : ℝ) *
                (C * ((2 * N + h.1 - 1 : ℕ) : ℝ) /
                  Real.rpow (Real.log ((2 * N + h.1 - 1 : ℕ) : ℝ)) A)) +
            ∑ h : BoundedGaps.engelsmaTuple,
              (engelsmaMaynardSupportCardLogEnvelope alpha N) ^ 2 *
                (BoundedGaps.engelsmaTuple.card : ℝ) *
                (C * ((N + h.1 - 1 : ℕ) : ℝ) /
                  Real.rpow (Real.log ((N + h.1 - 1 : ℕ) : ℝ)) A)) := by
      simp [B, pow_two, mul_assoc]

end BoundedGaps.Maynard
