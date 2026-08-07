import BoundedGaps.Maynard.ConcreteS2Bounds

/-!
# Uniform support-free concrete S2 error bound

This module combines the fixed distribution witness with the explicit
radius/logarithm support envelope for the frozen Engelsma family.
-/

namespace BoundedGaps.Maynard

open Filter

set_option maxRecDepth 3000 in
theorem PrimeLevelWitness.bound_abs_engelsmaMaynardS2Error_explicit
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
          (engelsmaMaynardSupportCardLogEnvelope alpha N) ^ 2 *
            (BoundedGaps.engelsmaTuple.card : ℝ) *
            (C * ((2 * N + h.1 - 1 : ℕ) : ℝ) /
              Real.rpow (Real.log ((2 * N + h.1 - 1 : ℕ) : ℝ)) A)) +
        ∑ h : BoundedGaps.engelsmaTuple,
          (engelsmaMaynardSupportCardLogEnvelope alpha N) ^ 2 *
            (BoundedGaps.engelsmaTuple.card : ℝ) *
            (C * ((N + h.1 - 1 : ℕ) : ℝ) /
              Real.rpow (Real.log ((N + h.1 - 1 : ℕ) : ℝ)) A)) := by
  classical
  let D := maynardSupportFamily BoundedGaps.engelsmaTuple
    (engelsmaMaynardRadius alpha) engelsmaMaynardModulus N
  let B : ℝ := engelsmaMaynardSupportCardLogEnvelope alpha N
  have hbase := hw.bound_abs_engelsmaMaynardS2Error N hcoverage hN
    hupper hlower hcutUpper hcutLower
  have hcard : (D.card : ℝ) ≤ B := by
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
      (mul_nonneg hw.1 (by positivity))
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
      (mul_nonneg hw.1 (by positivity))
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
    _ = _ := by
      simp [B, pow_two, mul_assoc]

end BoundedGaps.Maynard
