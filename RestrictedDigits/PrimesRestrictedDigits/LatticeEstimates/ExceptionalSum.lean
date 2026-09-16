import PrimesRestrictedDigits.Fourier.Moment235FractionalMoment
import PrimesRestrictedDigits.GenericMinorArcs.GenericFrequencyBounds
import PrimesRestrictedDigits.LatticeEstimates.ApproximationCount

/-!
# Exceptional-frequency sum in the lattice estimate

This file defines the literal `S3` sum from published Lemma 14.3 and combines the repaired
approximation count with the exact exceptional first mass.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

/-- The literal exceptional-frequency sum `S3`. The continuous transform is
evaluated at the source ratio; its exact discrete-grid identity is used only
in the proof. -/
noncomputable def latticeSThree
    (digit : Fin 10) (length d Q G E : Nat) : Real :=
  ∑ a ∈ genericExceptionalFrequencies digit length,
    normalizedPaddedDigitFourierMagnitudeAt digit length
        ((a.val : Real) / ((10 ^ length : Nat) : Real)) *
      (latticeApproximationCount length a d Q G E : Real)

theorem latticeSThree_nonneg
    (digit : Fin 10) (length d Q G E : Nat) :
    0 <= latticeSThree digit length d Q G E := by
  unfold latticeSThree
  exact Finset.sum_nonneg fun a _ =>
    mul_nonneg
      (normalizedPaddedDigitFourierMagnitudeAt_nonneg digit length _)
      (Nat.cast_nonneg _)

private theorem latticeExceptionalContinuousSum_eq_gridSum
    (digit : Fin 10) (length : Nat) :
    (∑ a ∈ genericExceptionalFrequencies digit length,
      normalizedPaddedDigitFourierMagnitudeAt digit length
        ((a.val : Real) / ((10 ^ length : Nat) : Real))) =
      ∑ a ∈ genericExceptionalFrequencies digit length,
        normalizedPaddedDigitFourierMagnitude digit length a.val := by
  apply Finset.sum_congr rfl
  intro a ha
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    normalizedPaddedDigitFourierMagnitudeAt_grid digit length a.val

/-- The sharp all-length `S3` estimate before the source-scale substitutions.
The exceptional saving is the exact coefficient-one consequence of the
kernel-checked `235/154` moment certificate. -/
theorem exists_latticeSThree_le_generic (rho : Real) (hrho : 0 < rho) :
    ∃ C : Real, 0 < C ∧
      ∀ (digit : Fin 10) (length d Q G E : Nat),
        0 < d -> 0 < Q -> 0 < G ->
        latticeSThree digit length d Q G E <=
          C * (((Q * G : Nat) : Real) ^ rho) *
            (1 + ((E * d * Q ^ 2 * G ^ 2 : Nat) : Real) /
              ((10 ^ length : Nat) : Real)) *
            (((10 ^ length : Nat) : Real) ^
              ((23 / 80 : Real) - 127 / 5334560)) := by
  obtain ⟨C, hC, hcount⟩ :=
    exists_latticeApproximationCount_le rho hrho
  refine ⟨C, hC, ?_⟩
  intro digit length d Q G E hd hQ hG
  let coefficient : Real :=
    C * (((Q * G : Nat) : Real) ^ rho) *
      (1 + ((E * d * Q ^ 2 * G ^ 2 : Nat) : Real) /
        ((10 ^ length : Nat) : Real))
  have hcoefficient : 0 <= coefficient := by
    dsimp only [coefficient]
    positivity
  have hpointwise (a : Fin (10 ^ length)) :
      normalizedPaddedDigitFourierMagnitudeAt digit length
          ((a.val : Real) / ((10 ^ length : Nat) : Real)) *
          (latticeApproximationCount length a d Q G E : Real) <=
        normalizedPaddedDigitFourierMagnitudeAt digit length
          ((a.val : Real) / ((10 ^ length : Nat) : Real)) * coefficient := by
    apply mul_le_mul_of_nonneg_left
    · simpa only [coefficient] using hcount length a d Q G E hd hQ hG
    · exact normalizedPaddedDigitFourierMagnitudeAt_nonneg digit length _
  have hmoment := positiveMomentFrequencySum_fractional_le digit length
  have hmass := sum_genericExceptionalFrequencies_le
    digit length (1 : Real) (by simpa using hmoment)
  unfold latticeSThree
  calc
    (∑ a ∈ genericExceptionalFrequencies digit length,
      normalizedPaddedDigitFourierMagnitudeAt digit length
          ((a.val : Real) / ((10 ^ length : Nat) : Real)) *
        (latticeApproximationCount length a d Q G E : Real)) <=
        ∑ a ∈ genericExceptionalFrequencies digit length,
          normalizedPaddedDigitFourierMagnitudeAt digit length
            ((a.val : Real) / ((10 ^ length : Nat) : Real)) * coefficient := by
      exact Finset.sum_le_sum fun a ha => hpointwise a
    _ = coefficient *
        (∑ a ∈ genericExceptionalFrequencies digit length,
          normalizedPaddedDigitFourierMagnitudeAt digit length
            ((a.val : Real) / ((10 ^ length : Nat) : Real))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = coefficient *
        (∑ a ∈ genericExceptionalFrequencies digit length,
          normalizedPaddedDigitFourierMagnitude digit length a.val) := by
      rw [latticeExceptionalContinuousSum_eq_gridSum]
    _ <= coefficient *
        (((10 ^ length : Nat) : Real) ^
          ((23 / 80 : Real) - 127 / 5334560)) := by
      apply mul_le_mul_of_nonneg_left
      simpa only [one_mul] using hmass
      exact hcoefficient
    _ = C * (((Q * G : Nat) : Real) ^ rho) *
        (1 + ((E * d * Q ^ 2 * G ^ 2 : Nat) : Real) /
          ((10 ^ length : Nat) : Real)) *
        (((10 ^ length : Nat) : Real) ^
          ((23 / 80 : Real) - 127 / 5334560)) := by
      rfl

end

end PrimesRestrictedDigits
