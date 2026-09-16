import PrimesRestrictedDigits.GenericMinorArcs.DirectComplementary
import PrimesRestrictedDigits.GenericMinorArcs.PrimeTupleL2

/-!
# Direct eta-uniform complementary region decay

This inserts the normalized-log region coefficient into the global direct
source-decay estimate for Lemma 12.2 of `MAYNARD-PRD-PUBLISHED`.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- The direct strict-complement decay with the eta-uniform normalized-region
coefficient cap inserted explicitly. -/
theorem sum_sourceSmallNormalizedMagnitude_mul_normalizedLogRegion_norm_div_le
    (a : Fin 10) (length ell : Nat) (hX : 4 <= 10 ^ length)
    {eta : Real} (_heta : 0 < eta) (hell : (ell : Real) <= 2 / eta)
    (region : Set (Fin ell -> Real))
    (frequencies : Finset (Fin (10 ^ length))) (K : Real) (hK : 0 <= K)
    (hsmall : ∀ h ∈ frequencies,
      normalizedPaddedDigitFourierMagnitude a length h.val <
        (((10 ^ length : Nat) : Real) ^ (-(23 / 80 : Real))))
    (hmoment : (∑ h : Fin (10 ^ length),
      normalizedPaddedDigitFourierMagnitude a length h.val ^
        (235 / 154 : Real)) <=
      K * (((10 ^ length : Nat) : Real) ^ (59 / 433 : Real))) :
    (∑ h ∈ frequencies,
      normalizedPaddedDigitFourierMagnitude a length h.val *
        ‖majorArcWeightedPhaseSum (Finset.range (10 ^ length))
          (fun n => (normalizedLogRegionWeightAtProduct
            (10 ^ length) region n : Complex))
          (-((h.val : Real) / ((10 ^ length : Nat) : Real)))‖) /
        ((10 ^ length : Nat) : Real) <=
      Real.sqrt K *
        ((Nat.factorial (Nat.ceil (2 / eta)) : Real) *
          Real.log (((10 ^ length : Nat) : Real)) ^ Nat.ceil (2 / eta)) /
        (((10 ^ length : Nat) : Real) ^ (127 / 10669120 : Real)) := by
  let L : Real :=
    (Nat.factorial (Nat.ceil (2 / eta)) : Real) *
      Real.log (((10 ^ length : Nat) : Real)) ^ Nat.ceil (2 / eta)
  have hL : 0 <= L := by
    dsimp only [L]
    positivity
  have hcoeff : ∀ n ∈ Finset.range (10 ^ length),
      ‖(normalizedLogRegionWeightAtProduct
        (10 ^ length) region n : Complex)‖ <= L := by
    intro n hn
    have hnonneg : 0 <=
        normalizedLogRegionWeightAtProduct (10 ^ length) region n := by
      unfold normalizedLogRegionWeightAtProduct
      exact primeTupleWeightAtProduct_nonneg _ _
    rw [Complex.norm_real, Real.norm_of_nonneg hnonneg]
    exact (normalizedLogRegionWeightAtProduct_le_factorial_mul_log_pow
      (10 ^ length) n region (Finset.mem_range.mp hn)).trans
        (factorial_mul_log_pow_le_arityCeil hX hell)
  have hresult :=
    sum_sourceSmallNormalizedMagnitude_mul_weightedPhase_norm_div_le
      a length
        (fun n => (normalizedLogRegionWeightAtProduct
          (10 ^ length) region n : Complex))
        frequencies K L hK hL hsmall hmoment hcoeff
  simpa only [L] using hresult

end PrimesRestrictedDigits
