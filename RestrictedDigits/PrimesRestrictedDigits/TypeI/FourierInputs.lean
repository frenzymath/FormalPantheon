import PrimesRestrictedDigits.Fourier.LargeSieveEstimates
import PrimesRestrictedDigits.Fourier.LInfBound

/-!
# Fourier inputs for the Type I estimate

These are source-shaped specializations of the repaired Lemmas 10.5 and 10.1 to
`MAYNARD-PRD-PUBLISHED`, Lemmas 8.1 and 8.2.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- Maynard's Lemma 8.1 at the fixed-length decimal scale, with an explicit
absolute constant and the exact weak denominator endpoint. -/
theorem typeILargeSieveEstimate
    (digit : Fin 10) (length : Nat) {Q : Real} (hQ : 1 <= Q) :
    (∑ pair ∈ reducedFractionCarrier (Nat.floor Q),
      normalizedPaddedDigitFourierMagnitudeAt digit length
        (reducedFractionValue pair)) <=
      largeSieveConstant *
        (Q ^ (54 / 77 : Real) + Q ^ 2 *
          (((10 ^ length : Nat) : Real) ^ (-(50 / 77 : Real)))) := by
  have h := reducedFractions_largeSieveEstimate
    digit length hQ (delta := 0) (by norm_num) 0
  simpa only [closedWindowMaximum_zero
      (normalizedPaddedDigitFourierMagnitudeAt_continuous digit length),
    add_zero, zero_mul, one_mul, mul_one, largeSieveSigma] using h

/-- Maynard's Lemma 8.2 with the repaired explicit positivity hypothesis and
absolute constants uniform in the omitted digit. -/
theorem typeILInfEstimate
    (digit : Fin 10) {length q q1 q2 : Nat} {a : Int} {eta : Real}
    (hq : q = q1 * q2) (hq2 : 0 < q2) (hq1 : 1 < q1)
    (hq10 : Nat.Coprime q1 10) (haq : Nat.Coprime a.natAbs q)
    (hqY : (q : Real) <
      (((10 ^ length : Nat) : Real) ^ (1 / 3 : Real)))
    (heta : |eta| <
      (((10 ^ length : Nat) : Real) ^ (-2 / 3 : Real)) / 2) :
    normalizedPaddedDigitFourierMagnitudeAt digit length
        ((a : Real) / q + eta) <=
      3 * Real.exp (-(1 / 100000000 : Real) *
        (Real.log (((10 ^ length : Nat) : Real)) / Real.log (q : Real))) := by
  exact normalizedPaddedDigitFourierMagnitudeAt_le_sourceDecay
    digit hq hq2 hq1 hq10 haq hqY heta

end PrimesRestrictedDigits
