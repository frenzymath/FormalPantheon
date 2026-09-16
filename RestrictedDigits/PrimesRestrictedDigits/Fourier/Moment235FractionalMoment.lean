import PrimesRestrictedDigits.Fourier.Moment235CertificateCheckedRows
import PrimesRestrictedDigits.Fourier.Moment235FractionalMomentBridge

/-!
# Unconditional complete-grid fractional moment

This is the repaired, exact certificate form of `MAYNARD-PRD-PUBLISHED`, Lemma 10.2, pp.
170--173, under the statements.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- The coefficient-one `235/154` complete decimal-grid moment estimate. -/
theorem positiveMomentFrequencySum_fractional_le
    (a : Fin 10) (length : Nat) :
    (∑ frequency : Fin (10 ^ length),
      normalizedPaddedDigitFourierMagnitude a length frequency.val ^
        (235 / 154 : Real)) <=
      (((10 ^ length : Nat) : Real) ^ (59 / 433 : Real)) :=
  positiveMomentFrequencySum_le_moment235_of_indexedRows
    moment235IndexedRows a length

end PrimesRestrictedDigits
