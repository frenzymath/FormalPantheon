import PrimesRestrictedDigits.Fourier.FirstMomentCertificateBridge
import PrimesRestrictedDigits.Fourier.FirstMomentCertificateCheckedRows

/-!
# Unconditional exact first-moment bounds

The finite data and 25,000 lower-half rows are checked by ordinary kernel reduction; proved
reflection supplies all 50,000 rows.
-/

namespace PrimesRestrictedDigits

theorem digitWordPathSum_firstMoment_le
    (digit : Fin 10) (length : Nat) (future : DigitWindowState 4) :
    digitWordPathSum
        (poweredWindowMajorantWeight digit 4 1)
        length future <=
      2 * (((10 ^ length : Nat) : Real) ^ (27 / 77 : Real)) :=
  digitWordPathSum_firstMoment_le_of_indexedRows
    firstMomentIndexedRows digit length future

theorem firstMomentFrequencySum_le
    (digit : Fin 10) (length : Nat) :
    (∑ frequency : Fin (10 ^ length),
      normalizedPaddedDigitFourierMagnitude
        digit length frequency.val) <=
      2 * (((10 ^ length : Nat) : Real) ^ (27 / 77 : Real)) :=
  firstMomentFrequencySum_le_of_indexedRows
    firstMomentIndexedRows digit length

end PrimesRestrictedDigits
