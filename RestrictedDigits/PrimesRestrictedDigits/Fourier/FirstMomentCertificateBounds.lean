import PrimesRestrictedDigits.Fourier.FirstMomentCertificateData
import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentMinimumDigit0
import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentMinimumDigit1
import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentMinimumDigit2
import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentMinimumDigit3
import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentMinimumDigit4
import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentMaximumDigit0
import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentMaximumDigit1
import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentMaximumDigit2
import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentMaximumDigit3
import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentMaximumDigit4
import Mathlib.Tactic.FinCases

/-! Uniform lower and upper bounds for the five exact first-moment vectors. -/

namespace PrimesRestrictedDigits

theorem firstMomentVectorScale_le
    (a : Fin 5) (state : Fin 10000) :
    firstMomentVectorScale a <= firstMomentVectorNumerator a state := by
  fin_cases a
  · simpa [firstMomentVectorScale, firstMomentVectorNumerator] using
      firstMomentVectorScaleDigit0_le state
  · simpa [firstMomentVectorScale, firstMomentVectorNumerator] using
      firstMomentVectorScaleDigit1_le state
  · simpa [firstMomentVectorScale, firstMomentVectorNumerator] using
      firstMomentVectorScaleDigit2_le state
  · simpa [firstMomentVectorScale, firstMomentVectorNumerator] using
      firstMomentVectorScaleDigit3_le state
  · simpa [firstMomentVectorScale, firstMomentVectorNumerator] using
      firstMomentVectorScaleDigit4_le state

theorem firstMomentVectorNumerator_le_maximum
    (a : Fin 5) (state : Fin 10000) :
    firstMomentVectorNumerator a state <=
      firstMomentCertificateVectorMaximum := by
  fin_cases a
  · simpa [firstMomentVectorNumerator] using
      firstMomentVectorNumeratorDigit0_le_maximum state
  · simpa [firstMomentVectorNumerator] using
      firstMomentVectorNumeratorDigit1_le_maximum state
  · simpa [firstMomentVectorNumerator] using
      firstMomentVectorNumeratorDigit2_le_maximum state
  · simpa [firstMomentVectorNumerator] using
      firstMomentVectorNumeratorDigit3_le_maximum state
  · simpa [firstMomentVectorNumerator] using
      firstMomentVectorNumeratorDigit4_le_maximum state

set_option maxRecDepth 1000000 in
theorem firstMomentVectorMaximum_le_two_mul_scale :
    forall a : Fin 5,
      firstMomentCertificateVectorMaximum <= 2 * firstMomentVectorScale a := by
  decide +kernel

theorem firstMomentVectorNumerator_le_two_mul_scale
    (a : Fin 5) (state : Fin 10000) :
    firstMomentVectorNumerator a state <= 2 * firstMomentVectorScale a :=
  (firstMomentVectorNumerator_le_maximum a state).trans
    (firstMomentVectorMaximum_le_two_mul_scale a)

end PrimesRestrictedDigits
