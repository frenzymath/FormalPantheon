import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentRowsDigit0
import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentRowsDigit1
import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentRowsDigit2
import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentRowsDigit3
import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentRowsDigit4
import Mathlib.Tactic.FinCases

/-! Assembly of all kernel-checked first-moment certificate rows. -/

namespace PrimesRestrictedDigits

theorem firstMomentIndexedRows :
    forall a : Fin 5, forall future : Fin 10000,
      firstMomentIndexedRow a future := by
  intro a
  fin_cases a
  · exact firstMomentRowsDigit0
  · exact firstMomentRowsDigit1
  · exact firstMomentRowsDigit2
  · exact firstMomentRowsDigit3
  · exact firstMomentRowsDigit4

end PrimesRestrictedDigits
