import PrimesRestrictedDigits.Fourier.Moment235CertificateData
import PrimesRestrictedDigits.Fourier.CertificateData.Moment235MinimumDigit0
import PrimesRestrictedDigits.Fourier.CertificateData.Moment235MinimumDigit1
import PrimesRestrictedDigits.Fourier.CertificateData.Moment235MinimumDigit2
import PrimesRestrictedDigits.Fourier.CertificateData.Moment235MinimumDigit3
import PrimesRestrictedDigits.Fourier.CertificateData.Moment235MinimumDigit4
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

/-!
# Minimum and terminal bridges for the five exact vectors
-/

namespace PrimesRestrictedDigits

theorem moment235VectorScale_le
    (a : Fin 5) (state : Fin 10000) :
    moment235VectorScale a <= moment235VectorNumerator a state := by
  fin_cases a
  · simpa [moment235VectorScale, moment235VectorNumerator] using
      moment235VectorScaleDigit0_le state
  · simpa [moment235VectorScale, moment235VectorNumerator] using
      moment235VectorScaleDigit1_le state
  · simpa [moment235VectorScale, moment235VectorNumerator] using
      moment235VectorScaleDigit2_le state
  · simpa [moment235VectorScale, moment235VectorNumerator] using
      moment235VectorScaleDigit3_le state
  · simpa [moment235VectorScale, moment235VectorNumerator] using
      moment235VectorScaleDigit4_le state

theorem moment235VectorScale_pos' :
    forall a : Fin 5, 0 < moment235VectorScale a := by
  decide +kernel

theorem moment235Vector_zero_eq_scale' :
    forall a : Fin 5,
      moment235VectorNumerator a 0 = moment235VectorScale a := by
  decide +kernel

end PrimesRestrictedDigits
