import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentDigit0
import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentDigit1
import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentDigit2
import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentDigit3
import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentDigit4
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

/-!
# Exact data for the first-moment certificates

Five 5,000-entry literals define reflected 10,000-state natural vectors.
All lookup bounds are carried by `Fin`; there is no defaulting operation.
-/

namespace PrimesRestrictedDigits

/-- Checked positive normalization scale for a representative digit vector. -/
def firstMomentVectorScale (a : Fin 5) : Nat :=
  match a.val with
  | 0 => firstMomentVectorScaleDigit0
  | 1 => firstMomentVectorScaleDigit1
  | 2 => firstMomentVectorScaleDigit2
  | 3 => firstMomentVectorScaleDigit3
  | 4 => firstMomentVectorScaleDigit4
  | _ => 0

/-- Reflected natural subeigenvector numerator for a representative digit. -/
def firstMomentVectorNumerator (a : Fin 5) (state : Fin 10000) : Nat :=
  match a.val with
  | 0 => firstMomentVectorNumeratorDigit0 state
  | 1 => firstMomentVectorNumeratorDigit1 state
  | 2 => firstMomentVectorNumeratorDigit2 state
  | 3 => firstMomentVectorNumeratorDigit3 state
  | 4 => firstMomentVectorNumeratorDigit4 state
  | _ => 0

set_option maxRecDepth 1000000 in
theorem firstMomentVectorScale_pos :
    forall a : Fin 5, 0 < firstMomentVectorScale a := by
  decide +kernel

theorem firstMomentVectorNumerator_reflect
    (a : Fin 5) (state : Fin 10000) :
    firstMomentVectorNumerator a ⟨9999 - state.val, by omega⟩ =
      firstMomentVectorNumerator a state := by
  fin_cases a
  · simpa [firstMomentVectorNumerator,
      firstMomentVectorNumeratorDigit0] using
      moment235ReflectedHalfVectorEntry_reflect
        firstMomentHalfVectorDigit0 state
  · simpa [firstMomentVectorNumerator,
      firstMomentVectorNumeratorDigit1] using
      moment235ReflectedHalfVectorEntry_reflect
        firstMomentHalfVectorDigit1 state
  · simpa [firstMomentVectorNumerator,
      firstMomentVectorNumeratorDigit2] using
      moment235ReflectedHalfVectorEntry_reflect
        firstMomentHalfVectorDigit2 state
  · simpa [firstMomentVectorNumerator,
      firstMomentVectorNumeratorDigit3] using
      moment235ReflectedHalfVectorEntry_reflect
        firstMomentHalfVectorDigit3 state
  · simpa [firstMomentVectorNumerator,
      firstMomentVectorNumeratorDigit4] using
      moment235ReflectedHalfVectorEntry_reflect
        firstMomentHalfVectorDigit4 state

end PrimesRestrictedDigits
