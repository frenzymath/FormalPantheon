import PrimesRestrictedDigits.Fourier.CertificateData.Moment235Digit0
import PrimesRestrictedDigits.Fourier.CertificateData.Moment235Digit1
import PrimesRestrictedDigits.Fourier.CertificateData.Moment235Digit2
import PrimesRestrictedDigits.Fourier.CertificateData.Moment235Digit3
import PrimesRestrictedDigits.Fourier.CertificateData.Moment235Digit4
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

/-!
# Exact data for the fractional-moment certificates

The five 5,000-entry literals define 10,000-entry vectors by exact reversal.
All lookups carry their bounds; no default or panic-based operation is used.
-/

namespace PrimesRestrictedDigits

def moment235VectorScale (a : Fin 5) : Nat :=
  match a.val with
  | 0 => moment235VectorScaleDigit0
  | 1 => moment235VectorScaleDigit1
  | 2 => moment235VectorScaleDigit2
  | 3 => moment235VectorScaleDigit3
  | 4 => moment235VectorScaleDigit4
  | _ => 0

def moment235VectorNumerator (a : Fin 5) (state : Fin 10000) : Nat :=
  match a.val with
  | 0 => moment235VectorNumeratorDigit0 state
  | 1 => moment235VectorNumeratorDigit1 state
  | 2 => moment235VectorNumeratorDigit2 state
  | 3 => moment235VectorNumeratorDigit3 state
  | 4 => moment235VectorNumeratorDigit4 state
  | _ => 0

set_option maxRecDepth 1000000 in
theorem moment235VectorScale_pos :
    forall a : Fin 5, 0 < moment235VectorScale a := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem moment235Vector_zero_eq_scale :
    forall a : Fin 5,
      moment235VectorNumerator a 0 = moment235VectorScale a := by
  decide +kernel

theorem moment235VectorNumerator_reflect
    (a : Fin 5) (state : Fin 10000) :
    moment235VectorNumerator a ⟨9999 - state.val, by omega⟩ =
      moment235VectorNumerator a state := by
  fin_cases a
  · simpa [moment235VectorNumerator, moment235VectorNumeratorDigit0] using
      moment235ReflectedHalfVectorEntry_reflect moment235HalfVectorDigit0 state
  · simpa [moment235VectorNumerator, moment235VectorNumeratorDigit1] using
      moment235ReflectedHalfVectorEntry_reflect moment235HalfVectorDigit1 state
  · simpa [moment235VectorNumerator, moment235VectorNumeratorDigit2] using
      moment235ReflectedHalfVectorEntry_reflect moment235HalfVectorDigit2 state
  · simpa [moment235VectorNumerator, moment235VectorNumeratorDigit3] using
      moment235ReflectedHalfVectorEntry_reflect moment235HalfVectorDigit3 state
  · simpa [moment235VectorNumerator, moment235VectorNumeratorDigit4] using
      moment235ReflectedHalfVectorEntry_reflect moment235HalfVectorDigit4 state

end PrimesRestrictedDigits
