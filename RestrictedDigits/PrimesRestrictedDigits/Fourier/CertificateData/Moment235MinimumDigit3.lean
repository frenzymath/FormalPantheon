import PrimesRestrictedDigits.Fourier.CertificateData.Moment235Digit3
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

/-! Kernel checks for one reflected fractional-moment vector minimum. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

private theorem moment235VectorMinDigit3Block0 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨0 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block1 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨1 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block2 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨2 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block3 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨3 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block4 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨4 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block5 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨5 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block6 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨6 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block7 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨7 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block8 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨8 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block9 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨9 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block10 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨10 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block11 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨11 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block12 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨12 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block13 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨13 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block14 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨14 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block15 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨15 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block16 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨16 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block17 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨17 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block18 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨18 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block19 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨19 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block20 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨20 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block21 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨21 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block22 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨22 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block23 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨23 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block24 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨24 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block25 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨25 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block26 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨26 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block27 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨27 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block28 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨28 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block29 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨29 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block30 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨30 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block31 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨31 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block32 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨32 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block33 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨33 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block34 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨34 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block35 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨35 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block36 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨36 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block37 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨37 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block38 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨38 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block39 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨39 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block40 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨40 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block41 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨41 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block42 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨42 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block43 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨43 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block44 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨44 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block45 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨45 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block46 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨46 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block47 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨47 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block48 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨48 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Block49 :
    forall offset : Fin 100,
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨49 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit3Blocked :
    forall (block : Fin 50) (offset : Fin 100),
      moment235VectorScaleDigit3 <= moment235HalfVectorEntry
        moment235HalfVectorDigit3
        ⟨block.val * 100 + offset.val, by omega⟩ := by
  intro block offset
  fin_cases block
  · exact moment235VectorMinDigit3Block0 offset
  · exact moment235VectorMinDigit3Block1 offset
  · exact moment235VectorMinDigit3Block2 offset
  · exact moment235VectorMinDigit3Block3 offset
  · exact moment235VectorMinDigit3Block4 offset
  · exact moment235VectorMinDigit3Block5 offset
  · exact moment235VectorMinDigit3Block6 offset
  · exact moment235VectorMinDigit3Block7 offset
  · exact moment235VectorMinDigit3Block8 offset
  · exact moment235VectorMinDigit3Block9 offset
  · exact moment235VectorMinDigit3Block10 offset
  · exact moment235VectorMinDigit3Block11 offset
  · exact moment235VectorMinDigit3Block12 offset
  · exact moment235VectorMinDigit3Block13 offset
  · exact moment235VectorMinDigit3Block14 offset
  · exact moment235VectorMinDigit3Block15 offset
  · exact moment235VectorMinDigit3Block16 offset
  · exact moment235VectorMinDigit3Block17 offset
  · exact moment235VectorMinDigit3Block18 offset
  · exact moment235VectorMinDigit3Block19 offset
  · exact moment235VectorMinDigit3Block20 offset
  · exact moment235VectorMinDigit3Block21 offset
  · exact moment235VectorMinDigit3Block22 offset
  · exact moment235VectorMinDigit3Block23 offset
  · exact moment235VectorMinDigit3Block24 offset
  · exact moment235VectorMinDigit3Block25 offset
  · exact moment235VectorMinDigit3Block26 offset
  · exact moment235VectorMinDigit3Block27 offset
  · exact moment235VectorMinDigit3Block28 offset
  · exact moment235VectorMinDigit3Block29 offset
  · exact moment235VectorMinDigit3Block30 offset
  · exact moment235VectorMinDigit3Block31 offset
  · exact moment235VectorMinDigit3Block32 offset
  · exact moment235VectorMinDigit3Block33 offset
  · exact moment235VectorMinDigit3Block34 offset
  · exact moment235VectorMinDigit3Block35 offset
  · exact moment235VectorMinDigit3Block36 offset
  · exact moment235VectorMinDigit3Block37 offset
  · exact moment235VectorMinDigit3Block38 offset
  · exact moment235VectorMinDigit3Block39 offset
  · exact moment235VectorMinDigit3Block40 offset
  · exact moment235VectorMinDigit3Block41 offset
  · exact moment235VectorMinDigit3Block42 offset
  · exact moment235VectorMinDigit3Block43 offset
  · exact moment235VectorMinDigit3Block44 offset
  · exact moment235VectorMinDigit3Block45 offset
  · exact moment235VectorMinDigit3Block46 offset
  · exact moment235VectorMinDigit3Block47 offset
  · exact moment235VectorMinDigit3Block48 offset
  · exact moment235VectorMinDigit3Block49 offset

theorem moment235VectorScaleDigit3_le (state : Fin 10000) :
    moment235VectorScaleDigit3 <=
      moment235VectorNumeratorDigit3 state := by
  exact moment235ReflectedHalfVectorEntry_le_of_blocked
    moment235HalfVectorDigit3 moment235VectorScaleDigit3
    moment235VectorMinDigit3Blocked state

end PrimesRestrictedDigits
