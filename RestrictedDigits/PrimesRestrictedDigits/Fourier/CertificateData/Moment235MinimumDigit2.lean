import PrimesRestrictedDigits.Fourier.CertificateData.Moment235Digit2
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

/-! Kernel checks for one reflected fractional-moment vector minimum. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

private theorem moment235VectorMinDigit2Block0 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨0 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block1 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨1 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block2 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨2 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block3 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨3 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block4 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨4 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block5 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨5 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block6 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨6 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block7 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨7 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block8 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨8 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block9 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨9 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block10 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨10 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block11 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨11 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block12 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨12 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block13 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨13 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block14 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨14 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block15 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨15 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block16 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨16 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block17 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨17 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block18 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨18 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block19 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨19 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block20 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨20 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block21 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨21 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block22 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨22 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block23 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨23 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block24 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨24 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block25 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨25 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block26 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨26 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block27 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨27 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block28 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨28 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block29 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨29 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block30 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨30 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block31 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨31 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block32 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨32 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block33 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨33 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block34 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨34 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block35 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨35 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block36 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨36 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block37 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨37 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block38 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨38 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block39 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨39 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block40 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨40 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block41 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨41 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block42 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨42 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block43 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨43 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block44 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨44 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block45 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨45 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block46 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨46 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block47 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨47 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block48 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨48 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Block49 :
    forall offset : Fin 100,
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨49 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit2Blocked :
    forall (block : Fin 50) (offset : Fin 100),
      moment235VectorScaleDigit2 <= moment235HalfVectorEntry
        moment235HalfVectorDigit2
        ⟨block.val * 100 + offset.val, by omega⟩ := by
  intro block offset
  fin_cases block
  · exact moment235VectorMinDigit2Block0 offset
  · exact moment235VectorMinDigit2Block1 offset
  · exact moment235VectorMinDigit2Block2 offset
  · exact moment235VectorMinDigit2Block3 offset
  · exact moment235VectorMinDigit2Block4 offset
  · exact moment235VectorMinDigit2Block5 offset
  · exact moment235VectorMinDigit2Block6 offset
  · exact moment235VectorMinDigit2Block7 offset
  · exact moment235VectorMinDigit2Block8 offset
  · exact moment235VectorMinDigit2Block9 offset
  · exact moment235VectorMinDigit2Block10 offset
  · exact moment235VectorMinDigit2Block11 offset
  · exact moment235VectorMinDigit2Block12 offset
  · exact moment235VectorMinDigit2Block13 offset
  · exact moment235VectorMinDigit2Block14 offset
  · exact moment235VectorMinDigit2Block15 offset
  · exact moment235VectorMinDigit2Block16 offset
  · exact moment235VectorMinDigit2Block17 offset
  · exact moment235VectorMinDigit2Block18 offset
  · exact moment235VectorMinDigit2Block19 offset
  · exact moment235VectorMinDigit2Block20 offset
  · exact moment235VectorMinDigit2Block21 offset
  · exact moment235VectorMinDigit2Block22 offset
  · exact moment235VectorMinDigit2Block23 offset
  · exact moment235VectorMinDigit2Block24 offset
  · exact moment235VectorMinDigit2Block25 offset
  · exact moment235VectorMinDigit2Block26 offset
  · exact moment235VectorMinDigit2Block27 offset
  · exact moment235VectorMinDigit2Block28 offset
  · exact moment235VectorMinDigit2Block29 offset
  · exact moment235VectorMinDigit2Block30 offset
  · exact moment235VectorMinDigit2Block31 offset
  · exact moment235VectorMinDigit2Block32 offset
  · exact moment235VectorMinDigit2Block33 offset
  · exact moment235VectorMinDigit2Block34 offset
  · exact moment235VectorMinDigit2Block35 offset
  · exact moment235VectorMinDigit2Block36 offset
  · exact moment235VectorMinDigit2Block37 offset
  · exact moment235VectorMinDigit2Block38 offset
  · exact moment235VectorMinDigit2Block39 offset
  · exact moment235VectorMinDigit2Block40 offset
  · exact moment235VectorMinDigit2Block41 offset
  · exact moment235VectorMinDigit2Block42 offset
  · exact moment235VectorMinDigit2Block43 offset
  · exact moment235VectorMinDigit2Block44 offset
  · exact moment235VectorMinDigit2Block45 offset
  · exact moment235VectorMinDigit2Block46 offset
  · exact moment235VectorMinDigit2Block47 offset
  · exact moment235VectorMinDigit2Block48 offset
  · exact moment235VectorMinDigit2Block49 offset

theorem moment235VectorScaleDigit2_le (state : Fin 10000) :
    moment235VectorScaleDigit2 <=
      moment235VectorNumeratorDigit2 state := by
  exact moment235ReflectedHalfVectorEntry_le_of_blocked
    moment235HalfVectorDigit2 moment235VectorScaleDigit2
    moment235VectorMinDigit2Blocked state

end PrimesRestrictedDigits
