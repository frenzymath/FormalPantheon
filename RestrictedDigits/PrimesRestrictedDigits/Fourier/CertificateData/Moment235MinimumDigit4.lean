import PrimesRestrictedDigits.Fourier.CertificateData.Moment235Digit4
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

/-! Kernel checks for one reflected fractional-moment vector minimum. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

private theorem moment235VectorMinDigit4Block0 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨0 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block1 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨1 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block2 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨2 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block3 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨3 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block4 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨4 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block5 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨5 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block6 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨6 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block7 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨7 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block8 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨8 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block9 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨9 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block10 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨10 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block11 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨11 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block12 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨12 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block13 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨13 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block14 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨14 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block15 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨15 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block16 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨16 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block17 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨17 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block18 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨18 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block19 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨19 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block20 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨20 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block21 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨21 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block22 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨22 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block23 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨23 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block24 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨24 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block25 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨25 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block26 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨26 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block27 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨27 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block28 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨28 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block29 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨29 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block30 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨30 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block31 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨31 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block32 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨32 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block33 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨33 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block34 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨34 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block35 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨35 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block36 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨36 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block37 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨37 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block38 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨38 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block39 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨39 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block40 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨40 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block41 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨41 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block42 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨42 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block43 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨43 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block44 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨44 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block45 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨45 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block46 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨46 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block47 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨47 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block48 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨48 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Block49 :
    forall offset : Fin 100,
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨49 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit4Blocked :
    forall (block : Fin 50) (offset : Fin 100),
      moment235VectorScaleDigit4 <= moment235HalfVectorEntry
        moment235HalfVectorDigit4
        ⟨block.val * 100 + offset.val, by omega⟩ := by
  intro block offset
  fin_cases block
  · exact moment235VectorMinDigit4Block0 offset
  · exact moment235VectorMinDigit4Block1 offset
  · exact moment235VectorMinDigit4Block2 offset
  · exact moment235VectorMinDigit4Block3 offset
  · exact moment235VectorMinDigit4Block4 offset
  · exact moment235VectorMinDigit4Block5 offset
  · exact moment235VectorMinDigit4Block6 offset
  · exact moment235VectorMinDigit4Block7 offset
  · exact moment235VectorMinDigit4Block8 offset
  · exact moment235VectorMinDigit4Block9 offset
  · exact moment235VectorMinDigit4Block10 offset
  · exact moment235VectorMinDigit4Block11 offset
  · exact moment235VectorMinDigit4Block12 offset
  · exact moment235VectorMinDigit4Block13 offset
  · exact moment235VectorMinDigit4Block14 offset
  · exact moment235VectorMinDigit4Block15 offset
  · exact moment235VectorMinDigit4Block16 offset
  · exact moment235VectorMinDigit4Block17 offset
  · exact moment235VectorMinDigit4Block18 offset
  · exact moment235VectorMinDigit4Block19 offset
  · exact moment235VectorMinDigit4Block20 offset
  · exact moment235VectorMinDigit4Block21 offset
  · exact moment235VectorMinDigit4Block22 offset
  · exact moment235VectorMinDigit4Block23 offset
  · exact moment235VectorMinDigit4Block24 offset
  · exact moment235VectorMinDigit4Block25 offset
  · exact moment235VectorMinDigit4Block26 offset
  · exact moment235VectorMinDigit4Block27 offset
  · exact moment235VectorMinDigit4Block28 offset
  · exact moment235VectorMinDigit4Block29 offset
  · exact moment235VectorMinDigit4Block30 offset
  · exact moment235VectorMinDigit4Block31 offset
  · exact moment235VectorMinDigit4Block32 offset
  · exact moment235VectorMinDigit4Block33 offset
  · exact moment235VectorMinDigit4Block34 offset
  · exact moment235VectorMinDigit4Block35 offset
  · exact moment235VectorMinDigit4Block36 offset
  · exact moment235VectorMinDigit4Block37 offset
  · exact moment235VectorMinDigit4Block38 offset
  · exact moment235VectorMinDigit4Block39 offset
  · exact moment235VectorMinDigit4Block40 offset
  · exact moment235VectorMinDigit4Block41 offset
  · exact moment235VectorMinDigit4Block42 offset
  · exact moment235VectorMinDigit4Block43 offset
  · exact moment235VectorMinDigit4Block44 offset
  · exact moment235VectorMinDigit4Block45 offset
  · exact moment235VectorMinDigit4Block46 offset
  · exact moment235VectorMinDigit4Block47 offset
  · exact moment235VectorMinDigit4Block48 offset
  · exact moment235VectorMinDigit4Block49 offset

theorem moment235VectorScaleDigit4_le (state : Fin 10000) :
    moment235VectorScaleDigit4 <=
      moment235VectorNumeratorDigit4 state := by
  exact moment235ReflectedHalfVectorEntry_le_of_blocked
    moment235HalfVectorDigit4 moment235VectorScaleDigit4
    moment235VectorMinDigit4Blocked state

end PrimesRestrictedDigits
