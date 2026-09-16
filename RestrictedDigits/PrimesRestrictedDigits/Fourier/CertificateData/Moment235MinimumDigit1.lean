import PrimesRestrictedDigits.Fourier.CertificateData.Moment235Digit1
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

/-! Kernel checks for one reflected fractional-moment vector minimum. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

private theorem moment235VectorMinDigit1Block0 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨0 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block1 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨1 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block2 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨2 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block3 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨3 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block4 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨4 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block5 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨5 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block6 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨6 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block7 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨7 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block8 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨8 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block9 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨9 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block10 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨10 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block11 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨11 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block12 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨12 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block13 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨13 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block14 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨14 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block15 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨15 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block16 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨16 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block17 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨17 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block18 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨18 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block19 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨19 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block20 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨20 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block21 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨21 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block22 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨22 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block23 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨23 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block24 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨24 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block25 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨25 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block26 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨26 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block27 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨27 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block28 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨28 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block29 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨29 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block30 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨30 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block31 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨31 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block32 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨32 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block33 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨33 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block34 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨34 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block35 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨35 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block36 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨36 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block37 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨37 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block38 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨38 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block39 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨39 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block40 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨40 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block41 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨41 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block42 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨42 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block43 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨43 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block44 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨44 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block45 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨45 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block46 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨46 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block47 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨47 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block48 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨48 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Block49 :
    forall offset : Fin 100,
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨49 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem moment235VectorMinDigit1Blocked :
    forall (block : Fin 50) (offset : Fin 100),
      moment235VectorScaleDigit1 <= moment235HalfVectorEntry
        moment235HalfVectorDigit1
        ⟨block.val * 100 + offset.val, by omega⟩ := by
  intro block offset
  fin_cases block
  · exact moment235VectorMinDigit1Block0 offset
  · exact moment235VectorMinDigit1Block1 offset
  · exact moment235VectorMinDigit1Block2 offset
  · exact moment235VectorMinDigit1Block3 offset
  · exact moment235VectorMinDigit1Block4 offset
  · exact moment235VectorMinDigit1Block5 offset
  · exact moment235VectorMinDigit1Block6 offset
  · exact moment235VectorMinDigit1Block7 offset
  · exact moment235VectorMinDigit1Block8 offset
  · exact moment235VectorMinDigit1Block9 offset
  · exact moment235VectorMinDigit1Block10 offset
  · exact moment235VectorMinDigit1Block11 offset
  · exact moment235VectorMinDigit1Block12 offset
  · exact moment235VectorMinDigit1Block13 offset
  · exact moment235VectorMinDigit1Block14 offset
  · exact moment235VectorMinDigit1Block15 offset
  · exact moment235VectorMinDigit1Block16 offset
  · exact moment235VectorMinDigit1Block17 offset
  · exact moment235VectorMinDigit1Block18 offset
  · exact moment235VectorMinDigit1Block19 offset
  · exact moment235VectorMinDigit1Block20 offset
  · exact moment235VectorMinDigit1Block21 offset
  · exact moment235VectorMinDigit1Block22 offset
  · exact moment235VectorMinDigit1Block23 offset
  · exact moment235VectorMinDigit1Block24 offset
  · exact moment235VectorMinDigit1Block25 offset
  · exact moment235VectorMinDigit1Block26 offset
  · exact moment235VectorMinDigit1Block27 offset
  · exact moment235VectorMinDigit1Block28 offset
  · exact moment235VectorMinDigit1Block29 offset
  · exact moment235VectorMinDigit1Block30 offset
  · exact moment235VectorMinDigit1Block31 offset
  · exact moment235VectorMinDigit1Block32 offset
  · exact moment235VectorMinDigit1Block33 offset
  · exact moment235VectorMinDigit1Block34 offset
  · exact moment235VectorMinDigit1Block35 offset
  · exact moment235VectorMinDigit1Block36 offset
  · exact moment235VectorMinDigit1Block37 offset
  · exact moment235VectorMinDigit1Block38 offset
  · exact moment235VectorMinDigit1Block39 offset
  · exact moment235VectorMinDigit1Block40 offset
  · exact moment235VectorMinDigit1Block41 offset
  · exact moment235VectorMinDigit1Block42 offset
  · exact moment235VectorMinDigit1Block43 offset
  · exact moment235VectorMinDigit1Block44 offset
  · exact moment235VectorMinDigit1Block45 offset
  · exact moment235VectorMinDigit1Block46 offset
  · exact moment235VectorMinDigit1Block47 offset
  · exact moment235VectorMinDigit1Block48 offset
  · exact moment235VectorMinDigit1Block49 offset

theorem moment235VectorScaleDigit1_le (state : Fin 10000) :
    moment235VectorScaleDigit1 <=
      moment235VectorNumeratorDigit1 state := by
  exact moment235ReflectedHalfVectorEntry_le_of_blocked
    moment235HalfVectorDigit1 moment235VectorScaleDigit1
    moment235VectorMinDigit1Blocked state

end PrimesRestrictedDigits
