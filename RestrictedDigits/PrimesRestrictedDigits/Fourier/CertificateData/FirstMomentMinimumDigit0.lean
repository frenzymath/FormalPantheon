import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentDigit0
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

/-! Kernel checks for one reflected first-moment vector minimum. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

private theorem firstMomentVectorMinDigit0Block0 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨0 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block1 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨1 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block2 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨2 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block3 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨3 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block4 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨4 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block5 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨5 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block6 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨6 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block7 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨7 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block8 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨8 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block9 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨9 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block10 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨10 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block11 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨11 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block12 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨12 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block13 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨13 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block14 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨14 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block15 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨15 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block16 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨16 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block17 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨17 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block18 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨18 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block19 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨19 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block20 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨20 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block21 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨21 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block22 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨22 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block23 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨23 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block24 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨24 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block25 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨25 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block26 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨26 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block27 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨27 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block28 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨28 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block29 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨29 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block30 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨30 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block31 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨31 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block32 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨32 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block33 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨33 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block34 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨34 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block35 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨35 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block36 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨36 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block37 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨37 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block38 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨38 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block39 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨39 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block40 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨40 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block41 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨41 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block42 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨42 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block43 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨43 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block44 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨44 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block45 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨45 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block46 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨46 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block47 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨47 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block48 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨48 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Block49 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨49 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit0Blocked :
    forall (block : Fin 50) (offset : Fin 100),
      firstMomentVectorScaleDigit0 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit0
          ⟨block.val * 100 + offset.val, by omega⟩ := by
  intro block offset
  fin_cases block
  · exact firstMomentVectorMinDigit0Block0 offset
  · exact firstMomentVectorMinDigit0Block1 offset
  · exact firstMomentVectorMinDigit0Block2 offset
  · exact firstMomentVectorMinDigit0Block3 offset
  · exact firstMomentVectorMinDigit0Block4 offset
  · exact firstMomentVectorMinDigit0Block5 offset
  · exact firstMomentVectorMinDigit0Block6 offset
  · exact firstMomentVectorMinDigit0Block7 offset
  · exact firstMomentVectorMinDigit0Block8 offset
  · exact firstMomentVectorMinDigit0Block9 offset
  · exact firstMomentVectorMinDigit0Block10 offset
  · exact firstMomentVectorMinDigit0Block11 offset
  · exact firstMomentVectorMinDigit0Block12 offset
  · exact firstMomentVectorMinDigit0Block13 offset
  · exact firstMomentVectorMinDigit0Block14 offset
  · exact firstMomentVectorMinDigit0Block15 offset
  · exact firstMomentVectorMinDigit0Block16 offset
  · exact firstMomentVectorMinDigit0Block17 offset
  · exact firstMomentVectorMinDigit0Block18 offset
  · exact firstMomentVectorMinDigit0Block19 offset
  · exact firstMomentVectorMinDigit0Block20 offset
  · exact firstMomentVectorMinDigit0Block21 offset
  · exact firstMomentVectorMinDigit0Block22 offset
  · exact firstMomentVectorMinDigit0Block23 offset
  · exact firstMomentVectorMinDigit0Block24 offset
  · exact firstMomentVectorMinDigit0Block25 offset
  · exact firstMomentVectorMinDigit0Block26 offset
  · exact firstMomentVectorMinDigit0Block27 offset
  · exact firstMomentVectorMinDigit0Block28 offset
  · exact firstMomentVectorMinDigit0Block29 offset
  · exact firstMomentVectorMinDigit0Block30 offset
  · exact firstMomentVectorMinDigit0Block31 offset
  · exact firstMomentVectorMinDigit0Block32 offset
  · exact firstMomentVectorMinDigit0Block33 offset
  · exact firstMomentVectorMinDigit0Block34 offset
  · exact firstMomentVectorMinDigit0Block35 offset
  · exact firstMomentVectorMinDigit0Block36 offset
  · exact firstMomentVectorMinDigit0Block37 offset
  · exact firstMomentVectorMinDigit0Block38 offset
  · exact firstMomentVectorMinDigit0Block39 offset
  · exact firstMomentVectorMinDigit0Block40 offset
  · exact firstMomentVectorMinDigit0Block41 offset
  · exact firstMomentVectorMinDigit0Block42 offset
  · exact firstMomentVectorMinDigit0Block43 offset
  · exact firstMomentVectorMinDigit0Block44 offset
  · exact firstMomentVectorMinDigit0Block45 offset
  · exact firstMomentVectorMinDigit0Block46 offset
  · exact firstMomentVectorMinDigit0Block47 offset
  · exact firstMomentVectorMinDigit0Block48 offset
  · exact firstMomentVectorMinDigit0Block49 offset

theorem firstMomentVectorScaleDigit0_le (state : Fin 10000) :
    firstMomentVectorScaleDigit0 <=
      firstMomentVectorNumeratorDigit0 state := by
  exact moment235ReflectedHalfVectorEntry_le_of_blocked
    firstMomentHalfVectorDigit0 firstMomentVectorScaleDigit0
    firstMomentVectorMinDigit0Blocked state

end PrimesRestrictedDigits
