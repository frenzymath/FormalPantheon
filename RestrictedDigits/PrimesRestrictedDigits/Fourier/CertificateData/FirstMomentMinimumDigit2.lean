import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentDigit2
import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentMaximumDigit1
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

/-! Kernel checks for one reflected first-moment vector minimum. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

private theorem firstMomentVectorMinDigit2Block0 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨0 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block1 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨1 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block2 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨2 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block3 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨3 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block4 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨4 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block5 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨5 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block6 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨6 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block7 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨7 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block8 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨8 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block9 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨9 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block10 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨10 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block11 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨11 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block12 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨12 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block13 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨13 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block14 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨14 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block15 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨15 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block16 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨16 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block17 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨17 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block18 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨18 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block19 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨19 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block20 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨20 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block21 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨21 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block22 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨22 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block23 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨23 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block24 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨24 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block25 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨25 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block26 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨26 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block27 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨27 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block28 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨28 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block29 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨29 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block30 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨30 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block31 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨31 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block32 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨32 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block33 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨33 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block34 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨34 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block35 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨35 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block36 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨36 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block37 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨37 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block38 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨38 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block39 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨39 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block40 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨40 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block41 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨41 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block42 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨42 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block43 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨43 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block44 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨44 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block45 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨45 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block46 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨46 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block47 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨47 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block48 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨48 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Block49 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨49 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit2Blocked :
    forall (block : Fin 50) (offset : Fin 100),
      firstMomentVectorScaleDigit2 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit2
          ⟨block.val * 100 + offset.val, by omega⟩ := by
  intro block offset
  fin_cases block
  · exact firstMomentVectorMinDigit2Block0 offset
  · exact firstMomentVectorMinDigit2Block1 offset
  · exact firstMomentVectorMinDigit2Block2 offset
  · exact firstMomentVectorMinDigit2Block3 offset
  · exact firstMomentVectorMinDigit2Block4 offset
  · exact firstMomentVectorMinDigit2Block5 offset
  · exact firstMomentVectorMinDigit2Block6 offset
  · exact firstMomentVectorMinDigit2Block7 offset
  · exact firstMomentVectorMinDigit2Block8 offset
  · exact firstMomentVectorMinDigit2Block9 offset
  · exact firstMomentVectorMinDigit2Block10 offset
  · exact firstMomentVectorMinDigit2Block11 offset
  · exact firstMomentVectorMinDigit2Block12 offset
  · exact firstMomentVectorMinDigit2Block13 offset
  · exact firstMomentVectorMinDigit2Block14 offset
  · exact firstMomentVectorMinDigit2Block15 offset
  · exact firstMomentVectorMinDigit2Block16 offset
  · exact firstMomentVectorMinDigit2Block17 offset
  · exact firstMomentVectorMinDigit2Block18 offset
  · exact firstMomentVectorMinDigit2Block19 offset
  · exact firstMomentVectorMinDigit2Block20 offset
  · exact firstMomentVectorMinDigit2Block21 offset
  · exact firstMomentVectorMinDigit2Block22 offset
  · exact firstMomentVectorMinDigit2Block23 offset
  · exact firstMomentVectorMinDigit2Block24 offset
  · exact firstMomentVectorMinDigit2Block25 offset
  · exact firstMomentVectorMinDigit2Block26 offset
  · exact firstMomentVectorMinDigit2Block27 offset
  · exact firstMomentVectorMinDigit2Block28 offset
  · exact firstMomentVectorMinDigit2Block29 offset
  · exact firstMomentVectorMinDigit2Block30 offset
  · exact firstMomentVectorMinDigit2Block31 offset
  · exact firstMomentVectorMinDigit2Block32 offset
  · exact firstMomentVectorMinDigit2Block33 offset
  · exact firstMomentVectorMinDigit2Block34 offset
  · exact firstMomentVectorMinDigit2Block35 offset
  · exact firstMomentVectorMinDigit2Block36 offset
  · exact firstMomentVectorMinDigit2Block37 offset
  · exact firstMomentVectorMinDigit2Block38 offset
  · exact firstMomentVectorMinDigit2Block39 offset
  · exact firstMomentVectorMinDigit2Block40 offset
  · exact firstMomentVectorMinDigit2Block41 offset
  · exact firstMomentVectorMinDigit2Block42 offset
  · exact firstMomentVectorMinDigit2Block43 offset
  · exact firstMomentVectorMinDigit2Block44 offset
  · exact firstMomentVectorMinDigit2Block45 offset
  · exact firstMomentVectorMinDigit2Block46 offset
  · exact firstMomentVectorMinDigit2Block47 offset
  · exact firstMomentVectorMinDigit2Block48 offset
  · exact firstMomentVectorMinDigit2Block49 offset

theorem firstMomentVectorScaleDigit2_le (state : Fin 10000) :
    firstMomentVectorScaleDigit2 <=
      firstMomentVectorNumeratorDigit2 state := by
  exact moment235ReflectedHalfVectorEntry_le_of_blocked
    firstMomentHalfVectorDigit2 firstMomentVectorScaleDigit2
    firstMomentVectorMinDigit2Blocked state

end PrimesRestrictedDigits
