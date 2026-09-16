import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentDigit4
import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentMaximumDigit3
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

/-! Kernel checks for one reflected first-moment vector minimum. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

private theorem firstMomentVectorMinDigit4Block0 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨0 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block1 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨1 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block2 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨2 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block3 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨3 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block4 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨4 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block5 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨5 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block6 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨6 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block7 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨7 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block8 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨8 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block9 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨9 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block10 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨10 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block11 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨11 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block12 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨12 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block13 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨13 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block14 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨14 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block15 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨15 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block16 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨16 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block17 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨17 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block18 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨18 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block19 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨19 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block20 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨20 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block21 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨21 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block22 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨22 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block23 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨23 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block24 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨24 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block25 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨25 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block26 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨26 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block27 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨27 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block28 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨28 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block29 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨29 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block30 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨30 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block31 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨31 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block32 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨32 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block33 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨33 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block34 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨34 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block35 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨35 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block36 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨36 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block37 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨37 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block38 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨38 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block39 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨39 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block40 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨40 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block41 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨41 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block42 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨42 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block43 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨43 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block44 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨44 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block45 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨45 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block46 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨46 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block47 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨47 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block48 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨48 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Block49 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨49 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit4Blocked :
    forall (block : Fin 50) (offset : Fin 100),
      firstMomentVectorScaleDigit4 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit4
          ⟨block.val * 100 + offset.val, by omega⟩ := by
  intro block offset
  fin_cases block
  · exact firstMomentVectorMinDigit4Block0 offset
  · exact firstMomentVectorMinDigit4Block1 offset
  · exact firstMomentVectorMinDigit4Block2 offset
  · exact firstMomentVectorMinDigit4Block3 offset
  · exact firstMomentVectorMinDigit4Block4 offset
  · exact firstMomentVectorMinDigit4Block5 offset
  · exact firstMomentVectorMinDigit4Block6 offset
  · exact firstMomentVectorMinDigit4Block7 offset
  · exact firstMomentVectorMinDigit4Block8 offset
  · exact firstMomentVectorMinDigit4Block9 offset
  · exact firstMomentVectorMinDigit4Block10 offset
  · exact firstMomentVectorMinDigit4Block11 offset
  · exact firstMomentVectorMinDigit4Block12 offset
  · exact firstMomentVectorMinDigit4Block13 offset
  · exact firstMomentVectorMinDigit4Block14 offset
  · exact firstMomentVectorMinDigit4Block15 offset
  · exact firstMomentVectorMinDigit4Block16 offset
  · exact firstMomentVectorMinDigit4Block17 offset
  · exact firstMomentVectorMinDigit4Block18 offset
  · exact firstMomentVectorMinDigit4Block19 offset
  · exact firstMomentVectorMinDigit4Block20 offset
  · exact firstMomentVectorMinDigit4Block21 offset
  · exact firstMomentVectorMinDigit4Block22 offset
  · exact firstMomentVectorMinDigit4Block23 offset
  · exact firstMomentVectorMinDigit4Block24 offset
  · exact firstMomentVectorMinDigit4Block25 offset
  · exact firstMomentVectorMinDigit4Block26 offset
  · exact firstMomentVectorMinDigit4Block27 offset
  · exact firstMomentVectorMinDigit4Block28 offset
  · exact firstMomentVectorMinDigit4Block29 offset
  · exact firstMomentVectorMinDigit4Block30 offset
  · exact firstMomentVectorMinDigit4Block31 offset
  · exact firstMomentVectorMinDigit4Block32 offset
  · exact firstMomentVectorMinDigit4Block33 offset
  · exact firstMomentVectorMinDigit4Block34 offset
  · exact firstMomentVectorMinDigit4Block35 offset
  · exact firstMomentVectorMinDigit4Block36 offset
  · exact firstMomentVectorMinDigit4Block37 offset
  · exact firstMomentVectorMinDigit4Block38 offset
  · exact firstMomentVectorMinDigit4Block39 offset
  · exact firstMomentVectorMinDigit4Block40 offset
  · exact firstMomentVectorMinDigit4Block41 offset
  · exact firstMomentVectorMinDigit4Block42 offset
  · exact firstMomentVectorMinDigit4Block43 offset
  · exact firstMomentVectorMinDigit4Block44 offset
  · exact firstMomentVectorMinDigit4Block45 offset
  · exact firstMomentVectorMinDigit4Block46 offset
  · exact firstMomentVectorMinDigit4Block47 offset
  · exact firstMomentVectorMinDigit4Block48 offset
  · exact firstMomentVectorMinDigit4Block49 offset

theorem firstMomentVectorScaleDigit4_le (state : Fin 10000) :
    firstMomentVectorScaleDigit4 <=
      firstMomentVectorNumeratorDigit4 state := by
  exact moment235ReflectedHalfVectorEntry_le_of_blocked
    firstMomentHalfVectorDigit4 firstMomentVectorScaleDigit4
    firstMomentVectorMinDigit4Blocked state

end PrimesRestrictedDigits
