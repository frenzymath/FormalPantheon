import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentDigit1
import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentMaximumDigit0
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

/-! Kernel checks for one reflected first-moment vector minimum. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

private theorem firstMomentVectorMinDigit1Block0 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨0 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block1 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨1 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block2 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨2 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block3 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨3 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block4 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨4 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block5 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨5 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block6 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨6 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block7 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨7 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block8 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨8 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block9 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨9 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block10 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨10 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block11 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨11 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block12 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨12 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block13 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨13 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block14 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨14 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block15 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨15 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block16 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨16 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block17 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨17 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block18 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨18 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block19 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨19 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block20 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨20 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block21 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨21 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block22 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨22 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block23 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨23 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block24 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨24 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block25 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨25 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block26 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨26 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block27 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨27 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block28 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨28 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block29 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨29 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block30 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨30 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block31 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨31 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block32 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨32 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block33 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨33 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block34 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨34 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block35 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨35 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block36 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨36 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block37 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨37 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block38 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨38 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block39 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨39 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block40 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨40 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block41 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨41 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block42 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨42 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block43 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨43 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block44 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨44 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block45 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨45 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block46 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨46 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block47 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨47 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block48 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨48 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Block49 :
    forall offset : Fin 100,
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨49 * 100 + offset.val, by omega⟩ := by
  decide +kernel

private theorem firstMomentVectorMinDigit1Blocked :
    forall (block : Fin 50) (offset : Fin 100),
      firstMomentVectorScaleDigit1 <= moment235HalfVectorEntry
          firstMomentHalfVectorDigit1
          ⟨block.val * 100 + offset.val, by omega⟩ := by
  intro block offset
  fin_cases block
  · exact firstMomentVectorMinDigit1Block0 offset
  · exact firstMomentVectorMinDigit1Block1 offset
  · exact firstMomentVectorMinDigit1Block2 offset
  · exact firstMomentVectorMinDigit1Block3 offset
  · exact firstMomentVectorMinDigit1Block4 offset
  · exact firstMomentVectorMinDigit1Block5 offset
  · exact firstMomentVectorMinDigit1Block6 offset
  · exact firstMomentVectorMinDigit1Block7 offset
  · exact firstMomentVectorMinDigit1Block8 offset
  · exact firstMomentVectorMinDigit1Block9 offset
  · exact firstMomentVectorMinDigit1Block10 offset
  · exact firstMomentVectorMinDigit1Block11 offset
  · exact firstMomentVectorMinDigit1Block12 offset
  · exact firstMomentVectorMinDigit1Block13 offset
  · exact firstMomentVectorMinDigit1Block14 offset
  · exact firstMomentVectorMinDigit1Block15 offset
  · exact firstMomentVectorMinDigit1Block16 offset
  · exact firstMomentVectorMinDigit1Block17 offset
  · exact firstMomentVectorMinDigit1Block18 offset
  · exact firstMomentVectorMinDigit1Block19 offset
  · exact firstMomentVectorMinDigit1Block20 offset
  · exact firstMomentVectorMinDigit1Block21 offset
  · exact firstMomentVectorMinDigit1Block22 offset
  · exact firstMomentVectorMinDigit1Block23 offset
  · exact firstMomentVectorMinDigit1Block24 offset
  · exact firstMomentVectorMinDigit1Block25 offset
  · exact firstMomentVectorMinDigit1Block26 offset
  · exact firstMomentVectorMinDigit1Block27 offset
  · exact firstMomentVectorMinDigit1Block28 offset
  · exact firstMomentVectorMinDigit1Block29 offset
  · exact firstMomentVectorMinDigit1Block30 offset
  · exact firstMomentVectorMinDigit1Block31 offset
  · exact firstMomentVectorMinDigit1Block32 offset
  · exact firstMomentVectorMinDigit1Block33 offset
  · exact firstMomentVectorMinDigit1Block34 offset
  · exact firstMomentVectorMinDigit1Block35 offset
  · exact firstMomentVectorMinDigit1Block36 offset
  · exact firstMomentVectorMinDigit1Block37 offset
  · exact firstMomentVectorMinDigit1Block38 offset
  · exact firstMomentVectorMinDigit1Block39 offset
  · exact firstMomentVectorMinDigit1Block40 offset
  · exact firstMomentVectorMinDigit1Block41 offset
  · exact firstMomentVectorMinDigit1Block42 offset
  · exact firstMomentVectorMinDigit1Block43 offset
  · exact firstMomentVectorMinDigit1Block44 offset
  · exact firstMomentVectorMinDigit1Block45 offset
  · exact firstMomentVectorMinDigit1Block46 offset
  · exact firstMomentVectorMinDigit1Block47 offset
  · exact firstMomentVectorMinDigit1Block48 offset
  · exact firstMomentVectorMinDigit1Block49 offset

theorem firstMomentVectorScaleDigit1_le (state : Fin 10000) :
    firstMomentVectorScaleDigit1 <=
      firstMomentVectorNumeratorDigit1 state := by
  exact moment235ReflectedHalfVectorEntry_le_of_blocked
    firstMomentHalfVectorDigit1 firstMomentVectorScaleDigit1
    firstMomentVectorMinDigit1Blocked state

end PrimesRestrictedDigits
