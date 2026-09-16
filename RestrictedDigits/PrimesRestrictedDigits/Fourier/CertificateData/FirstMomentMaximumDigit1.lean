import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentMinimumDigit1
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

/-! Kernel checks for one reflected first-moment vector maximum. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

private theorem firstMomentVectorMaxDigit1Block0 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨0 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block1 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨1 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block2 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨2 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block3 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨3 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block4 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨4 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block5 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨5 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block6 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨6 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block7 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨7 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block8 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨8 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block9 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨9 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block10 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨10 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block11 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨11 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block12 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨12 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block13 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨13 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block14 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨14 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block15 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨15 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block16 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨16 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block17 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨17 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block18 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨18 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block19 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨19 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block20 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨20 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block21 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨21 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block22 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨22 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block23 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨23 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block24 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨24 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block25 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨25 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block26 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨26 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block27 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨27 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block28 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨28 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block29 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨29 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block30 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨30 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block31 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨31 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block32 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨32 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block33 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨33 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block34 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨34 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block35 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨35 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block36 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨36 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block37 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨37 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block38 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨38 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block39 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨39 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block40 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨40 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block41 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨41 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block42 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨42 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block43 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨43 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block44 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨44 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block45 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨45 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block46 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨46 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block47 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨47 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block48 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨48 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Block49 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨49 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit1Blocked :
    forall (block : Fin 50) (offset : Fin 100),
      moment235HalfVectorEntry firstMomentHalfVectorDigit1
          ⟨block.val * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  intro block offset
  fin_cases block
  · exact firstMomentVectorMaxDigit1Block0 offset
  · exact firstMomentVectorMaxDigit1Block1 offset
  · exact firstMomentVectorMaxDigit1Block2 offset
  · exact firstMomentVectorMaxDigit1Block3 offset
  · exact firstMomentVectorMaxDigit1Block4 offset
  · exact firstMomentVectorMaxDigit1Block5 offset
  · exact firstMomentVectorMaxDigit1Block6 offset
  · exact firstMomentVectorMaxDigit1Block7 offset
  · exact firstMomentVectorMaxDigit1Block8 offset
  · exact firstMomentVectorMaxDigit1Block9 offset
  · exact firstMomentVectorMaxDigit1Block10 offset
  · exact firstMomentVectorMaxDigit1Block11 offset
  · exact firstMomentVectorMaxDigit1Block12 offset
  · exact firstMomentVectorMaxDigit1Block13 offset
  · exact firstMomentVectorMaxDigit1Block14 offset
  · exact firstMomentVectorMaxDigit1Block15 offset
  · exact firstMomentVectorMaxDigit1Block16 offset
  · exact firstMomentVectorMaxDigit1Block17 offset
  · exact firstMomentVectorMaxDigit1Block18 offset
  · exact firstMomentVectorMaxDigit1Block19 offset
  · exact firstMomentVectorMaxDigit1Block20 offset
  · exact firstMomentVectorMaxDigit1Block21 offset
  · exact firstMomentVectorMaxDigit1Block22 offset
  · exact firstMomentVectorMaxDigit1Block23 offset
  · exact firstMomentVectorMaxDigit1Block24 offset
  · exact firstMomentVectorMaxDigit1Block25 offset
  · exact firstMomentVectorMaxDigit1Block26 offset
  · exact firstMomentVectorMaxDigit1Block27 offset
  · exact firstMomentVectorMaxDigit1Block28 offset
  · exact firstMomentVectorMaxDigit1Block29 offset
  · exact firstMomentVectorMaxDigit1Block30 offset
  · exact firstMomentVectorMaxDigit1Block31 offset
  · exact firstMomentVectorMaxDigit1Block32 offset
  · exact firstMomentVectorMaxDigit1Block33 offset
  · exact firstMomentVectorMaxDigit1Block34 offset
  · exact firstMomentVectorMaxDigit1Block35 offset
  · exact firstMomentVectorMaxDigit1Block36 offset
  · exact firstMomentVectorMaxDigit1Block37 offset
  · exact firstMomentVectorMaxDigit1Block38 offset
  · exact firstMomentVectorMaxDigit1Block39 offset
  · exact firstMomentVectorMaxDigit1Block40 offset
  · exact firstMomentVectorMaxDigit1Block41 offset
  · exact firstMomentVectorMaxDigit1Block42 offset
  · exact firstMomentVectorMaxDigit1Block43 offset
  · exact firstMomentVectorMaxDigit1Block44 offset
  · exact firstMomentVectorMaxDigit1Block45 offset
  · exact firstMomentVectorMaxDigit1Block46 offset
  · exact firstMomentVectorMaxDigit1Block47 offset
  · exact firstMomentVectorMaxDigit1Block48 offset
  · exact firstMomentVectorMaxDigit1Block49 offset

theorem firstMomentVectorNumeratorDigit1_le_maximum
    (state : Fin 10000) :
    firstMomentVectorNumeratorDigit1 state <=
      firstMomentCertificateVectorMaximum := by
  exact firstMomentReflectedHalfVectorEntry_le_of_blocked
    firstMomentHalfVectorDigit1 firstMomentCertificateVectorMaximum
    firstMomentVectorMaxDigit1Blocked state

end PrimesRestrictedDigits
