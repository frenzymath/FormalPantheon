import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentMinimumDigit0
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

/-! Kernel checks for one reflected first-moment vector maximum. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

private theorem firstMomentVectorMaxDigit0Block0 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨0 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block1 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨1 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block2 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨2 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block3 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨3 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block4 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨4 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block5 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨5 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block6 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨6 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block7 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨7 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block8 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨8 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block9 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨9 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block10 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨10 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block11 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨11 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block12 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨12 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block13 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨13 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block14 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨14 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block15 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨15 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block16 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨16 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block17 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨17 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block18 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨18 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block19 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨19 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block20 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨20 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block21 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨21 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block22 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨22 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block23 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨23 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block24 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨24 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block25 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨25 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block26 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨26 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block27 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨27 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block28 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨28 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block29 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨29 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block30 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨30 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block31 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨31 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block32 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨32 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block33 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨33 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block34 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨34 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block35 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨35 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block36 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨36 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block37 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨37 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block38 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨38 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block39 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨39 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block40 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨40 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block41 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨41 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block42 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨42 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block43 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨43 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block44 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨44 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block45 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨45 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block46 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨46 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block47 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨47 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block48 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨48 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Block49 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨49 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit0Blocked :
    forall (block : Fin 50) (offset : Fin 100),
      moment235HalfVectorEntry firstMomentHalfVectorDigit0
          ⟨block.val * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  intro block offset
  fin_cases block
  · exact firstMomentVectorMaxDigit0Block0 offset
  · exact firstMomentVectorMaxDigit0Block1 offset
  · exact firstMomentVectorMaxDigit0Block2 offset
  · exact firstMomentVectorMaxDigit0Block3 offset
  · exact firstMomentVectorMaxDigit0Block4 offset
  · exact firstMomentVectorMaxDigit0Block5 offset
  · exact firstMomentVectorMaxDigit0Block6 offset
  · exact firstMomentVectorMaxDigit0Block7 offset
  · exact firstMomentVectorMaxDigit0Block8 offset
  · exact firstMomentVectorMaxDigit0Block9 offset
  · exact firstMomentVectorMaxDigit0Block10 offset
  · exact firstMomentVectorMaxDigit0Block11 offset
  · exact firstMomentVectorMaxDigit0Block12 offset
  · exact firstMomentVectorMaxDigit0Block13 offset
  · exact firstMomentVectorMaxDigit0Block14 offset
  · exact firstMomentVectorMaxDigit0Block15 offset
  · exact firstMomentVectorMaxDigit0Block16 offset
  · exact firstMomentVectorMaxDigit0Block17 offset
  · exact firstMomentVectorMaxDigit0Block18 offset
  · exact firstMomentVectorMaxDigit0Block19 offset
  · exact firstMomentVectorMaxDigit0Block20 offset
  · exact firstMomentVectorMaxDigit0Block21 offset
  · exact firstMomentVectorMaxDigit0Block22 offset
  · exact firstMomentVectorMaxDigit0Block23 offset
  · exact firstMomentVectorMaxDigit0Block24 offset
  · exact firstMomentVectorMaxDigit0Block25 offset
  · exact firstMomentVectorMaxDigit0Block26 offset
  · exact firstMomentVectorMaxDigit0Block27 offset
  · exact firstMomentVectorMaxDigit0Block28 offset
  · exact firstMomentVectorMaxDigit0Block29 offset
  · exact firstMomentVectorMaxDigit0Block30 offset
  · exact firstMomentVectorMaxDigit0Block31 offset
  · exact firstMomentVectorMaxDigit0Block32 offset
  · exact firstMomentVectorMaxDigit0Block33 offset
  · exact firstMomentVectorMaxDigit0Block34 offset
  · exact firstMomentVectorMaxDigit0Block35 offset
  · exact firstMomentVectorMaxDigit0Block36 offset
  · exact firstMomentVectorMaxDigit0Block37 offset
  · exact firstMomentVectorMaxDigit0Block38 offset
  · exact firstMomentVectorMaxDigit0Block39 offset
  · exact firstMomentVectorMaxDigit0Block40 offset
  · exact firstMomentVectorMaxDigit0Block41 offset
  · exact firstMomentVectorMaxDigit0Block42 offset
  · exact firstMomentVectorMaxDigit0Block43 offset
  · exact firstMomentVectorMaxDigit0Block44 offset
  · exact firstMomentVectorMaxDigit0Block45 offset
  · exact firstMomentVectorMaxDigit0Block46 offset
  · exact firstMomentVectorMaxDigit0Block47 offset
  · exact firstMomentVectorMaxDigit0Block48 offset
  · exact firstMomentVectorMaxDigit0Block49 offset

theorem firstMomentVectorNumeratorDigit0_le_maximum
    (state : Fin 10000) :
    firstMomentVectorNumeratorDigit0 state <=
      firstMomentCertificateVectorMaximum := by
  exact firstMomentReflectedHalfVectorEntry_le_of_blocked
    firstMomentHalfVectorDigit0 firstMomentCertificateVectorMaximum
    firstMomentVectorMaxDigit0Blocked state

end PrimesRestrictedDigits
