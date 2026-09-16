import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentMinimumDigit3
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

/-! Kernel checks for one reflected first-moment vector maximum. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

private theorem firstMomentVectorMaxDigit3Block0 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨0 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block1 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨1 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block2 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨2 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block3 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨3 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block4 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨4 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block5 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨5 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block6 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨6 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block7 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨7 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block8 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨8 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block9 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨9 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block10 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨10 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block11 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨11 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block12 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨12 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block13 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨13 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block14 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨14 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block15 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨15 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block16 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨16 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block17 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨17 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block18 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨18 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block19 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨19 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block20 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨20 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block21 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨21 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block22 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨22 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block23 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨23 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block24 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨24 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block25 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨25 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block26 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨26 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block27 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨27 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block28 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨28 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block29 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨29 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block30 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨30 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block31 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨31 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block32 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨32 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block33 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨33 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block34 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨34 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block35 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨35 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block36 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨36 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block37 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨37 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block38 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨38 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block39 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨39 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block40 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨40 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block41 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨41 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block42 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨42 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block43 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨43 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block44 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨44 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block45 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨45 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block46 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨46 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block47 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨47 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block48 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨48 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Block49 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨49 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit3Blocked :
    forall (block : Fin 50) (offset : Fin 100),
      moment235HalfVectorEntry firstMomentHalfVectorDigit3
          ⟨block.val * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  intro block offset
  fin_cases block
  · exact firstMomentVectorMaxDigit3Block0 offset
  · exact firstMomentVectorMaxDigit3Block1 offset
  · exact firstMomentVectorMaxDigit3Block2 offset
  · exact firstMomentVectorMaxDigit3Block3 offset
  · exact firstMomentVectorMaxDigit3Block4 offset
  · exact firstMomentVectorMaxDigit3Block5 offset
  · exact firstMomentVectorMaxDigit3Block6 offset
  · exact firstMomentVectorMaxDigit3Block7 offset
  · exact firstMomentVectorMaxDigit3Block8 offset
  · exact firstMomentVectorMaxDigit3Block9 offset
  · exact firstMomentVectorMaxDigit3Block10 offset
  · exact firstMomentVectorMaxDigit3Block11 offset
  · exact firstMomentVectorMaxDigit3Block12 offset
  · exact firstMomentVectorMaxDigit3Block13 offset
  · exact firstMomentVectorMaxDigit3Block14 offset
  · exact firstMomentVectorMaxDigit3Block15 offset
  · exact firstMomentVectorMaxDigit3Block16 offset
  · exact firstMomentVectorMaxDigit3Block17 offset
  · exact firstMomentVectorMaxDigit3Block18 offset
  · exact firstMomentVectorMaxDigit3Block19 offset
  · exact firstMomentVectorMaxDigit3Block20 offset
  · exact firstMomentVectorMaxDigit3Block21 offset
  · exact firstMomentVectorMaxDigit3Block22 offset
  · exact firstMomentVectorMaxDigit3Block23 offset
  · exact firstMomentVectorMaxDigit3Block24 offset
  · exact firstMomentVectorMaxDigit3Block25 offset
  · exact firstMomentVectorMaxDigit3Block26 offset
  · exact firstMomentVectorMaxDigit3Block27 offset
  · exact firstMomentVectorMaxDigit3Block28 offset
  · exact firstMomentVectorMaxDigit3Block29 offset
  · exact firstMomentVectorMaxDigit3Block30 offset
  · exact firstMomentVectorMaxDigit3Block31 offset
  · exact firstMomentVectorMaxDigit3Block32 offset
  · exact firstMomentVectorMaxDigit3Block33 offset
  · exact firstMomentVectorMaxDigit3Block34 offset
  · exact firstMomentVectorMaxDigit3Block35 offset
  · exact firstMomentVectorMaxDigit3Block36 offset
  · exact firstMomentVectorMaxDigit3Block37 offset
  · exact firstMomentVectorMaxDigit3Block38 offset
  · exact firstMomentVectorMaxDigit3Block39 offset
  · exact firstMomentVectorMaxDigit3Block40 offset
  · exact firstMomentVectorMaxDigit3Block41 offset
  · exact firstMomentVectorMaxDigit3Block42 offset
  · exact firstMomentVectorMaxDigit3Block43 offset
  · exact firstMomentVectorMaxDigit3Block44 offset
  · exact firstMomentVectorMaxDigit3Block45 offset
  · exact firstMomentVectorMaxDigit3Block46 offset
  · exact firstMomentVectorMaxDigit3Block47 offset
  · exact firstMomentVectorMaxDigit3Block48 offset
  · exact firstMomentVectorMaxDigit3Block49 offset

theorem firstMomentVectorNumeratorDigit3_le_maximum
    (state : Fin 10000) :
    firstMomentVectorNumeratorDigit3 state <=
      firstMomentCertificateVectorMaximum := by
  exact firstMomentReflectedHalfVectorEntry_le_of_blocked
    firstMomentHalfVectorDigit3 firstMomentCertificateVectorMaximum
    firstMomentVectorMaxDigit3Blocked state

end PrimesRestrictedDigits
