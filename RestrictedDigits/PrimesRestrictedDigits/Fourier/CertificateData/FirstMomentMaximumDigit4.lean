import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentMinimumDigit4
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

/-! Kernel checks for one reflected first-moment vector maximum. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

private theorem firstMomentVectorMaxDigit4Block0 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨0 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block1 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨1 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block2 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨2 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block3 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨3 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block4 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨4 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block5 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨5 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block6 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨6 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block7 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨7 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block8 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨8 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block9 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨9 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block10 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨10 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block11 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨11 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block12 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨12 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block13 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨13 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block14 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨14 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block15 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨15 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block16 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨16 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block17 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨17 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block18 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨18 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block19 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨19 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block20 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨20 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block21 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨21 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block22 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨22 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block23 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨23 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block24 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨24 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block25 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨25 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block26 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨26 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block27 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨27 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block28 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨28 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block29 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨29 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block30 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨30 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block31 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨31 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block32 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨32 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block33 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨33 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block34 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨34 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block35 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨35 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block36 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨36 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block37 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨37 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block38 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨38 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block39 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨39 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block40 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨40 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block41 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨41 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block42 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨42 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block43 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨43 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block44 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨44 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block45 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨45 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block46 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨46 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block47 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨47 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block48 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨48 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Block49 :
    forall offset : Fin 100,
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨49 * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  decide +kernel

private theorem firstMomentVectorMaxDigit4Blocked :
    forall (block : Fin 50) (offset : Fin 100),
      moment235HalfVectorEntry firstMomentHalfVectorDigit4
          ⟨block.val * 100 + offset.val, by omega⟩ <=
        firstMomentCertificateVectorMaximum := by
  intro block offset
  fin_cases block
  · exact firstMomentVectorMaxDigit4Block0 offset
  · exact firstMomentVectorMaxDigit4Block1 offset
  · exact firstMomentVectorMaxDigit4Block2 offset
  · exact firstMomentVectorMaxDigit4Block3 offset
  · exact firstMomentVectorMaxDigit4Block4 offset
  · exact firstMomentVectorMaxDigit4Block5 offset
  · exact firstMomentVectorMaxDigit4Block6 offset
  · exact firstMomentVectorMaxDigit4Block7 offset
  · exact firstMomentVectorMaxDigit4Block8 offset
  · exact firstMomentVectorMaxDigit4Block9 offset
  · exact firstMomentVectorMaxDigit4Block10 offset
  · exact firstMomentVectorMaxDigit4Block11 offset
  · exact firstMomentVectorMaxDigit4Block12 offset
  · exact firstMomentVectorMaxDigit4Block13 offset
  · exact firstMomentVectorMaxDigit4Block14 offset
  · exact firstMomentVectorMaxDigit4Block15 offset
  · exact firstMomentVectorMaxDigit4Block16 offset
  · exact firstMomentVectorMaxDigit4Block17 offset
  · exact firstMomentVectorMaxDigit4Block18 offset
  · exact firstMomentVectorMaxDigit4Block19 offset
  · exact firstMomentVectorMaxDigit4Block20 offset
  · exact firstMomentVectorMaxDigit4Block21 offset
  · exact firstMomentVectorMaxDigit4Block22 offset
  · exact firstMomentVectorMaxDigit4Block23 offset
  · exact firstMomentVectorMaxDigit4Block24 offset
  · exact firstMomentVectorMaxDigit4Block25 offset
  · exact firstMomentVectorMaxDigit4Block26 offset
  · exact firstMomentVectorMaxDigit4Block27 offset
  · exact firstMomentVectorMaxDigit4Block28 offset
  · exact firstMomentVectorMaxDigit4Block29 offset
  · exact firstMomentVectorMaxDigit4Block30 offset
  · exact firstMomentVectorMaxDigit4Block31 offset
  · exact firstMomentVectorMaxDigit4Block32 offset
  · exact firstMomentVectorMaxDigit4Block33 offset
  · exact firstMomentVectorMaxDigit4Block34 offset
  · exact firstMomentVectorMaxDigit4Block35 offset
  · exact firstMomentVectorMaxDigit4Block36 offset
  · exact firstMomentVectorMaxDigit4Block37 offset
  · exact firstMomentVectorMaxDigit4Block38 offset
  · exact firstMomentVectorMaxDigit4Block39 offset
  · exact firstMomentVectorMaxDigit4Block40 offset
  · exact firstMomentVectorMaxDigit4Block41 offset
  · exact firstMomentVectorMaxDigit4Block42 offset
  · exact firstMomentVectorMaxDigit4Block43 offset
  · exact firstMomentVectorMaxDigit4Block44 offset
  · exact firstMomentVectorMaxDigit4Block45 offset
  · exact firstMomentVectorMaxDigit4Block46 offset
  · exact firstMomentVectorMaxDigit4Block47 offset
  · exact firstMomentVectorMaxDigit4Block48 offset
  · exact firstMomentVectorMaxDigit4Block49 offset

theorem firstMomentVectorNumeratorDigit4_le_maximum
    (state : Fin 10000) :
    firstMomentVectorNumeratorDigit4 state <=
      firstMomentCertificateVectorMaximum := by
  exact firstMomentReflectedHalfVectorEntry_le_of_blocked
    firstMomentHalfVectorDigit4 firstMomentCertificateVectorMaximum
    firstMomentVectorMaxDigit4Blocked state

end PrimesRestrictedDigits
