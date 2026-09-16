import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentRowsDigit3Group17
import PrimesRestrictedDigits.Fourier.FirstMomentCertificateRowAggregation

/-! Bounds for one 200-row certificate group. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

theorem firstMomentRowsDigit3Group17 :
    forall offset : Fin 200,
      firstMomentIndexedRow (3 : Fin 5)
        ⟨3400 + offset.val, by omega⟩ := by
  have h3400_3420 := firstMomentIndexedRows_append (3 : Fin 5) 3400 10 10
    (by omega) firstMomentRowsDigit3Group17Block00 firstMomentRowsDigit3Group17Block01
  have h3420_3440 := firstMomentIndexedRows_append (3 : Fin 5) 3420 10 10
    (by omega) firstMomentRowsDigit3Group17Block02 firstMomentRowsDigit3Group17Block03
  have h3440_3460 := firstMomentIndexedRows_append (3 : Fin 5) 3440 10 10
    (by omega) firstMomentRowsDigit3Group17Block04 firstMomentRowsDigit3Group17Block05
  have h3460_3480 := firstMomentIndexedRows_append (3 : Fin 5) 3460 10 10
    (by omega) firstMomentRowsDigit3Group17Block06 firstMomentRowsDigit3Group17Block07
  have h3480_3500 := firstMomentIndexedRows_append (3 : Fin 5) 3480 10 10
    (by omega) firstMomentRowsDigit3Group17Block08 firstMomentRowsDigit3Group17Block09
  have h3500_3520 := firstMomentIndexedRows_append (3 : Fin 5) 3500 10 10
    (by omega) firstMomentRowsDigit3Group17Block10 firstMomentRowsDigit3Group17Block11
  have h3520_3540 := firstMomentIndexedRows_append (3 : Fin 5) 3520 10 10
    (by omega) firstMomentRowsDigit3Group17Block12 firstMomentRowsDigit3Group17Block13
  have h3540_3560 := firstMomentIndexedRows_append (3 : Fin 5) 3540 10 10
    (by omega) firstMomentRowsDigit3Group17Block14 firstMomentRowsDigit3Group17Block15
  have h3560_3580 := firstMomentIndexedRows_append (3 : Fin 5) 3560 10 10
    (by omega) firstMomentRowsDigit3Group17Block16 firstMomentRowsDigit3Group17Block17
  have h3580_3600 := firstMomentIndexedRows_append (3 : Fin 5) 3580 10 10
    (by omega) firstMomentRowsDigit3Group17Block18 firstMomentRowsDigit3Group17Block19
  have h3400_3440 := firstMomentIndexedRows_append (3 : Fin 5) 3400 20 20
    (by omega) h3400_3420 h3420_3440
  have h3440_3480 := firstMomentIndexedRows_append (3 : Fin 5) 3440 20 20
    (by omega) h3440_3460 h3460_3480
  have h3480_3520 := firstMomentIndexedRows_append (3 : Fin 5) 3480 20 20
    (by omega) h3480_3500 h3500_3520
  have h3520_3560 := firstMomentIndexedRows_append (3 : Fin 5) 3520 20 20
    (by omega) h3520_3540 h3540_3560
  have h3560_3600 := firstMomentIndexedRows_append (3 : Fin 5) 3560 20 20
    (by omega) h3560_3580 h3580_3600
  have h3400_3480 := firstMomentIndexedRows_append (3 : Fin 5) 3400 40 40
    (by omega) h3400_3440 h3440_3480
  have h3480_3560 := firstMomentIndexedRows_append (3 : Fin 5) 3480 40 40
    (by omega) h3480_3520 h3520_3560
  have h3400_3560 := firstMomentIndexedRows_append (3 : Fin 5) 3400 80 80
    (by omega) h3400_3480 h3480_3560
  exact firstMomentIndexedRows_append (3 : Fin 5) 3400 160 40
    (by omega) h3400_3560 h3560_3600

end PrimesRestrictedDigits
