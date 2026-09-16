import PrimesRestrictedDigits.Fourier.CertificateData.Moment235RowsDigit1Group17
import PrimesRestrictedDigits.Fourier.Moment235CertificateRowAggregation

/-! Bounds for one 200-row certificate group. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

theorem moment235RowsDigit1Group17 :
    forall offset : Fin 200,
      moment235IndexedRow (1 : Fin 5)
        ⟨3400 + offset.val, by omega⟩ := by
  have h3400_3420 := moment235IndexedRows_append (1 : Fin 5) 3400 10 10
    (by omega) moment235RowsDigit1Group17Block00 moment235RowsDigit1Group17Block01
  have h3420_3440 := moment235IndexedRows_append (1 : Fin 5) 3420 10 10
    (by omega) moment235RowsDigit1Group17Block02 moment235RowsDigit1Group17Block03
  have h3440_3460 := moment235IndexedRows_append (1 : Fin 5) 3440 10 10
    (by omega) moment235RowsDigit1Group17Block04 moment235RowsDigit1Group17Block05
  have h3460_3480 := moment235IndexedRows_append (1 : Fin 5) 3460 10 10
    (by omega) moment235RowsDigit1Group17Block06 moment235RowsDigit1Group17Block07
  have h3480_3500 := moment235IndexedRows_append (1 : Fin 5) 3480 10 10
    (by omega) moment235RowsDigit1Group17Block08 moment235RowsDigit1Group17Block09
  have h3500_3520 := moment235IndexedRows_append (1 : Fin 5) 3500 10 10
    (by omega) moment235RowsDigit1Group17Block10 moment235RowsDigit1Group17Block11
  have h3520_3540 := moment235IndexedRows_append (1 : Fin 5) 3520 10 10
    (by omega) moment235RowsDigit1Group17Block12 moment235RowsDigit1Group17Block13
  have h3540_3560 := moment235IndexedRows_append (1 : Fin 5) 3540 10 10
    (by omega) moment235RowsDigit1Group17Block14 moment235RowsDigit1Group17Block15
  have h3560_3580 := moment235IndexedRows_append (1 : Fin 5) 3560 10 10
    (by omega) moment235RowsDigit1Group17Block16 moment235RowsDigit1Group17Block17
  have h3580_3600 := moment235IndexedRows_append (1 : Fin 5) 3580 10 10
    (by omega) moment235RowsDigit1Group17Block18 moment235RowsDigit1Group17Block19
  have h3400_3440 := moment235IndexedRows_append (1 : Fin 5) 3400 20 20
    (by omega) h3400_3420 h3420_3440
  have h3440_3480 := moment235IndexedRows_append (1 : Fin 5) 3440 20 20
    (by omega) h3440_3460 h3460_3480
  have h3480_3520 := moment235IndexedRows_append (1 : Fin 5) 3480 20 20
    (by omega) h3480_3500 h3500_3520
  have h3520_3560 := moment235IndexedRows_append (1 : Fin 5) 3520 20 20
    (by omega) h3520_3540 h3540_3560
  have h3560_3600 := moment235IndexedRows_append (1 : Fin 5) 3560 20 20
    (by omega) h3560_3580 h3580_3600
  have h3400_3480 := moment235IndexedRows_append (1 : Fin 5) 3400 40 40
    (by omega) h3400_3440 h3440_3480
  have h3480_3560 := moment235IndexedRows_append (1 : Fin 5) 3480 40 40
    (by omega) h3480_3520 h3520_3560
  have h3400_3560 := moment235IndexedRows_append (1 : Fin 5) 3400 80 80
    (by omega) h3400_3480 h3480_3560
  exact moment235IndexedRows_append (1 : Fin 5) 3400 160 40
    (by omega) h3400_3560 h3560_3600

end PrimesRestrictedDigits
