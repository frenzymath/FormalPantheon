import PrimesRestrictedDigits.Fourier.CertificateData.Moment235RowsDigit2Group22
import PrimesRestrictedDigits.Fourier.Moment235CertificateRowAggregation

/-! Bounds for one 200-row certificate group. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

theorem moment235RowsDigit2Group22 :
    forall offset : Fin 200,
      moment235IndexedRow (2 : Fin 5)
        ⟨4400 + offset.val, by omega⟩ := by
  have h4400_4420 := moment235IndexedRows_append (2 : Fin 5) 4400 10 10
    (by omega) moment235RowsDigit2Group22Block00 moment235RowsDigit2Group22Block01
  have h4420_4440 := moment235IndexedRows_append (2 : Fin 5) 4420 10 10
    (by omega) moment235RowsDigit2Group22Block02 moment235RowsDigit2Group22Block03
  have h4440_4460 := moment235IndexedRows_append (2 : Fin 5) 4440 10 10
    (by omega) moment235RowsDigit2Group22Block04 moment235RowsDigit2Group22Block05
  have h4460_4480 := moment235IndexedRows_append (2 : Fin 5) 4460 10 10
    (by omega) moment235RowsDigit2Group22Block06 moment235RowsDigit2Group22Block07
  have h4480_4500 := moment235IndexedRows_append (2 : Fin 5) 4480 10 10
    (by omega) moment235RowsDigit2Group22Block08 moment235RowsDigit2Group22Block09
  have h4500_4520 := moment235IndexedRows_append (2 : Fin 5) 4500 10 10
    (by omega) moment235RowsDigit2Group22Block10 moment235RowsDigit2Group22Block11
  have h4520_4540 := moment235IndexedRows_append (2 : Fin 5) 4520 10 10
    (by omega) moment235RowsDigit2Group22Block12 moment235RowsDigit2Group22Block13
  have h4540_4560 := moment235IndexedRows_append (2 : Fin 5) 4540 10 10
    (by omega) moment235RowsDigit2Group22Block14 moment235RowsDigit2Group22Block15
  have h4560_4580 := moment235IndexedRows_append (2 : Fin 5) 4560 10 10
    (by omega) moment235RowsDigit2Group22Block16 moment235RowsDigit2Group22Block17
  have h4580_4600 := moment235IndexedRows_append (2 : Fin 5) 4580 10 10
    (by omega) moment235RowsDigit2Group22Block18 moment235RowsDigit2Group22Block19
  have h4400_4440 := moment235IndexedRows_append (2 : Fin 5) 4400 20 20
    (by omega) h4400_4420 h4420_4440
  have h4440_4480 := moment235IndexedRows_append (2 : Fin 5) 4440 20 20
    (by omega) h4440_4460 h4460_4480
  have h4480_4520 := moment235IndexedRows_append (2 : Fin 5) 4480 20 20
    (by omega) h4480_4500 h4500_4520
  have h4520_4560 := moment235IndexedRows_append (2 : Fin 5) 4520 20 20
    (by omega) h4520_4540 h4540_4560
  have h4560_4600 := moment235IndexedRows_append (2 : Fin 5) 4560 20 20
    (by omega) h4560_4580 h4580_4600
  have h4400_4480 := moment235IndexedRows_append (2 : Fin 5) 4400 40 40
    (by omega) h4400_4440 h4440_4480
  have h4480_4560 := moment235IndexedRows_append (2 : Fin 5) 4480 40 40
    (by omega) h4480_4520 h4520_4560
  have h4400_4560 := moment235IndexedRows_append (2 : Fin 5) 4400 80 80
    (by omega) h4400_4480 h4480_4560
  exact moment235IndexedRows_append (2 : Fin 5) 4400 160 40
    (by omega) h4400_4560 h4560_4600

end PrimesRestrictedDigits
