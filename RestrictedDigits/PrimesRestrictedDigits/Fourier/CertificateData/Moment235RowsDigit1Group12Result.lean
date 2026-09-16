import PrimesRestrictedDigits.Fourier.CertificateData.Moment235RowsDigit1Group12
import PrimesRestrictedDigits.Fourier.Moment235CertificateRowAggregation

/-! Bounds for one 200-row certificate group. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

theorem moment235RowsDigit1Group12 :
    forall offset : Fin 200,
      moment235IndexedRow (1 : Fin 5)
        ⟨2400 + offset.val, by omega⟩ := by
  have h2400_2420 := moment235IndexedRows_append (1 : Fin 5) 2400 10 10
    (by omega) moment235RowsDigit1Group12Block00 moment235RowsDigit1Group12Block01
  have h2420_2440 := moment235IndexedRows_append (1 : Fin 5) 2420 10 10
    (by omega) moment235RowsDigit1Group12Block02 moment235RowsDigit1Group12Block03
  have h2440_2460 := moment235IndexedRows_append (1 : Fin 5) 2440 10 10
    (by omega) moment235RowsDigit1Group12Block04 moment235RowsDigit1Group12Block05
  have h2460_2480 := moment235IndexedRows_append (1 : Fin 5) 2460 10 10
    (by omega) moment235RowsDigit1Group12Block06 moment235RowsDigit1Group12Block07
  have h2480_2500 := moment235IndexedRows_append (1 : Fin 5) 2480 10 10
    (by omega) moment235RowsDigit1Group12Block08 moment235RowsDigit1Group12Block09
  have h2500_2520 := moment235IndexedRows_append (1 : Fin 5) 2500 10 10
    (by omega) moment235RowsDigit1Group12Block10 moment235RowsDigit1Group12Block11
  have h2520_2540 := moment235IndexedRows_append (1 : Fin 5) 2520 10 10
    (by omega) moment235RowsDigit1Group12Block12 moment235RowsDigit1Group12Block13
  have h2540_2560 := moment235IndexedRows_append (1 : Fin 5) 2540 10 10
    (by omega) moment235RowsDigit1Group12Block14 moment235RowsDigit1Group12Block15
  have h2560_2580 := moment235IndexedRows_append (1 : Fin 5) 2560 10 10
    (by omega) moment235RowsDigit1Group12Block16 moment235RowsDigit1Group12Block17
  have h2580_2600 := moment235IndexedRows_append (1 : Fin 5) 2580 10 10
    (by omega) moment235RowsDigit1Group12Block18 moment235RowsDigit1Group12Block19
  have h2400_2440 := moment235IndexedRows_append (1 : Fin 5) 2400 20 20
    (by omega) h2400_2420 h2420_2440
  have h2440_2480 := moment235IndexedRows_append (1 : Fin 5) 2440 20 20
    (by omega) h2440_2460 h2460_2480
  have h2480_2520 := moment235IndexedRows_append (1 : Fin 5) 2480 20 20
    (by omega) h2480_2500 h2500_2520
  have h2520_2560 := moment235IndexedRows_append (1 : Fin 5) 2520 20 20
    (by omega) h2520_2540 h2540_2560
  have h2560_2600 := moment235IndexedRows_append (1 : Fin 5) 2560 20 20
    (by omega) h2560_2580 h2580_2600
  have h2400_2480 := moment235IndexedRows_append (1 : Fin 5) 2400 40 40
    (by omega) h2400_2440 h2440_2480
  have h2480_2560 := moment235IndexedRows_append (1 : Fin 5) 2480 40 40
    (by omega) h2480_2520 h2520_2560
  have h2400_2560 := moment235IndexedRows_append (1 : Fin 5) 2400 80 80
    (by omega) h2400_2480 h2480_2560
  exact moment235IndexedRows_append (1 : Fin 5) 2400 160 40
    (by omega) h2400_2560 h2560_2600

end PrimesRestrictedDigits
