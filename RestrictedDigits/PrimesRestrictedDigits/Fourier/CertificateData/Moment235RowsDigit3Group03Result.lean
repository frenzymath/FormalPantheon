import PrimesRestrictedDigits.Fourier.CertificateData.Moment235RowsDigit3Group03
import PrimesRestrictedDigits.Fourier.Moment235CertificateRowAggregation

/-! Bounds for one 200-row certificate group. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

theorem moment235RowsDigit3Group03 :
    forall offset : Fin 200,
      moment235IndexedRow (3 : Fin 5)
        ⟨600 + offset.val, by omega⟩ := by
  have h600_620 := moment235IndexedRows_append (3 : Fin 5) 600 10 10
    (by omega) moment235RowsDigit3Group03Block00 moment235RowsDigit3Group03Block01
  have h620_640 := moment235IndexedRows_append (3 : Fin 5) 620 10 10
    (by omega) moment235RowsDigit3Group03Block02 moment235RowsDigit3Group03Block03
  have h640_660 := moment235IndexedRows_append (3 : Fin 5) 640 10 10
    (by omega) moment235RowsDigit3Group03Block04 moment235RowsDigit3Group03Block05
  have h660_680 := moment235IndexedRows_append (3 : Fin 5) 660 10 10
    (by omega) moment235RowsDigit3Group03Block06 moment235RowsDigit3Group03Block07
  have h680_700 := moment235IndexedRows_append (3 : Fin 5) 680 10 10
    (by omega) moment235RowsDigit3Group03Block08 moment235RowsDigit3Group03Block09
  have h700_720 := moment235IndexedRows_append (3 : Fin 5) 700 10 10
    (by omega) moment235RowsDigit3Group03Block10 moment235RowsDigit3Group03Block11
  have h720_740 := moment235IndexedRows_append (3 : Fin 5) 720 10 10
    (by omega) moment235RowsDigit3Group03Block12 moment235RowsDigit3Group03Block13
  have h740_760 := moment235IndexedRows_append (3 : Fin 5) 740 10 10
    (by omega) moment235RowsDigit3Group03Block14 moment235RowsDigit3Group03Block15
  have h760_780 := moment235IndexedRows_append (3 : Fin 5) 760 10 10
    (by omega) moment235RowsDigit3Group03Block16 moment235RowsDigit3Group03Block17
  have h780_800 := moment235IndexedRows_append (3 : Fin 5) 780 10 10
    (by omega) moment235RowsDigit3Group03Block18 moment235RowsDigit3Group03Block19
  have h600_640 := moment235IndexedRows_append (3 : Fin 5) 600 20 20
    (by omega) h600_620 h620_640
  have h640_680 := moment235IndexedRows_append (3 : Fin 5) 640 20 20
    (by omega) h640_660 h660_680
  have h680_720 := moment235IndexedRows_append (3 : Fin 5) 680 20 20
    (by omega) h680_700 h700_720
  have h720_760 := moment235IndexedRows_append (3 : Fin 5) 720 20 20
    (by omega) h720_740 h740_760
  have h760_800 := moment235IndexedRows_append (3 : Fin 5) 760 20 20
    (by omega) h760_780 h780_800
  have h600_680 := moment235IndexedRows_append (3 : Fin 5) 600 40 40
    (by omega) h600_640 h640_680
  have h680_760 := moment235IndexedRows_append (3 : Fin 5) 680 40 40
    (by omega) h680_720 h720_760
  have h600_760 := moment235IndexedRows_append (3 : Fin 5) 600 80 80
    (by omega) h600_680 h680_760
  exact moment235IndexedRows_append (3 : Fin 5) 600 160 40
    (by omega) h600_760 h760_800

end PrimesRestrictedDigits
