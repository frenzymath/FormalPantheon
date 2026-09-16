import PrimesRestrictedDigits.Fourier.CertificateData.Moment235RowsDigit2Group21
import PrimesRestrictedDigits.Fourier.Moment235CertificateRowAggregation

/-! Bounds for one 200-row certificate group. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

theorem moment235RowsDigit2Group21 :
    forall offset : Fin 200,
      moment235IndexedRow (2 : Fin 5)
        ⟨4200 + offset.val, by omega⟩ := by
  have h4200_4220 := moment235IndexedRows_append (2 : Fin 5) 4200 10 10
    (by omega) moment235RowsDigit2Group21Block00 moment235RowsDigit2Group21Block01
  have h4220_4240 := moment235IndexedRows_append (2 : Fin 5) 4220 10 10
    (by omega) moment235RowsDigit2Group21Block02 moment235RowsDigit2Group21Block03
  have h4240_4260 := moment235IndexedRows_append (2 : Fin 5) 4240 10 10
    (by omega) moment235RowsDigit2Group21Block04 moment235RowsDigit2Group21Block05
  have h4260_4280 := moment235IndexedRows_append (2 : Fin 5) 4260 10 10
    (by omega) moment235RowsDigit2Group21Block06 moment235RowsDigit2Group21Block07
  have h4280_4300 := moment235IndexedRows_append (2 : Fin 5) 4280 10 10
    (by omega) moment235RowsDigit2Group21Block08 moment235RowsDigit2Group21Block09
  have h4300_4320 := moment235IndexedRows_append (2 : Fin 5) 4300 10 10
    (by omega) moment235RowsDigit2Group21Block10 moment235RowsDigit2Group21Block11
  have h4320_4340 := moment235IndexedRows_append (2 : Fin 5) 4320 10 10
    (by omega) moment235RowsDigit2Group21Block12 moment235RowsDigit2Group21Block13
  have h4340_4360 := moment235IndexedRows_append (2 : Fin 5) 4340 10 10
    (by omega) moment235RowsDigit2Group21Block14 moment235RowsDigit2Group21Block15
  have h4360_4380 := moment235IndexedRows_append (2 : Fin 5) 4360 10 10
    (by omega) moment235RowsDigit2Group21Block16 moment235RowsDigit2Group21Block17
  have h4380_4400 := moment235IndexedRows_append (2 : Fin 5) 4380 10 10
    (by omega) moment235RowsDigit2Group21Block18 moment235RowsDigit2Group21Block19
  have h4200_4240 := moment235IndexedRows_append (2 : Fin 5) 4200 20 20
    (by omega) h4200_4220 h4220_4240
  have h4240_4280 := moment235IndexedRows_append (2 : Fin 5) 4240 20 20
    (by omega) h4240_4260 h4260_4280
  have h4280_4320 := moment235IndexedRows_append (2 : Fin 5) 4280 20 20
    (by omega) h4280_4300 h4300_4320
  have h4320_4360 := moment235IndexedRows_append (2 : Fin 5) 4320 20 20
    (by omega) h4320_4340 h4340_4360
  have h4360_4400 := moment235IndexedRows_append (2 : Fin 5) 4360 20 20
    (by omega) h4360_4380 h4380_4400
  have h4200_4280 := moment235IndexedRows_append (2 : Fin 5) 4200 40 40
    (by omega) h4200_4240 h4240_4280
  have h4280_4360 := moment235IndexedRows_append (2 : Fin 5) 4280 40 40
    (by omega) h4280_4320 h4320_4360
  have h4200_4360 := moment235IndexedRows_append (2 : Fin 5) 4200 80 80
    (by omega) h4200_4280 h4280_4360
  exact moment235IndexedRows_append (2 : Fin 5) 4200 160 40
    (by omega) h4200_4360 h4360_4400

end PrimesRestrictedDigits
