import PrimesRestrictedDigits.Fourier.CertificateData.Moment235RowsDigit3Group06
import PrimesRestrictedDigits.Fourier.Moment235CertificateRowAggregation

/-! Bounds for one 200-row certificate group. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

theorem moment235RowsDigit3Group06 :
    forall offset : Fin 200,
      moment235IndexedRow (3 : Fin 5)
        ⟨1200 + offset.val, by omega⟩ := by
  have h1200_1220 := moment235IndexedRows_append (3 : Fin 5) 1200 10 10
    (by omega) moment235RowsDigit3Group06Block00 moment235RowsDigit3Group06Block01
  have h1220_1240 := moment235IndexedRows_append (3 : Fin 5) 1220 10 10
    (by omega) moment235RowsDigit3Group06Block02 moment235RowsDigit3Group06Block03
  have h1240_1260 := moment235IndexedRows_append (3 : Fin 5) 1240 10 10
    (by omega) moment235RowsDigit3Group06Block04 moment235RowsDigit3Group06Block05
  have h1260_1280 := moment235IndexedRows_append (3 : Fin 5) 1260 10 10
    (by omega) moment235RowsDigit3Group06Block06 moment235RowsDigit3Group06Block07
  have h1280_1300 := moment235IndexedRows_append (3 : Fin 5) 1280 10 10
    (by omega) moment235RowsDigit3Group06Block08 moment235RowsDigit3Group06Block09
  have h1300_1320 := moment235IndexedRows_append (3 : Fin 5) 1300 10 10
    (by omega) moment235RowsDigit3Group06Block10 moment235RowsDigit3Group06Block11
  have h1320_1340 := moment235IndexedRows_append (3 : Fin 5) 1320 10 10
    (by omega) moment235RowsDigit3Group06Block12 moment235RowsDigit3Group06Block13
  have h1340_1360 := moment235IndexedRows_append (3 : Fin 5) 1340 10 10
    (by omega) moment235RowsDigit3Group06Block14 moment235RowsDigit3Group06Block15
  have h1360_1380 := moment235IndexedRows_append (3 : Fin 5) 1360 10 10
    (by omega) moment235RowsDigit3Group06Block16 moment235RowsDigit3Group06Block17
  have h1380_1400 := moment235IndexedRows_append (3 : Fin 5) 1380 10 10
    (by omega) moment235RowsDigit3Group06Block18 moment235RowsDigit3Group06Block19
  have h1200_1240 := moment235IndexedRows_append (3 : Fin 5) 1200 20 20
    (by omega) h1200_1220 h1220_1240
  have h1240_1280 := moment235IndexedRows_append (3 : Fin 5) 1240 20 20
    (by omega) h1240_1260 h1260_1280
  have h1280_1320 := moment235IndexedRows_append (3 : Fin 5) 1280 20 20
    (by omega) h1280_1300 h1300_1320
  have h1320_1360 := moment235IndexedRows_append (3 : Fin 5) 1320 20 20
    (by omega) h1320_1340 h1340_1360
  have h1360_1400 := moment235IndexedRows_append (3 : Fin 5) 1360 20 20
    (by omega) h1360_1380 h1380_1400
  have h1200_1280 := moment235IndexedRows_append (3 : Fin 5) 1200 40 40
    (by omega) h1200_1240 h1240_1280
  have h1280_1360 := moment235IndexedRows_append (3 : Fin 5) 1280 40 40
    (by omega) h1280_1320 h1320_1360
  have h1200_1360 := moment235IndexedRows_append (3 : Fin 5) 1200 80 80
    (by omega) h1200_1280 h1280_1360
  exact moment235IndexedRows_append (3 : Fin 5) 1200 160 40
    (by omega) h1200_1360 h1360_1400

end PrimesRestrictedDigits
