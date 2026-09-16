import PrimesRestrictedDigits.Fourier.CertificateData.Moment235RowsDigit3Group05
import PrimesRestrictedDigits.Fourier.Moment235CertificateRowAggregation

/-! Bounds for one 200-row certificate group. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

theorem moment235RowsDigit3Group05 :
    forall offset : Fin 200,
      moment235IndexedRow (3 : Fin 5)
        ⟨1000 + offset.val, by omega⟩ := by
  have h1000_1020 := moment235IndexedRows_append (3 : Fin 5) 1000 10 10
    (by omega) moment235RowsDigit3Group05Block00 moment235RowsDigit3Group05Block01
  have h1020_1040 := moment235IndexedRows_append (3 : Fin 5) 1020 10 10
    (by omega) moment235RowsDigit3Group05Block02 moment235RowsDigit3Group05Block03
  have h1040_1060 := moment235IndexedRows_append (3 : Fin 5) 1040 10 10
    (by omega) moment235RowsDigit3Group05Block04 moment235RowsDigit3Group05Block05
  have h1060_1080 := moment235IndexedRows_append (3 : Fin 5) 1060 10 10
    (by omega) moment235RowsDigit3Group05Block06 moment235RowsDigit3Group05Block07
  have h1080_1100 := moment235IndexedRows_append (3 : Fin 5) 1080 10 10
    (by omega) moment235RowsDigit3Group05Block08 moment235RowsDigit3Group05Block09
  have h1100_1120 := moment235IndexedRows_append (3 : Fin 5) 1100 10 10
    (by omega) moment235RowsDigit3Group05Block10 moment235RowsDigit3Group05Block11
  have h1120_1140 := moment235IndexedRows_append (3 : Fin 5) 1120 10 10
    (by omega) moment235RowsDigit3Group05Block12 moment235RowsDigit3Group05Block13
  have h1140_1160 := moment235IndexedRows_append (3 : Fin 5) 1140 10 10
    (by omega) moment235RowsDigit3Group05Block14 moment235RowsDigit3Group05Block15
  have h1160_1180 := moment235IndexedRows_append (3 : Fin 5) 1160 10 10
    (by omega) moment235RowsDigit3Group05Block16 moment235RowsDigit3Group05Block17
  have h1180_1200 := moment235IndexedRows_append (3 : Fin 5) 1180 10 10
    (by omega) moment235RowsDigit3Group05Block18 moment235RowsDigit3Group05Block19
  have h1000_1040 := moment235IndexedRows_append (3 : Fin 5) 1000 20 20
    (by omega) h1000_1020 h1020_1040
  have h1040_1080 := moment235IndexedRows_append (3 : Fin 5) 1040 20 20
    (by omega) h1040_1060 h1060_1080
  have h1080_1120 := moment235IndexedRows_append (3 : Fin 5) 1080 20 20
    (by omega) h1080_1100 h1100_1120
  have h1120_1160 := moment235IndexedRows_append (3 : Fin 5) 1120 20 20
    (by omega) h1120_1140 h1140_1160
  have h1160_1200 := moment235IndexedRows_append (3 : Fin 5) 1160 20 20
    (by omega) h1160_1180 h1180_1200
  have h1000_1080 := moment235IndexedRows_append (3 : Fin 5) 1000 40 40
    (by omega) h1000_1040 h1040_1080
  have h1080_1160 := moment235IndexedRows_append (3 : Fin 5) 1080 40 40
    (by omega) h1080_1120 h1120_1160
  have h1000_1160 := moment235IndexedRows_append (3 : Fin 5) 1000 80 80
    (by omega) h1000_1080 h1080_1160
  exact moment235IndexedRows_append (3 : Fin 5) 1000 160 40
    (by omega) h1000_1160 h1160_1200

end PrimesRestrictedDigits
