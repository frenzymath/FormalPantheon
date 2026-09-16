import PrimesRestrictedDigits.Fourier.CertificateData.Moment235RowsDigit3Group10
import PrimesRestrictedDigits.Fourier.Moment235CertificateRowAggregation

/-! Bounds for one 200-row certificate group. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

theorem moment235RowsDigit3Group10 :
    forall offset : Fin 200,
      moment235IndexedRow (3 : Fin 5)
        ⟨2000 + offset.val, by omega⟩ := by
  have h2000_2020 := moment235IndexedRows_append (3 : Fin 5) 2000 10 10
    (by omega) moment235RowsDigit3Group10Block00 moment235RowsDigit3Group10Block01
  have h2020_2040 := moment235IndexedRows_append (3 : Fin 5) 2020 10 10
    (by omega) moment235RowsDigit3Group10Block02 moment235RowsDigit3Group10Block03
  have h2040_2060 := moment235IndexedRows_append (3 : Fin 5) 2040 10 10
    (by omega) moment235RowsDigit3Group10Block04 moment235RowsDigit3Group10Block05
  have h2060_2080 := moment235IndexedRows_append (3 : Fin 5) 2060 10 10
    (by omega) moment235RowsDigit3Group10Block06 moment235RowsDigit3Group10Block07
  have h2080_2100 := moment235IndexedRows_append (3 : Fin 5) 2080 10 10
    (by omega) moment235RowsDigit3Group10Block08 moment235RowsDigit3Group10Block09
  have h2100_2120 := moment235IndexedRows_append (3 : Fin 5) 2100 10 10
    (by omega) moment235RowsDigit3Group10Block10 moment235RowsDigit3Group10Block11
  have h2120_2140 := moment235IndexedRows_append (3 : Fin 5) 2120 10 10
    (by omega) moment235RowsDigit3Group10Block12 moment235RowsDigit3Group10Block13
  have h2140_2160 := moment235IndexedRows_append (3 : Fin 5) 2140 10 10
    (by omega) moment235RowsDigit3Group10Block14 moment235RowsDigit3Group10Block15
  have h2160_2180 := moment235IndexedRows_append (3 : Fin 5) 2160 10 10
    (by omega) moment235RowsDigit3Group10Block16 moment235RowsDigit3Group10Block17
  have h2180_2200 := moment235IndexedRows_append (3 : Fin 5) 2180 10 10
    (by omega) moment235RowsDigit3Group10Block18 moment235RowsDigit3Group10Block19
  have h2000_2040 := moment235IndexedRows_append (3 : Fin 5) 2000 20 20
    (by omega) h2000_2020 h2020_2040
  have h2040_2080 := moment235IndexedRows_append (3 : Fin 5) 2040 20 20
    (by omega) h2040_2060 h2060_2080
  have h2080_2120 := moment235IndexedRows_append (3 : Fin 5) 2080 20 20
    (by omega) h2080_2100 h2100_2120
  have h2120_2160 := moment235IndexedRows_append (3 : Fin 5) 2120 20 20
    (by omega) h2120_2140 h2140_2160
  have h2160_2200 := moment235IndexedRows_append (3 : Fin 5) 2160 20 20
    (by omega) h2160_2180 h2180_2200
  have h2000_2080 := moment235IndexedRows_append (3 : Fin 5) 2000 40 40
    (by omega) h2000_2040 h2040_2080
  have h2080_2160 := moment235IndexedRows_append (3 : Fin 5) 2080 40 40
    (by omega) h2080_2120 h2120_2160
  have h2000_2160 := moment235IndexedRows_append (3 : Fin 5) 2000 80 80
    (by omega) h2000_2080 h2080_2160
  exact moment235IndexedRows_append (3 : Fin 5) 2000 160 40
    (by omega) h2000_2160 h2160_2200

end PrimesRestrictedDigits
