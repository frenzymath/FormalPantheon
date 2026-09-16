import PrimesRestrictedDigits.Fourier.CertificateData.Moment235RowsDigit0Group20
import PrimesRestrictedDigits.Fourier.Moment235CertificateRowAggregation

/-! Bounds for one 200-row certificate group. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

theorem moment235RowsDigit0Group20 :
    forall offset : Fin 200,
      moment235IndexedRow (0 : Fin 5)
        ⟨4000 + offset.val, by omega⟩ := by
  have h4000_4020 := moment235IndexedRows_append (0 : Fin 5) 4000 10 10
    (by omega) moment235RowsDigit0Group20Block00 moment235RowsDigit0Group20Block01
  have h4020_4040 := moment235IndexedRows_append (0 : Fin 5) 4020 10 10
    (by omega) moment235RowsDigit0Group20Block02 moment235RowsDigit0Group20Block03
  have h4040_4060 := moment235IndexedRows_append (0 : Fin 5) 4040 10 10
    (by omega) moment235RowsDigit0Group20Block04 moment235RowsDigit0Group20Block05
  have h4060_4080 := moment235IndexedRows_append (0 : Fin 5) 4060 10 10
    (by omega) moment235RowsDigit0Group20Block06 moment235RowsDigit0Group20Block07
  have h4080_4100 := moment235IndexedRows_append (0 : Fin 5) 4080 10 10
    (by omega) moment235RowsDigit0Group20Block08 moment235RowsDigit0Group20Block09
  have h4100_4120 := moment235IndexedRows_append (0 : Fin 5) 4100 10 10
    (by omega) moment235RowsDigit0Group20Block10 moment235RowsDigit0Group20Block11
  have h4120_4140 := moment235IndexedRows_append (0 : Fin 5) 4120 10 10
    (by omega) moment235RowsDigit0Group20Block12 moment235RowsDigit0Group20Block13
  have h4140_4160 := moment235IndexedRows_append (0 : Fin 5) 4140 10 10
    (by omega) moment235RowsDigit0Group20Block14 moment235RowsDigit0Group20Block15
  have h4160_4180 := moment235IndexedRows_append (0 : Fin 5) 4160 10 10
    (by omega) moment235RowsDigit0Group20Block16 moment235RowsDigit0Group20Block17
  have h4180_4200 := moment235IndexedRows_append (0 : Fin 5) 4180 10 10
    (by omega) moment235RowsDigit0Group20Block18 moment235RowsDigit0Group20Block19
  have h4000_4040 := moment235IndexedRows_append (0 : Fin 5) 4000 20 20
    (by omega) h4000_4020 h4020_4040
  have h4040_4080 := moment235IndexedRows_append (0 : Fin 5) 4040 20 20
    (by omega) h4040_4060 h4060_4080
  have h4080_4120 := moment235IndexedRows_append (0 : Fin 5) 4080 20 20
    (by omega) h4080_4100 h4100_4120
  have h4120_4160 := moment235IndexedRows_append (0 : Fin 5) 4120 20 20
    (by omega) h4120_4140 h4140_4160
  have h4160_4200 := moment235IndexedRows_append (0 : Fin 5) 4160 20 20
    (by omega) h4160_4180 h4180_4200
  have h4000_4080 := moment235IndexedRows_append (0 : Fin 5) 4000 40 40
    (by omega) h4000_4040 h4040_4080
  have h4080_4160 := moment235IndexedRows_append (0 : Fin 5) 4080 40 40
    (by omega) h4080_4120 h4120_4160
  have h4000_4160 := moment235IndexedRows_append (0 : Fin 5) 4000 80 80
    (by omega) h4000_4080 h4080_4160
  exact moment235IndexedRows_append (0 : Fin 5) 4000 160 40
    (by omega) h4000_4160 h4160_4200

end PrimesRestrictedDigits
