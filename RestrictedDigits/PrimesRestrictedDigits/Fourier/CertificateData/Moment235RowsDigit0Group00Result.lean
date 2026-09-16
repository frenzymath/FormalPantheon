import PrimesRestrictedDigits.Fourier.CertificateData.Moment235RowsDigit0Group00
import PrimesRestrictedDigits.Fourier.Moment235CertificateRowAggregation

/-! Bounds for one 200-row certificate group. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

theorem moment235RowsDigit0Group00 :
    forall offset : Fin 200,
      moment235IndexedRow (0 : Fin 5)
        ⟨0 + offset.val, by omega⟩ := by
  have h0_20 := moment235IndexedRows_append (0 : Fin 5) 0 10 10
    (by omega) moment235RowsDigit0Group00Block00 moment235RowsDigit0Group00Block01
  have h20_40 := moment235IndexedRows_append (0 : Fin 5) 20 10 10
    (by omega) moment235RowsDigit0Group00Block02 moment235RowsDigit0Group00Block03
  have h40_60 := moment235IndexedRows_append (0 : Fin 5) 40 10 10
    (by omega) moment235RowsDigit0Group00Block04 moment235RowsDigit0Group00Block05
  have h60_80 := moment235IndexedRows_append (0 : Fin 5) 60 10 10
    (by omega) moment235RowsDigit0Group00Block06 moment235RowsDigit0Group00Block07
  have h80_100 := moment235IndexedRows_append (0 : Fin 5) 80 10 10
    (by omega) moment235RowsDigit0Group00Block08 moment235RowsDigit0Group00Block09
  have h100_120 := moment235IndexedRows_append (0 : Fin 5) 100 10 10
    (by omega) moment235RowsDigit0Group00Block10 moment235RowsDigit0Group00Block11
  have h120_140 := moment235IndexedRows_append (0 : Fin 5) 120 10 10
    (by omega) moment235RowsDigit0Group00Block12 moment235RowsDigit0Group00Block13
  have h140_160 := moment235IndexedRows_append (0 : Fin 5) 140 10 10
    (by omega) moment235RowsDigit0Group00Block14 moment235RowsDigit0Group00Block15
  have h160_180 := moment235IndexedRows_append (0 : Fin 5) 160 10 10
    (by omega) moment235RowsDigit0Group00Block16 moment235RowsDigit0Group00Block17
  have h180_200 := moment235IndexedRows_append (0 : Fin 5) 180 10 10
    (by omega) moment235RowsDigit0Group00Block18 moment235RowsDigit0Group00Block19
  have h0_40 := moment235IndexedRows_append (0 : Fin 5) 0 20 20
    (by omega) h0_20 h20_40
  have h40_80 := moment235IndexedRows_append (0 : Fin 5) 40 20 20
    (by omega) h40_60 h60_80
  have h80_120 := moment235IndexedRows_append (0 : Fin 5) 80 20 20
    (by omega) h80_100 h100_120
  have h120_160 := moment235IndexedRows_append (0 : Fin 5) 120 20 20
    (by omega) h120_140 h140_160
  have h160_200 := moment235IndexedRows_append (0 : Fin 5) 160 20 20
    (by omega) h160_180 h180_200
  have h0_80 := moment235IndexedRows_append (0 : Fin 5) 0 40 40
    (by omega) h0_40 h40_80
  have h80_160 := moment235IndexedRows_append (0 : Fin 5) 80 40 40
    (by omega) h80_120 h120_160
  have h0_160 := moment235IndexedRows_append (0 : Fin 5) 0 80 80
    (by omega) h0_80 h80_160
  exact moment235IndexedRows_append (0 : Fin 5) 0 160 40
    (by omega) h0_160 h160_200

end PrimesRestrictedDigits
