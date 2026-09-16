import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentRowsDigit0Group01
import PrimesRestrictedDigits.Fourier.FirstMomentCertificateRowAggregation

/-! Bounds for one 200-row certificate group. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

theorem firstMomentRowsDigit0Group01 :
    forall offset : Fin 200,
      firstMomentIndexedRow (0 : Fin 5)
        ⟨200 + offset.val, by omega⟩ := by
  have h200_220 := firstMomentIndexedRows_append (0 : Fin 5) 200 10 10
    (by omega) firstMomentRowsDigit0Group01Block00 firstMomentRowsDigit0Group01Block01
  have h220_240 := firstMomentIndexedRows_append (0 : Fin 5) 220 10 10
    (by omega) firstMomentRowsDigit0Group01Block02 firstMomentRowsDigit0Group01Block03
  have h240_260 := firstMomentIndexedRows_append (0 : Fin 5) 240 10 10
    (by omega) firstMomentRowsDigit0Group01Block04 firstMomentRowsDigit0Group01Block05
  have h260_280 := firstMomentIndexedRows_append (0 : Fin 5) 260 10 10
    (by omega) firstMomentRowsDigit0Group01Block06 firstMomentRowsDigit0Group01Block07
  have h280_300 := firstMomentIndexedRows_append (0 : Fin 5) 280 10 10
    (by omega) firstMomentRowsDigit0Group01Block08 firstMomentRowsDigit0Group01Block09
  have h300_320 := firstMomentIndexedRows_append (0 : Fin 5) 300 10 10
    (by omega) firstMomentRowsDigit0Group01Block10 firstMomentRowsDigit0Group01Block11
  have h320_340 := firstMomentIndexedRows_append (0 : Fin 5) 320 10 10
    (by omega) firstMomentRowsDigit0Group01Block12 firstMomentRowsDigit0Group01Block13
  have h340_360 := firstMomentIndexedRows_append (0 : Fin 5) 340 10 10
    (by omega) firstMomentRowsDigit0Group01Block14 firstMomentRowsDigit0Group01Block15
  have h360_380 := firstMomentIndexedRows_append (0 : Fin 5) 360 10 10
    (by omega) firstMomentRowsDigit0Group01Block16 firstMomentRowsDigit0Group01Block17
  have h380_400 := firstMomentIndexedRows_append (0 : Fin 5) 380 10 10
    (by omega) firstMomentRowsDigit0Group01Block18 firstMomentRowsDigit0Group01Block19
  have h200_240 := firstMomentIndexedRows_append (0 : Fin 5) 200 20 20
    (by omega) h200_220 h220_240
  have h240_280 := firstMomentIndexedRows_append (0 : Fin 5) 240 20 20
    (by omega) h240_260 h260_280
  have h280_320 := firstMomentIndexedRows_append (0 : Fin 5) 280 20 20
    (by omega) h280_300 h300_320
  have h320_360 := firstMomentIndexedRows_append (0 : Fin 5) 320 20 20
    (by omega) h320_340 h340_360
  have h360_400 := firstMomentIndexedRows_append (0 : Fin 5) 360 20 20
    (by omega) h360_380 h380_400
  have h200_280 := firstMomentIndexedRows_append (0 : Fin 5) 200 40 40
    (by omega) h200_240 h240_280
  have h280_360 := firstMomentIndexedRows_append (0 : Fin 5) 280 40 40
    (by omega) h280_320 h320_360
  have h200_360 := firstMomentIndexedRows_append (0 : Fin 5) 200 80 80
    (by omega) h200_280 h280_360
  exact firstMomentIndexedRows_append (0 : Fin 5) 200 160 40
    (by omega) h200_360 h360_400

end PrimesRestrictedDigits
