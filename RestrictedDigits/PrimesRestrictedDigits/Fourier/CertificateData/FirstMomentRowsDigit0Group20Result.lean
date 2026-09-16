import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentRowsDigit0Group20
import PrimesRestrictedDigits.Fourier.FirstMomentCertificateRowAggregation

/-! Bounds for one 200-row certificate group. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

theorem firstMomentRowsDigit0Group20 :
    forall offset : Fin 200,
      firstMomentIndexedRow (0 : Fin 5)
        ⟨4000 + offset.val, by omega⟩ := by
  have h4000_4020 := firstMomentIndexedRows_append (0 : Fin 5) 4000 10 10
    (by omega) firstMomentRowsDigit0Group20Block00 firstMomentRowsDigit0Group20Block01
  have h4020_4040 := firstMomentIndexedRows_append (0 : Fin 5) 4020 10 10
    (by omega) firstMomentRowsDigit0Group20Block02 firstMomentRowsDigit0Group20Block03
  have h4040_4060 := firstMomentIndexedRows_append (0 : Fin 5) 4040 10 10
    (by omega) firstMomentRowsDigit0Group20Block04 firstMomentRowsDigit0Group20Block05
  have h4060_4080 := firstMomentIndexedRows_append (0 : Fin 5) 4060 10 10
    (by omega) firstMomentRowsDigit0Group20Block06 firstMomentRowsDigit0Group20Block07
  have h4080_4100 := firstMomentIndexedRows_append (0 : Fin 5) 4080 10 10
    (by omega) firstMomentRowsDigit0Group20Block08 firstMomentRowsDigit0Group20Block09
  have h4100_4120 := firstMomentIndexedRows_append (0 : Fin 5) 4100 10 10
    (by omega) firstMomentRowsDigit0Group20Block10 firstMomentRowsDigit0Group20Block11
  have h4120_4140 := firstMomentIndexedRows_append (0 : Fin 5) 4120 10 10
    (by omega) firstMomentRowsDigit0Group20Block12 firstMomentRowsDigit0Group20Block13
  have h4140_4160 := firstMomentIndexedRows_append (0 : Fin 5) 4140 10 10
    (by omega) firstMomentRowsDigit0Group20Block14 firstMomentRowsDigit0Group20Block15
  have h4160_4180 := firstMomentIndexedRows_append (0 : Fin 5) 4160 10 10
    (by omega) firstMomentRowsDigit0Group20Block16 firstMomentRowsDigit0Group20Block17
  have h4180_4200 := firstMomentIndexedRows_append (0 : Fin 5) 4180 10 10
    (by omega) firstMomentRowsDigit0Group20Block18 firstMomentRowsDigit0Group20Block19
  have h4000_4040 := firstMomentIndexedRows_append (0 : Fin 5) 4000 20 20
    (by omega) h4000_4020 h4020_4040
  have h4040_4080 := firstMomentIndexedRows_append (0 : Fin 5) 4040 20 20
    (by omega) h4040_4060 h4060_4080
  have h4080_4120 := firstMomentIndexedRows_append (0 : Fin 5) 4080 20 20
    (by omega) h4080_4100 h4100_4120
  have h4120_4160 := firstMomentIndexedRows_append (0 : Fin 5) 4120 20 20
    (by omega) h4120_4140 h4140_4160
  have h4160_4200 := firstMomentIndexedRows_append (0 : Fin 5) 4160 20 20
    (by omega) h4160_4180 h4180_4200
  have h4000_4080 := firstMomentIndexedRows_append (0 : Fin 5) 4000 40 40
    (by omega) h4000_4040 h4040_4080
  have h4080_4160 := firstMomentIndexedRows_append (0 : Fin 5) 4080 40 40
    (by omega) h4080_4120 h4120_4160
  have h4000_4160 := firstMomentIndexedRows_append (0 : Fin 5) 4000 80 80
    (by omega) h4000_4080 h4080_4160
  exact firstMomentIndexedRows_append (0 : Fin 5) 4000 160 40
    (by omega) h4000_4160 h4160_4200

end PrimesRestrictedDigits
