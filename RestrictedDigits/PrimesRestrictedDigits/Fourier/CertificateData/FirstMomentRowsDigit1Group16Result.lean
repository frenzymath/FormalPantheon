import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentRowsDigit1Group16
import PrimesRestrictedDigits.Fourier.FirstMomentCertificateRowAggregation

/-! Bounds for one 200-row certificate group. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

theorem firstMomentRowsDigit1Group16 :
    forall offset : Fin 200,
      firstMomentIndexedRow (1 : Fin 5)
        ⟨3200 + offset.val, by omega⟩ := by
  have h3200_3220 := firstMomentIndexedRows_append (1 : Fin 5) 3200 10 10
    (by omega) firstMomentRowsDigit1Group16Block00 firstMomentRowsDigit1Group16Block01
  have h3220_3240 := firstMomentIndexedRows_append (1 : Fin 5) 3220 10 10
    (by omega) firstMomentRowsDigit1Group16Block02 firstMomentRowsDigit1Group16Block03
  have h3240_3260 := firstMomentIndexedRows_append (1 : Fin 5) 3240 10 10
    (by omega) firstMomentRowsDigit1Group16Block04 firstMomentRowsDigit1Group16Block05
  have h3260_3280 := firstMomentIndexedRows_append (1 : Fin 5) 3260 10 10
    (by omega) firstMomentRowsDigit1Group16Block06 firstMomentRowsDigit1Group16Block07
  have h3280_3300 := firstMomentIndexedRows_append (1 : Fin 5) 3280 10 10
    (by omega) firstMomentRowsDigit1Group16Block08 firstMomentRowsDigit1Group16Block09
  have h3300_3320 := firstMomentIndexedRows_append (1 : Fin 5) 3300 10 10
    (by omega) firstMomentRowsDigit1Group16Block10 firstMomentRowsDigit1Group16Block11
  have h3320_3340 := firstMomentIndexedRows_append (1 : Fin 5) 3320 10 10
    (by omega) firstMomentRowsDigit1Group16Block12 firstMomentRowsDigit1Group16Block13
  have h3340_3360 := firstMomentIndexedRows_append (1 : Fin 5) 3340 10 10
    (by omega) firstMomentRowsDigit1Group16Block14 firstMomentRowsDigit1Group16Block15
  have h3360_3380 := firstMomentIndexedRows_append (1 : Fin 5) 3360 10 10
    (by omega) firstMomentRowsDigit1Group16Block16 firstMomentRowsDigit1Group16Block17
  have h3380_3400 := firstMomentIndexedRows_append (1 : Fin 5) 3380 10 10
    (by omega) firstMomentRowsDigit1Group16Block18 firstMomentRowsDigit1Group16Block19
  have h3200_3240 := firstMomentIndexedRows_append (1 : Fin 5) 3200 20 20
    (by omega) h3200_3220 h3220_3240
  have h3240_3280 := firstMomentIndexedRows_append (1 : Fin 5) 3240 20 20
    (by omega) h3240_3260 h3260_3280
  have h3280_3320 := firstMomentIndexedRows_append (1 : Fin 5) 3280 20 20
    (by omega) h3280_3300 h3300_3320
  have h3320_3360 := firstMomentIndexedRows_append (1 : Fin 5) 3320 20 20
    (by omega) h3320_3340 h3340_3360
  have h3360_3400 := firstMomentIndexedRows_append (1 : Fin 5) 3360 20 20
    (by omega) h3360_3380 h3380_3400
  have h3200_3280 := firstMomentIndexedRows_append (1 : Fin 5) 3200 40 40
    (by omega) h3200_3240 h3240_3280
  have h3280_3360 := firstMomentIndexedRows_append (1 : Fin 5) 3280 40 40
    (by omega) h3280_3320 h3320_3360
  have h3200_3360 := firstMomentIndexedRows_append (1 : Fin 5) 3200 80 80
    (by omega) h3200_3280 h3280_3360
  exact firstMomentIndexedRows_append (1 : Fin 5) 3200 160 40
    (by omega) h3200_3360 h3360_3400

end PrimesRestrictedDigits
