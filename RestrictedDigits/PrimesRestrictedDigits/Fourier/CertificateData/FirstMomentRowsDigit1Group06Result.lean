import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentRowsDigit1Group06
import PrimesRestrictedDigits.Fourier.FirstMomentCertificateRowAggregation

/-! Bounds for one 200-row certificate group. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

theorem firstMomentRowsDigit1Group06 :
    forall offset : Fin 200,
      firstMomentIndexedRow (1 : Fin 5)
        ⟨1200 + offset.val, by omega⟩ := by
  have h1200_1220 := firstMomentIndexedRows_append (1 : Fin 5) 1200 10 10
    (by omega) firstMomentRowsDigit1Group06Block00 firstMomentRowsDigit1Group06Block01
  have h1220_1240 := firstMomentIndexedRows_append (1 : Fin 5) 1220 10 10
    (by omega) firstMomentRowsDigit1Group06Block02 firstMomentRowsDigit1Group06Block03
  have h1240_1260 := firstMomentIndexedRows_append (1 : Fin 5) 1240 10 10
    (by omega) firstMomentRowsDigit1Group06Block04 firstMomentRowsDigit1Group06Block05
  have h1260_1280 := firstMomentIndexedRows_append (1 : Fin 5) 1260 10 10
    (by omega) firstMomentRowsDigit1Group06Block06 firstMomentRowsDigit1Group06Block07
  have h1280_1300 := firstMomentIndexedRows_append (1 : Fin 5) 1280 10 10
    (by omega) firstMomentRowsDigit1Group06Block08 firstMomentRowsDigit1Group06Block09
  have h1300_1320 := firstMomentIndexedRows_append (1 : Fin 5) 1300 10 10
    (by omega) firstMomentRowsDigit1Group06Block10 firstMomentRowsDigit1Group06Block11
  have h1320_1340 := firstMomentIndexedRows_append (1 : Fin 5) 1320 10 10
    (by omega) firstMomentRowsDigit1Group06Block12 firstMomentRowsDigit1Group06Block13
  have h1340_1360 := firstMomentIndexedRows_append (1 : Fin 5) 1340 10 10
    (by omega) firstMomentRowsDigit1Group06Block14 firstMomentRowsDigit1Group06Block15
  have h1360_1380 := firstMomentIndexedRows_append (1 : Fin 5) 1360 10 10
    (by omega) firstMomentRowsDigit1Group06Block16 firstMomentRowsDigit1Group06Block17
  have h1380_1400 := firstMomentIndexedRows_append (1 : Fin 5) 1380 10 10
    (by omega) firstMomentRowsDigit1Group06Block18 firstMomentRowsDigit1Group06Block19
  have h1200_1240 := firstMomentIndexedRows_append (1 : Fin 5) 1200 20 20
    (by omega) h1200_1220 h1220_1240
  have h1240_1280 := firstMomentIndexedRows_append (1 : Fin 5) 1240 20 20
    (by omega) h1240_1260 h1260_1280
  have h1280_1320 := firstMomentIndexedRows_append (1 : Fin 5) 1280 20 20
    (by omega) h1280_1300 h1300_1320
  have h1320_1360 := firstMomentIndexedRows_append (1 : Fin 5) 1320 20 20
    (by omega) h1320_1340 h1340_1360
  have h1360_1400 := firstMomentIndexedRows_append (1 : Fin 5) 1360 20 20
    (by omega) h1360_1380 h1380_1400
  have h1200_1280 := firstMomentIndexedRows_append (1 : Fin 5) 1200 40 40
    (by omega) h1200_1240 h1240_1280
  have h1280_1360 := firstMomentIndexedRows_append (1 : Fin 5) 1280 40 40
    (by omega) h1280_1320 h1320_1360
  have h1200_1360 := firstMomentIndexedRows_append (1 : Fin 5) 1200 80 80
    (by omega) h1200_1280 h1280_1360
  exact firstMomentIndexedRows_append (1 : Fin 5) 1200 160 40
    (by omega) h1200_1360 h1360_1400

end PrimesRestrictedDigits
