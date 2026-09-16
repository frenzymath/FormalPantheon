import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentRowsDigit1Group21
import PrimesRestrictedDigits.Fourier.FirstMomentCertificateRowAggregation

/-! Bounds for one 200-row certificate group. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

theorem firstMomentRowsDigit1Group21 :
    forall offset : Fin 200,
      firstMomentIndexedRow (1 : Fin 5)
        ⟨4200 + offset.val, by omega⟩ := by
  have h4200_4220 := firstMomentIndexedRows_append (1 : Fin 5) 4200 10 10
    (by omega) firstMomentRowsDigit1Group21Block00 firstMomentRowsDigit1Group21Block01
  have h4220_4240 := firstMomentIndexedRows_append (1 : Fin 5) 4220 10 10
    (by omega) firstMomentRowsDigit1Group21Block02 firstMomentRowsDigit1Group21Block03
  have h4240_4260 := firstMomentIndexedRows_append (1 : Fin 5) 4240 10 10
    (by omega) firstMomentRowsDigit1Group21Block04 firstMomentRowsDigit1Group21Block05
  have h4260_4280 := firstMomentIndexedRows_append (1 : Fin 5) 4260 10 10
    (by omega) firstMomentRowsDigit1Group21Block06 firstMomentRowsDigit1Group21Block07
  have h4280_4300 := firstMomentIndexedRows_append (1 : Fin 5) 4280 10 10
    (by omega) firstMomentRowsDigit1Group21Block08 firstMomentRowsDigit1Group21Block09
  have h4300_4320 := firstMomentIndexedRows_append (1 : Fin 5) 4300 10 10
    (by omega) firstMomentRowsDigit1Group21Block10 firstMomentRowsDigit1Group21Block11
  have h4320_4340 := firstMomentIndexedRows_append (1 : Fin 5) 4320 10 10
    (by omega) firstMomentRowsDigit1Group21Block12 firstMomentRowsDigit1Group21Block13
  have h4340_4360 := firstMomentIndexedRows_append (1 : Fin 5) 4340 10 10
    (by omega) firstMomentRowsDigit1Group21Block14 firstMomentRowsDigit1Group21Block15
  have h4360_4380 := firstMomentIndexedRows_append (1 : Fin 5) 4360 10 10
    (by omega) firstMomentRowsDigit1Group21Block16 firstMomentRowsDigit1Group21Block17
  have h4380_4400 := firstMomentIndexedRows_append (1 : Fin 5) 4380 10 10
    (by omega) firstMomentRowsDigit1Group21Block18 firstMomentRowsDigit1Group21Block19
  have h4200_4240 := firstMomentIndexedRows_append (1 : Fin 5) 4200 20 20
    (by omega) h4200_4220 h4220_4240
  have h4240_4280 := firstMomentIndexedRows_append (1 : Fin 5) 4240 20 20
    (by omega) h4240_4260 h4260_4280
  have h4280_4320 := firstMomentIndexedRows_append (1 : Fin 5) 4280 20 20
    (by omega) h4280_4300 h4300_4320
  have h4320_4360 := firstMomentIndexedRows_append (1 : Fin 5) 4320 20 20
    (by omega) h4320_4340 h4340_4360
  have h4360_4400 := firstMomentIndexedRows_append (1 : Fin 5) 4360 20 20
    (by omega) h4360_4380 h4380_4400
  have h4200_4280 := firstMomentIndexedRows_append (1 : Fin 5) 4200 40 40
    (by omega) h4200_4240 h4240_4280
  have h4280_4360 := firstMomentIndexedRows_append (1 : Fin 5) 4280 40 40
    (by omega) h4280_4320 h4320_4360
  have h4200_4360 := firstMomentIndexedRows_append (1 : Fin 5) 4200 80 80
    (by omega) h4200_4280 h4280_4360
  exact firstMomentIndexedRows_append (1 : Fin 5) 4200 160 40
    (by omega) h4200_4360 h4360_4400

end PrimesRestrictedDigits
