import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentRowsDigit0Group11
import PrimesRestrictedDigits.Fourier.FirstMomentCertificateRowAggregation

/-! Bounds for one 200-row certificate group. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

theorem firstMomentRowsDigit0Group11 :
    forall offset : Fin 200,
      firstMomentIndexedRow (0 : Fin 5)
        ⟨2200 + offset.val, by omega⟩ := by
  have h2200_2220 := firstMomentIndexedRows_append (0 : Fin 5) 2200 10 10
    (by omega) firstMomentRowsDigit0Group11Block00 firstMomentRowsDigit0Group11Block01
  have h2220_2240 := firstMomentIndexedRows_append (0 : Fin 5) 2220 10 10
    (by omega) firstMomentRowsDigit0Group11Block02 firstMomentRowsDigit0Group11Block03
  have h2240_2260 := firstMomentIndexedRows_append (0 : Fin 5) 2240 10 10
    (by omega) firstMomentRowsDigit0Group11Block04 firstMomentRowsDigit0Group11Block05
  have h2260_2280 := firstMomentIndexedRows_append (0 : Fin 5) 2260 10 10
    (by omega) firstMomentRowsDigit0Group11Block06 firstMomentRowsDigit0Group11Block07
  have h2280_2300 := firstMomentIndexedRows_append (0 : Fin 5) 2280 10 10
    (by omega) firstMomentRowsDigit0Group11Block08 firstMomentRowsDigit0Group11Block09
  have h2300_2320 := firstMomentIndexedRows_append (0 : Fin 5) 2300 10 10
    (by omega) firstMomentRowsDigit0Group11Block10 firstMomentRowsDigit0Group11Block11
  have h2320_2340 := firstMomentIndexedRows_append (0 : Fin 5) 2320 10 10
    (by omega) firstMomentRowsDigit0Group11Block12 firstMomentRowsDigit0Group11Block13
  have h2340_2360 := firstMomentIndexedRows_append (0 : Fin 5) 2340 10 10
    (by omega) firstMomentRowsDigit0Group11Block14 firstMomentRowsDigit0Group11Block15
  have h2360_2380 := firstMomentIndexedRows_append (0 : Fin 5) 2360 10 10
    (by omega) firstMomentRowsDigit0Group11Block16 firstMomentRowsDigit0Group11Block17
  have h2380_2400 := firstMomentIndexedRows_append (0 : Fin 5) 2380 10 10
    (by omega) firstMomentRowsDigit0Group11Block18 firstMomentRowsDigit0Group11Block19
  have h2200_2240 := firstMomentIndexedRows_append (0 : Fin 5) 2200 20 20
    (by omega) h2200_2220 h2220_2240
  have h2240_2280 := firstMomentIndexedRows_append (0 : Fin 5) 2240 20 20
    (by omega) h2240_2260 h2260_2280
  have h2280_2320 := firstMomentIndexedRows_append (0 : Fin 5) 2280 20 20
    (by omega) h2280_2300 h2300_2320
  have h2320_2360 := firstMomentIndexedRows_append (0 : Fin 5) 2320 20 20
    (by omega) h2320_2340 h2340_2360
  have h2360_2400 := firstMomentIndexedRows_append (0 : Fin 5) 2360 20 20
    (by omega) h2360_2380 h2380_2400
  have h2200_2280 := firstMomentIndexedRows_append (0 : Fin 5) 2200 40 40
    (by omega) h2200_2240 h2240_2280
  have h2280_2360 := firstMomentIndexedRows_append (0 : Fin 5) 2280 40 40
    (by omega) h2280_2320 h2320_2360
  have h2200_2360 := firstMomentIndexedRows_append (0 : Fin 5) 2200 80 80
    (by omega) h2200_2280 h2280_2360
  exact firstMomentIndexedRows_append (0 : Fin 5) 2200 160 40
    (by omega) h2200_2360 h2360_2400

end PrimesRestrictedDigits
