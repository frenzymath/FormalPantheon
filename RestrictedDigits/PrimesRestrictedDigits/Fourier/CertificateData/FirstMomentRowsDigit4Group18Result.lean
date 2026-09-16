import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentRowsDigit4Group18
import PrimesRestrictedDigits.Fourier.FirstMomentCertificateRowAggregation

/-! Bounds for one 200-row certificate group. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

theorem firstMomentRowsDigit4Group18 :
    forall offset : Fin 200,
      firstMomentIndexedRow (4 : Fin 5)
        ⟨3600 + offset.val, by omega⟩ := by
  have h3600_3620 := firstMomentIndexedRows_append (4 : Fin 5) 3600 10 10
    (by omega) firstMomentRowsDigit4Group18Block00 firstMomentRowsDigit4Group18Block01
  have h3620_3640 := firstMomentIndexedRows_append (4 : Fin 5) 3620 10 10
    (by omega) firstMomentRowsDigit4Group18Block02 firstMomentRowsDigit4Group18Block03
  have h3640_3660 := firstMomentIndexedRows_append (4 : Fin 5) 3640 10 10
    (by omega) firstMomentRowsDigit4Group18Block04 firstMomentRowsDigit4Group18Block05
  have h3660_3680 := firstMomentIndexedRows_append (4 : Fin 5) 3660 10 10
    (by omega) firstMomentRowsDigit4Group18Block06 firstMomentRowsDigit4Group18Block07
  have h3680_3700 := firstMomentIndexedRows_append (4 : Fin 5) 3680 10 10
    (by omega) firstMomentRowsDigit4Group18Block08 firstMomentRowsDigit4Group18Block09
  have h3700_3720 := firstMomentIndexedRows_append (4 : Fin 5) 3700 10 10
    (by omega) firstMomentRowsDigit4Group18Block10 firstMomentRowsDigit4Group18Block11
  have h3720_3740 := firstMomentIndexedRows_append (4 : Fin 5) 3720 10 10
    (by omega) firstMomentRowsDigit4Group18Block12 firstMomentRowsDigit4Group18Block13
  have h3740_3760 := firstMomentIndexedRows_append (4 : Fin 5) 3740 10 10
    (by omega) firstMomentRowsDigit4Group18Block14 firstMomentRowsDigit4Group18Block15
  have h3760_3780 := firstMomentIndexedRows_append (4 : Fin 5) 3760 10 10
    (by omega) firstMomentRowsDigit4Group18Block16 firstMomentRowsDigit4Group18Block17
  have h3780_3800 := firstMomentIndexedRows_append (4 : Fin 5) 3780 10 10
    (by omega) firstMomentRowsDigit4Group18Block18 firstMomentRowsDigit4Group18Block19
  have h3600_3640 := firstMomentIndexedRows_append (4 : Fin 5) 3600 20 20
    (by omega) h3600_3620 h3620_3640
  have h3640_3680 := firstMomentIndexedRows_append (4 : Fin 5) 3640 20 20
    (by omega) h3640_3660 h3660_3680
  have h3680_3720 := firstMomentIndexedRows_append (4 : Fin 5) 3680 20 20
    (by omega) h3680_3700 h3700_3720
  have h3720_3760 := firstMomentIndexedRows_append (4 : Fin 5) 3720 20 20
    (by omega) h3720_3740 h3740_3760
  have h3760_3800 := firstMomentIndexedRows_append (4 : Fin 5) 3760 20 20
    (by omega) h3760_3780 h3780_3800
  have h3600_3680 := firstMomentIndexedRows_append (4 : Fin 5) 3600 40 40
    (by omega) h3600_3640 h3640_3680
  have h3680_3760 := firstMomentIndexedRows_append (4 : Fin 5) 3680 40 40
    (by omega) h3680_3720 h3720_3760
  have h3600_3760 := firstMomentIndexedRows_append (4 : Fin 5) 3600 80 80
    (by omega) h3600_3680 h3680_3760
  exact firstMomentIndexedRows_append (4 : Fin 5) 3600 160 40
    (by omega) h3600_3760 h3760_3800

end PrimesRestrictedDigits
