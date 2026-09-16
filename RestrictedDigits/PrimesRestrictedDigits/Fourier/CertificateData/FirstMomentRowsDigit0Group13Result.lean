import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentRowsDigit0Group13
import PrimesRestrictedDigits.Fourier.FirstMomentCertificateRowAggregation

/-! Bounds for one 200-row certificate group. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

theorem firstMomentRowsDigit0Group13 :
    forall offset : Fin 200,
      firstMomentIndexedRow (0 : Fin 5)
        ⟨2600 + offset.val, by omega⟩ := by
  have h2600_2620 := firstMomentIndexedRows_append (0 : Fin 5) 2600 10 10
    (by omega) firstMomentRowsDigit0Group13Block00 firstMomentRowsDigit0Group13Block01
  have h2620_2640 := firstMomentIndexedRows_append (0 : Fin 5) 2620 10 10
    (by omega) firstMomentRowsDigit0Group13Block02 firstMomentRowsDigit0Group13Block03
  have h2640_2660 := firstMomentIndexedRows_append (0 : Fin 5) 2640 10 10
    (by omega) firstMomentRowsDigit0Group13Block04 firstMomentRowsDigit0Group13Block05
  have h2660_2680 := firstMomentIndexedRows_append (0 : Fin 5) 2660 10 10
    (by omega) firstMomentRowsDigit0Group13Block06 firstMomentRowsDigit0Group13Block07
  have h2680_2700 := firstMomentIndexedRows_append (0 : Fin 5) 2680 10 10
    (by omega) firstMomentRowsDigit0Group13Block08 firstMomentRowsDigit0Group13Block09
  have h2700_2720 := firstMomentIndexedRows_append (0 : Fin 5) 2700 10 10
    (by omega) firstMomentRowsDigit0Group13Block10 firstMomentRowsDigit0Group13Block11
  have h2720_2740 := firstMomentIndexedRows_append (0 : Fin 5) 2720 10 10
    (by omega) firstMomentRowsDigit0Group13Block12 firstMomentRowsDigit0Group13Block13
  have h2740_2760 := firstMomentIndexedRows_append (0 : Fin 5) 2740 10 10
    (by omega) firstMomentRowsDigit0Group13Block14 firstMomentRowsDigit0Group13Block15
  have h2760_2780 := firstMomentIndexedRows_append (0 : Fin 5) 2760 10 10
    (by omega) firstMomentRowsDigit0Group13Block16 firstMomentRowsDigit0Group13Block17
  have h2780_2800 := firstMomentIndexedRows_append (0 : Fin 5) 2780 10 10
    (by omega) firstMomentRowsDigit0Group13Block18 firstMomentRowsDigit0Group13Block19
  have h2600_2640 := firstMomentIndexedRows_append (0 : Fin 5) 2600 20 20
    (by omega) h2600_2620 h2620_2640
  have h2640_2680 := firstMomentIndexedRows_append (0 : Fin 5) 2640 20 20
    (by omega) h2640_2660 h2660_2680
  have h2680_2720 := firstMomentIndexedRows_append (0 : Fin 5) 2680 20 20
    (by omega) h2680_2700 h2700_2720
  have h2720_2760 := firstMomentIndexedRows_append (0 : Fin 5) 2720 20 20
    (by omega) h2720_2740 h2740_2760
  have h2760_2800 := firstMomentIndexedRows_append (0 : Fin 5) 2760 20 20
    (by omega) h2760_2780 h2780_2800
  have h2600_2680 := firstMomentIndexedRows_append (0 : Fin 5) 2600 40 40
    (by omega) h2600_2640 h2640_2680
  have h2680_2760 := firstMomentIndexedRows_append (0 : Fin 5) 2680 40 40
    (by omega) h2680_2720 h2720_2760
  have h2600_2760 := firstMomentIndexedRows_append (0 : Fin 5) 2600 80 80
    (by omega) h2600_2680 h2680_2760
  exact firstMomentIndexedRows_append (0 : Fin 5) 2600 160 40
    (by omega) h2600_2760 h2760_2800

end PrimesRestrictedDigits
