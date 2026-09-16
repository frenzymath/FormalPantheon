import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentRowsDigit4Group14
import PrimesRestrictedDigits.Fourier.FirstMomentCertificateRowAggregation

/-! Bounds for one 200-row certificate group. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

theorem firstMomentRowsDigit4Group14 :
    forall offset : Fin 200,
      firstMomentIndexedRow (4 : Fin 5)
        ⟨2800 + offset.val, by omega⟩ := by
  have h2800_2820 := firstMomentIndexedRows_append (4 : Fin 5) 2800 10 10
    (by omega) firstMomentRowsDigit4Group14Block00 firstMomentRowsDigit4Group14Block01
  have h2820_2840 := firstMomentIndexedRows_append (4 : Fin 5) 2820 10 10
    (by omega) firstMomentRowsDigit4Group14Block02 firstMomentRowsDigit4Group14Block03
  have h2840_2860 := firstMomentIndexedRows_append (4 : Fin 5) 2840 10 10
    (by omega) firstMomentRowsDigit4Group14Block04 firstMomentRowsDigit4Group14Block05
  have h2860_2880 := firstMomentIndexedRows_append (4 : Fin 5) 2860 10 10
    (by omega) firstMomentRowsDigit4Group14Block06 firstMomentRowsDigit4Group14Block07
  have h2880_2900 := firstMomentIndexedRows_append (4 : Fin 5) 2880 10 10
    (by omega) firstMomentRowsDigit4Group14Block08 firstMomentRowsDigit4Group14Block09
  have h2900_2920 := firstMomentIndexedRows_append (4 : Fin 5) 2900 10 10
    (by omega) firstMomentRowsDigit4Group14Block10 firstMomentRowsDigit4Group14Block11
  have h2920_2940 := firstMomentIndexedRows_append (4 : Fin 5) 2920 10 10
    (by omega) firstMomentRowsDigit4Group14Block12 firstMomentRowsDigit4Group14Block13
  have h2940_2960 := firstMomentIndexedRows_append (4 : Fin 5) 2940 10 10
    (by omega) firstMomentRowsDigit4Group14Block14 firstMomentRowsDigit4Group14Block15
  have h2960_2980 := firstMomentIndexedRows_append (4 : Fin 5) 2960 10 10
    (by omega) firstMomentRowsDigit4Group14Block16 firstMomentRowsDigit4Group14Block17
  have h2980_3000 := firstMomentIndexedRows_append (4 : Fin 5) 2980 10 10
    (by omega) firstMomentRowsDigit4Group14Block18 firstMomentRowsDigit4Group14Block19
  have h2800_2840 := firstMomentIndexedRows_append (4 : Fin 5) 2800 20 20
    (by omega) h2800_2820 h2820_2840
  have h2840_2880 := firstMomentIndexedRows_append (4 : Fin 5) 2840 20 20
    (by omega) h2840_2860 h2860_2880
  have h2880_2920 := firstMomentIndexedRows_append (4 : Fin 5) 2880 20 20
    (by omega) h2880_2900 h2900_2920
  have h2920_2960 := firstMomentIndexedRows_append (4 : Fin 5) 2920 20 20
    (by omega) h2920_2940 h2940_2960
  have h2960_3000 := firstMomentIndexedRows_append (4 : Fin 5) 2960 20 20
    (by omega) h2960_2980 h2980_3000
  have h2800_2880 := firstMomentIndexedRows_append (4 : Fin 5) 2800 40 40
    (by omega) h2800_2840 h2840_2880
  have h2880_2960 := firstMomentIndexedRows_append (4 : Fin 5) 2880 40 40
    (by omega) h2880_2920 h2920_2960
  have h2800_2960 := firstMomentIndexedRows_append (4 : Fin 5) 2800 80 80
    (by omega) h2800_2880 h2880_2960
  exact firstMomentIndexedRows_append (4 : Fin 5) 2800 160 40
    (by omega) h2800_2960 h2960_3000

end PrimesRestrictedDigits
