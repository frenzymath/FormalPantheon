import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentRowsDigit1Group24
import PrimesRestrictedDigits.Fourier.FirstMomentCertificateRowAggregation

/-! Bounds for one 200-row certificate group. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

theorem firstMomentRowsDigit1Group24 :
    forall offset : Fin 200,
      firstMomentIndexedRow (1 : Fin 5)
        ⟨4800 + offset.val, by omega⟩ := by
  have h4800_4820 := firstMomentIndexedRows_append (1 : Fin 5) 4800 10 10
    (by omega) firstMomentRowsDigit1Group24Block00 firstMomentRowsDigit1Group24Block01
  have h4820_4840 := firstMomentIndexedRows_append (1 : Fin 5) 4820 10 10
    (by omega) firstMomentRowsDigit1Group24Block02 firstMomentRowsDigit1Group24Block03
  have h4840_4860 := firstMomentIndexedRows_append (1 : Fin 5) 4840 10 10
    (by omega) firstMomentRowsDigit1Group24Block04 firstMomentRowsDigit1Group24Block05
  have h4860_4880 := firstMomentIndexedRows_append (1 : Fin 5) 4860 10 10
    (by omega) firstMomentRowsDigit1Group24Block06 firstMomentRowsDigit1Group24Block07
  have h4880_4900 := firstMomentIndexedRows_append (1 : Fin 5) 4880 10 10
    (by omega) firstMomentRowsDigit1Group24Block08 firstMomentRowsDigit1Group24Block09
  have h4900_4920 := firstMomentIndexedRows_append (1 : Fin 5) 4900 10 10
    (by omega) firstMomentRowsDigit1Group24Block10 firstMomentRowsDigit1Group24Block11
  have h4920_4940 := firstMomentIndexedRows_append (1 : Fin 5) 4920 10 10
    (by omega) firstMomentRowsDigit1Group24Block12 firstMomentRowsDigit1Group24Block13
  have h4940_4960 := firstMomentIndexedRows_append (1 : Fin 5) 4940 10 10
    (by omega) firstMomentRowsDigit1Group24Block14 firstMomentRowsDigit1Group24Block15
  have h4960_4980 := firstMomentIndexedRows_append (1 : Fin 5) 4960 10 10
    (by omega) firstMomentRowsDigit1Group24Block16 firstMomentRowsDigit1Group24Block17
  have h4980_5000 := firstMomentIndexedRows_append (1 : Fin 5) 4980 10 10
    (by omega) firstMomentRowsDigit1Group24Block18 firstMomentRowsDigit1Group24Block19
  have h4800_4840 := firstMomentIndexedRows_append (1 : Fin 5) 4800 20 20
    (by omega) h4800_4820 h4820_4840
  have h4840_4880 := firstMomentIndexedRows_append (1 : Fin 5) 4840 20 20
    (by omega) h4840_4860 h4860_4880
  have h4880_4920 := firstMomentIndexedRows_append (1 : Fin 5) 4880 20 20
    (by omega) h4880_4900 h4900_4920
  have h4920_4960 := firstMomentIndexedRows_append (1 : Fin 5) 4920 20 20
    (by omega) h4920_4940 h4940_4960
  have h4960_5000 := firstMomentIndexedRows_append (1 : Fin 5) 4960 20 20
    (by omega) h4960_4980 h4980_5000
  have h4800_4880 := firstMomentIndexedRows_append (1 : Fin 5) 4800 40 40
    (by omega) h4800_4840 h4840_4880
  have h4880_4960 := firstMomentIndexedRows_append (1 : Fin 5) 4880 40 40
    (by omega) h4880_4920 h4920_4960
  have h4800_4960 := firstMomentIndexedRows_append (1 : Fin 5) 4800 80 80
    (by omega) h4800_4880 h4880_4960
  exact firstMomentIndexedRows_append (1 : Fin 5) 4800 160 40
    (by omega) h4800_4960 h4960_5000

end PrimesRestrictedDigits
