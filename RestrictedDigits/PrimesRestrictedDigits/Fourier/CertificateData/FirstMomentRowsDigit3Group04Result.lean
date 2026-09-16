import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentRowsDigit3Group04
import PrimesRestrictedDigits.Fourier.FirstMomentCertificateRowAggregation

/-! Bounds for one 200-row certificate group. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

theorem firstMomentRowsDigit3Group04 :
    forall offset : Fin 200,
      firstMomentIndexedRow (3 : Fin 5)
        ⟨800 + offset.val, by omega⟩ := by
  have h800_820 := firstMomentIndexedRows_append (3 : Fin 5) 800 10 10
    (by omega) firstMomentRowsDigit3Group04Block00 firstMomentRowsDigit3Group04Block01
  have h820_840 := firstMomentIndexedRows_append (3 : Fin 5) 820 10 10
    (by omega) firstMomentRowsDigit3Group04Block02 firstMomentRowsDigit3Group04Block03
  have h840_860 := firstMomentIndexedRows_append (3 : Fin 5) 840 10 10
    (by omega) firstMomentRowsDigit3Group04Block04 firstMomentRowsDigit3Group04Block05
  have h860_880 := firstMomentIndexedRows_append (3 : Fin 5) 860 10 10
    (by omega) firstMomentRowsDigit3Group04Block06 firstMomentRowsDigit3Group04Block07
  have h880_900 := firstMomentIndexedRows_append (3 : Fin 5) 880 10 10
    (by omega) firstMomentRowsDigit3Group04Block08 firstMomentRowsDigit3Group04Block09
  have h900_920 := firstMomentIndexedRows_append (3 : Fin 5) 900 10 10
    (by omega) firstMomentRowsDigit3Group04Block10 firstMomentRowsDigit3Group04Block11
  have h920_940 := firstMomentIndexedRows_append (3 : Fin 5) 920 10 10
    (by omega) firstMomentRowsDigit3Group04Block12 firstMomentRowsDigit3Group04Block13
  have h940_960 := firstMomentIndexedRows_append (3 : Fin 5) 940 10 10
    (by omega) firstMomentRowsDigit3Group04Block14 firstMomentRowsDigit3Group04Block15
  have h960_980 := firstMomentIndexedRows_append (3 : Fin 5) 960 10 10
    (by omega) firstMomentRowsDigit3Group04Block16 firstMomentRowsDigit3Group04Block17
  have h980_1000 := firstMomentIndexedRows_append (3 : Fin 5) 980 10 10
    (by omega) firstMomentRowsDigit3Group04Block18 firstMomentRowsDigit3Group04Block19
  have h800_840 := firstMomentIndexedRows_append (3 : Fin 5) 800 20 20
    (by omega) h800_820 h820_840
  have h840_880 := firstMomentIndexedRows_append (3 : Fin 5) 840 20 20
    (by omega) h840_860 h860_880
  have h880_920 := firstMomentIndexedRows_append (3 : Fin 5) 880 20 20
    (by omega) h880_900 h900_920
  have h920_960 := firstMomentIndexedRows_append (3 : Fin 5) 920 20 20
    (by omega) h920_940 h940_960
  have h960_1000 := firstMomentIndexedRows_append (3 : Fin 5) 960 20 20
    (by omega) h960_980 h980_1000
  have h800_880 := firstMomentIndexedRows_append (3 : Fin 5) 800 40 40
    (by omega) h800_840 h840_880
  have h880_960 := firstMomentIndexedRows_append (3 : Fin 5) 880 40 40
    (by omega) h880_920 h920_960
  have h800_960 := firstMomentIndexedRows_append (3 : Fin 5) 800 80 80
    (by omega) h800_880 h880_960
  exact firstMomentIndexedRows_append (3 : Fin 5) 800 160 40
    (by omega) h800_960 h960_1000

end PrimesRestrictedDigits
