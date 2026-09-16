import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentRowsDigit4Group19
import PrimesRestrictedDigits.Fourier.FirstMomentCertificateRowAggregation

/-! Bounds for one 200-row certificate group. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

theorem firstMomentRowsDigit4Group19 :
    forall offset : Fin 200,
      firstMomentIndexedRow (4 : Fin 5)
        ⟨3800 + offset.val, by omega⟩ := by
  have h3800_3820 := firstMomentIndexedRows_append (4 : Fin 5) 3800 10 10
    (by omega) firstMomentRowsDigit4Group19Block00 firstMomentRowsDigit4Group19Block01
  have h3820_3840 := firstMomentIndexedRows_append (4 : Fin 5) 3820 10 10
    (by omega) firstMomentRowsDigit4Group19Block02 firstMomentRowsDigit4Group19Block03
  have h3840_3860 := firstMomentIndexedRows_append (4 : Fin 5) 3840 10 10
    (by omega) firstMomentRowsDigit4Group19Block04 firstMomentRowsDigit4Group19Block05
  have h3860_3880 := firstMomentIndexedRows_append (4 : Fin 5) 3860 10 10
    (by omega) firstMomentRowsDigit4Group19Block06 firstMomentRowsDigit4Group19Block07
  have h3880_3900 := firstMomentIndexedRows_append (4 : Fin 5) 3880 10 10
    (by omega) firstMomentRowsDigit4Group19Block08 firstMomentRowsDigit4Group19Block09
  have h3900_3920 := firstMomentIndexedRows_append (4 : Fin 5) 3900 10 10
    (by omega) firstMomentRowsDigit4Group19Block10 firstMomentRowsDigit4Group19Block11
  have h3920_3940 := firstMomentIndexedRows_append (4 : Fin 5) 3920 10 10
    (by omega) firstMomentRowsDigit4Group19Block12 firstMomentRowsDigit4Group19Block13
  have h3940_3960 := firstMomentIndexedRows_append (4 : Fin 5) 3940 10 10
    (by omega) firstMomentRowsDigit4Group19Block14 firstMomentRowsDigit4Group19Block15
  have h3960_3980 := firstMomentIndexedRows_append (4 : Fin 5) 3960 10 10
    (by omega) firstMomentRowsDigit4Group19Block16 firstMomentRowsDigit4Group19Block17
  have h3980_4000 := firstMomentIndexedRows_append (4 : Fin 5) 3980 10 10
    (by omega) firstMomentRowsDigit4Group19Block18 firstMomentRowsDigit4Group19Block19
  have h3800_3840 := firstMomentIndexedRows_append (4 : Fin 5) 3800 20 20
    (by omega) h3800_3820 h3820_3840
  have h3840_3880 := firstMomentIndexedRows_append (4 : Fin 5) 3840 20 20
    (by omega) h3840_3860 h3860_3880
  have h3880_3920 := firstMomentIndexedRows_append (4 : Fin 5) 3880 20 20
    (by omega) h3880_3900 h3900_3920
  have h3920_3960 := firstMomentIndexedRows_append (4 : Fin 5) 3920 20 20
    (by omega) h3920_3940 h3940_3960
  have h3960_4000 := firstMomentIndexedRows_append (4 : Fin 5) 3960 20 20
    (by omega) h3960_3980 h3980_4000
  have h3800_3880 := firstMomentIndexedRows_append (4 : Fin 5) 3800 40 40
    (by omega) h3800_3840 h3840_3880
  have h3880_3960 := firstMomentIndexedRows_append (4 : Fin 5) 3880 40 40
    (by omega) h3880_3920 h3920_3960
  have h3800_3960 := firstMomentIndexedRows_append (4 : Fin 5) 3800 80 80
    (by omega) h3800_3880 h3880_3960
  exact firstMomentIndexedRows_append (4 : Fin 5) 3800 160 40
    (by omega) h3800_3960 h3960_4000

end PrimesRestrictedDigits
