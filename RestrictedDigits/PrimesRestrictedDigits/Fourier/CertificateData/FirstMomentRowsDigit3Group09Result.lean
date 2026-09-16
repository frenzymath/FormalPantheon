import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentRowsDigit3Group09
import PrimesRestrictedDigits.Fourier.FirstMomentCertificateRowAggregation

/-! Bounds for one 200-row certificate group. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

theorem firstMomentRowsDigit3Group09 :
    forall offset : Fin 200,
      firstMomentIndexedRow (3 : Fin 5)
        ⟨1800 + offset.val, by omega⟩ := by
  have h1800_1820 := firstMomentIndexedRows_append (3 : Fin 5) 1800 10 10
    (by omega) firstMomentRowsDigit3Group09Block00 firstMomentRowsDigit3Group09Block01
  have h1820_1840 := firstMomentIndexedRows_append (3 : Fin 5) 1820 10 10
    (by omega) firstMomentRowsDigit3Group09Block02 firstMomentRowsDigit3Group09Block03
  have h1840_1860 := firstMomentIndexedRows_append (3 : Fin 5) 1840 10 10
    (by omega) firstMomentRowsDigit3Group09Block04 firstMomentRowsDigit3Group09Block05
  have h1860_1880 := firstMomentIndexedRows_append (3 : Fin 5) 1860 10 10
    (by omega) firstMomentRowsDigit3Group09Block06 firstMomentRowsDigit3Group09Block07
  have h1880_1900 := firstMomentIndexedRows_append (3 : Fin 5) 1880 10 10
    (by omega) firstMomentRowsDigit3Group09Block08 firstMomentRowsDigit3Group09Block09
  have h1900_1920 := firstMomentIndexedRows_append (3 : Fin 5) 1900 10 10
    (by omega) firstMomentRowsDigit3Group09Block10 firstMomentRowsDigit3Group09Block11
  have h1920_1940 := firstMomentIndexedRows_append (3 : Fin 5) 1920 10 10
    (by omega) firstMomentRowsDigit3Group09Block12 firstMomentRowsDigit3Group09Block13
  have h1940_1960 := firstMomentIndexedRows_append (3 : Fin 5) 1940 10 10
    (by omega) firstMomentRowsDigit3Group09Block14 firstMomentRowsDigit3Group09Block15
  have h1960_1980 := firstMomentIndexedRows_append (3 : Fin 5) 1960 10 10
    (by omega) firstMomentRowsDigit3Group09Block16 firstMomentRowsDigit3Group09Block17
  have h1980_2000 := firstMomentIndexedRows_append (3 : Fin 5) 1980 10 10
    (by omega) firstMomentRowsDigit3Group09Block18 firstMomentRowsDigit3Group09Block19
  have h1800_1840 := firstMomentIndexedRows_append (3 : Fin 5) 1800 20 20
    (by omega) h1800_1820 h1820_1840
  have h1840_1880 := firstMomentIndexedRows_append (3 : Fin 5) 1840 20 20
    (by omega) h1840_1860 h1860_1880
  have h1880_1920 := firstMomentIndexedRows_append (3 : Fin 5) 1880 20 20
    (by omega) h1880_1900 h1900_1920
  have h1920_1960 := firstMomentIndexedRows_append (3 : Fin 5) 1920 20 20
    (by omega) h1920_1940 h1940_1960
  have h1960_2000 := firstMomentIndexedRows_append (3 : Fin 5) 1960 20 20
    (by omega) h1960_1980 h1980_2000
  have h1800_1880 := firstMomentIndexedRows_append (3 : Fin 5) 1800 40 40
    (by omega) h1800_1840 h1840_1880
  have h1880_1960 := firstMomentIndexedRows_append (3 : Fin 5) 1880 40 40
    (by omega) h1880_1920 h1920_1960
  have h1800_1960 := firstMomentIndexedRows_append (3 : Fin 5) 1800 80 80
    (by omega) h1800_1880 h1880_1960
  exact firstMomentIndexedRows_append (3 : Fin 5) 1800 160 40
    (by omega) h1800_1960 h1960_2000

end PrimesRestrictedDigits
