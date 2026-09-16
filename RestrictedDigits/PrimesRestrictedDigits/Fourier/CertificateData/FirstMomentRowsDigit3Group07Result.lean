import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentRowsDigit3Group07
import PrimesRestrictedDigits.Fourier.FirstMomentCertificateRowAggregation

/-! Bounds for one 200-row certificate group. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

theorem firstMomentRowsDigit3Group07 :
    forall offset : Fin 200,
      firstMomentIndexedRow (3 : Fin 5)
        ⟨1400 + offset.val, by omega⟩ := by
  have h1400_1420 := firstMomentIndexedRows_append (3 : Fin 5) 1400 10 10
    (by omega) firstMomentRowsDigit3Group07Block00 firstMomentRowsDigit3Group07Block01
  have h1420_1440 := firstMomentIndexedRows_append (3 : Fin 5) 1420 10 10
    (by omega) firstMomentRowsDigit3Group07Block02 firstMomentRowsDigit3Group07Block03
  have h1440_1460 := firstMomentIndexedRows_append (3 : Fin 5) 1440 10 10
    (by omega) firstMomentRowsDigit3Group07Block04 firstMomentRowsDigit3Group07Block05
  have h1460_1480 := firstMomentIndexedRows_append (3 : Fin 5) 1460 10 10
    (by omega) firstMomentRowsDigit3Group07Block06 firstMomentRowsDigit3Group07Block07
  have h1480_1500 := firstMomentIndexedRows_append (3 : Fin 5) 1480 10 10
    (by omega) firstMomentRowsDigit3Group07Block08 firstMomentRowsDigit3Group07Block09
  have h1500_1520 := firstMomentIndexedRows_append (3 : Fin 5) 1500 10 10
    (by omega) firstMomentRowsDigit3Group07Block10 firstMomentRowsDigit3Group07Block11
  have h1520_1540 := firstMomentIndexedRows_append (3 : Fin 5) 1520 10 10
    (by omega) firstMomentRowsDigit3Group07Block12 firstMomentRowsDigit3Group07Block13
  have h1540_1560 := firstMomentIndexedRows_append (3 : Fin 5) 1540 10 10
    (by omega) firstMomentRowsDigit3Group07Block14 firstMomentRowsDigit3Group07Block15
  have h1560_1580 := firstMomentIndexedRows_append (3 : Fin 5) 1560 10 10
    (by omega) firstMomentRowsDigit3Group07Block16 firstMomentRowsDigit3Group07Block17
  have h1580_1600 := firstMomentIndexedRows_append (3 : Fin 5) 1580 10 10
    (by omega) firstMomentRowsDigit3Group07Block18 firstMomentRowsDigit3Group07Block19
  have h1400_1440 := firstMomentIndexedRows_append (3 : Fin 5) 1400 20 20
    (by omega) h1400_1420 h1420_1440
  have h1440_1480 := firstMomentIndexedRows_append (3 : Fin 5) 1440 20 20
    (by omega) h1440_1460 h1460_1480
  have h1480_1520 := firstMomentIndexedRows_append (3 : Fin 5) 1480 20 20
    (by omega) h1480_1500 h1500_1520
  have h1520_1560 := firstMomentIndexedRows_append (3 : Fin 5) 1520 20 20
    (by omega) h1520_1540 h1540_1560
  have h1560_1600 := firstMomentIndexedRows_append (3 : Fin 5) 1560 20 20
    (by omega) h1560_1580 h1580_1600
  have h1400_1480 := firstMomentIndexedRows_append (3 : Fin 5) 1400 40 40
    (by omega) h1400_1440 h1440_1480
  have h1480_1560 := firstMomentIndexedRows_append (3 : Fin 5) 1480 40 40
    (by omega) h1480_1520 h1520_1560
  have h1400_1560 := firstMomentIndexedRows_append (3 : Fin 5) 1400 80 80
    (by omega) h1400_1480 h1480_1560
  exact firstMomentIndexedRows_append (3 : Fin 5) 1400 160 40
    (by omega) h1400_1560 h1560_1600

end PrimesRestrictedDigits
