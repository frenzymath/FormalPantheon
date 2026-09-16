import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentRowsDigit3Group02
import PrimesRestrictedDigits.Fourier.FirstMomentCertificateRowAggregation

/-! Bounds for one 200-row certificate group. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

theorem firstMomentRowsDigit3Group02 :
    forall offset : Fin 200,
      firstMomentIndexedRow (3 : Fin 5)
        ⟨400 + offset.val, by omega⟩ := by
  have h400_420 := firstMomentIndexedRows_append (3 : Fin 5) 400 10 10
    (by omega) firstMomentRowsDigit3Group02Block00 firstMomentRowsDigit3Group02Block01
  have h420_440 := firstMomentIndexedRows_append (3 : Fin 5) 420 10 10
    (by omega) firstMomentRowsDigit3Group02Block02 firstMomentRowsDigit3Group02Block03
  have h440_460 := firstMomentIndexedRows_append (3 : Fin 5) 440 10 10
    (by omega) firstMomentRowsDigit3Group02Block04 firstMomentRowsDigit3Group02Block05
  have h460_480 := firstMomentIndexedRows_append (3 : Fin 5) 460 10 10
    (by omega) firstMomentRowsDigit3Group02Block06 firstMomentRowsDigit3Group02Block07
  have h480_500 := firstMomentIndexedRows_append (3 : Fin 5) 480 10 10
    (by omega) firstMomentRowsDigit3Group02Block08 firstMomentRowsDigit3Group02Block09
  have h500_520 := firstMomentIndexedRows_append (3 : Fin 5) 500 10 10
    (by omega) firstMomentRowsDigit3Group02Block10 firstMomentRowsDigit3Group02Block11
  have h520_540 := firstMomentIndexedRows_append (3 : Fin 5) 520 10 10
    (by omega) firstMomentRowsDigit3Group02Block12 firstMomentRowsDigit3Group02Block13
  have h540_560 := firstMomentIndexedRows_append (3 : Fin 5) 540 10 10
    (by omega) firstMomentRowsDigit3Group02Block14 firstMomentRowsDigit3Group02Block15
  have h560_580 := firstMomentIndexedRows_append (3 : Fin 5) 560 10 10
    (by omega) firstMomentRowsDigit3Group02Block16 firstMomentRowsDigit3Group02Block17
  have h580_600 := firstMomentIndexedRows_append (3 : Fin 5) 580 10 10
    (by omega) firstMomentRowsDigit3Group02Block18 firstMomentRowsDigit3Group02Block19
  have h400_440 := firstMomentIndexedRows_append (3 : Fin 5) 400 20 20
    (by omega) h400_420 h420_440
  have h440_480 := firstMomentIndexedRows_append (3 : Fin 5) 440 20 20
    (by omega) h440_460 h460_480
  have h480_520 := firstMomentIndexedRows_append (3 : Fin 5) 480 20 20
    (by omega) h480_500 h500_520
  have h520_560 := firstMomentIndexedRows_append (3 : Fin 5) 520 20 20
    (by omega) h520_540 h540_560
  have h560_600 := firstMomentIndexedRows_append (3 : Fin 5) 560 20 20
    (by omega) h560_580 h580_600
  have h400_480 := firstMomentIndexedRows_append (3 : Fin 5) 400 40 40
    (by omega) h400_440 h440_480
  have h480_560 := firstMomentIndexedRows_append (3 : Fin 5) 480 40 40
    (by omega) h480_520 h520_560
  have h400_560 := firstMomentIndexedRows_append (3 : Fin 5) 400 80 80
    (by omega) h400_480 h480_560
  exact firstMomentIndexedRows_append (3 : Fin 5) 400 160 40
    (by omega) h400_560 h560_600

end PrimesRestrictedDigits
