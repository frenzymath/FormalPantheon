import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentRowsDigit2Group00
import PrimesRestrictedDigits.Fourier.FirstMomentCertificateRowAggregation

/-! Bounds for one 200-row certificate group. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

theorem firstMomentRowsDigit2Group00 :
    forall offset : Fin 200,
      firstMomentIndexedRow (2 : Fin 5)
        ⟨0 + offset.val, by omega⟩ := by
  have h0_20 := firstMomentIndexedRows_append (2 : Fin 5) 0 10 10
    (by omega) firstMomentRowsDigit2Group00Block00 firstMomentRowsDigit2Group00Block01
  have h20_40 := firstMomentIndexedRows_append (2 : Fin 5) 20 10 10
    (by omega) firstMomentRowsDigit2Group00Block02 firstMomentRowsDigit2Group00Block03
  have h40_60 := firstMomentIndexedRows_append (2 : Fin 5) 40 10 10
    (by omega) firstMomentRowsDigit2Group00Block04 firstMomentRowsDigit2Group00Block05
  have h60_80 := firstMomentIndexedRows_append (2 : Fin 5) 60 10 10
    (by omega) firstMomentRowsDigit2Group00Block06 firstMomentRowsDigit2Group00Block07
  have h80_100 := firstMomentIndexedRows_append (2 : Fin 5) 80 10 10
    (by omega) firstMomentRowsDigit2Group00Block08 firstMomentRowsDigit2Group00Block09
  have h100_120 := firstMomentIndexedRows_append (2 : Fin 5) 100 10 10
    (by omega) firstMomentRowsDigit2Group00Block10 firstMomentRowsDigit2Group00Block11
  have h120_140 := firstMomentIndexedRows_append (2 : Fin 5) 120 10 10
    (by omega) firstMomentRowsDigit2Group00Block12 firstMomentRowsDigit2Group00Block13
  have h140_160 := firstMomentIndexedRows_append (2 : Fin 5) 140 10 10
    (by omega) firstMomentRowsDigit2Group00Block14 firstMomentRowsDigit2Group00Block15
  have h160_180 := firstMomentIndexedRows_append (2 : Fin 5) 160 10 10
    (by omega) firstMomentRowsDigit2Group00Block16 firstMomentRowsDigit2Group00Block17
  have h180_200 := firstMomentIndexedRows_append (2 : Fin 5) 180 10 10
    (by omega) firstMomentRowsDigit2Group00Block18 firstMomentRowsDigit2Group00Block19
  have h0_40 := firstMomentIndexedRows_append (2 : Fin 5) 0 20 20
    (by omega) h0_20 h20_40
  have h40_80 := firstMomentIndexedRows_append (2 : Fin 5) 40 20 20
    (by omega) h40_60 h60_80
  have h80_120 := firstMomentIndexedRows_append (2 : Fin 5) 80 20 20
    (by omega) h80_100 h100_120
  have h120_160 := firstMomentIndexedRows_append (2 : Fin 5) 120 20 20
    (by omega) h120_140 h140_160
  have h160_200 := firstMomentIndexedRows_append (2 : Fin 5) 160 20 20
    (by omega) h160_180 h180_200
  have h0_80 := firstMomentIndexedRows_append (2 : Fin 5) 0 40 40
    (by omega) h0_40 h40_80
  have h80_160 := firstMomentIndexedRows_append (2 : Fin 5) 80 40 40
    (by omega) h80_120 h120_160
  have h0_160 := firstMomentIndexedRows_append (2 : Fin 5) 0 80 80
    (by omega) h0_80 h80_160
  exact firstMomentIndexedRows_append (2 : Fin 5) 0 160 40
    (by omega) h0_160 h160_200

end PrimesRestrictedDigits
