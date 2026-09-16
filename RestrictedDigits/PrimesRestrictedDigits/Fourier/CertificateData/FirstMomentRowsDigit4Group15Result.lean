import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentRowsDigit4Group15
import PrimesRestrictedDigits.Fourier.FirstMomentCertificateRowAggregation

/-! Bounds for one 200-row certificate group. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

theorem firstMomentRowsDigit4Group15 :
    forall offset : Fin 200,
      firstMomentIndexedRow (4 : Fin 5)
        ⟨3000 + offset.val, by omega⟩ := by
  have h3000_3020 := firstMomentIndexedRows_append (4 : Fin 5) 3000 10 10
    (by omega) firstMomentRowsDigit4Group15Block00 firstMomentRowsDigit4Group15Block01
  have h3020_3040 := firstMomentIndexedRows_append (4 : Fin 5) 3020 10 10
    (by omega) firstMomentRowsDigit4Group15Block02 firstMomentRowsDigit4Group15Block03
  have h3040_3060 := firstMomentIndexedRows_append (4 : Fin 5) 3040 10 10
    (by omega) firstMomentRowsDigit4Group15Block04 firstMomentRowsDigit4Group15Block05
  have h3060_3080 := firstMomentIndexedRows_append (4 : Fin 5) 3060 10 10
    (by omega) firstMomentRowsDigit4Group15Block06 firstMomentRowsDigit4Group15Block07
  have h3080_3100 := firstMomentIndexedRows_append (4 : Fin 5) 3080 10 10
    (by omega) firstMomentRowsDigit4Group15Block08 firstMomentRowsDigit4Group15Block09
  have h3100_3120 := firstMomentIndexedRows_append (4 : Fin 5) 3100 10 10
    (by omega) firstMomentRowsDigit4Group15Block10 firstMomentRowsDigit4Group15Block11
  have h3120_3140 := firstMomentIndexedRows_append (4 : Fin 5) 3120 10 10
    (by omega) firstMomentRowsDigit4Group15Block12 firstMomentRowsDigit4Group15Block13
  have h3140_3160 := firstMomentIndexedRows_append (4 : Fin 5) 3140 10 10
    (by omega) firstMomentRowsDigit4Group15Block14 firstMomentRowsDigit4Group15Block15
  have h3160_3180 := firstMomentIndexedRows_append (4 : Fin 5) 3160 10 10
    (by omega) firstMomentRowsDigit4Group15Block16 firstMomentRowsDigit4Group15Block17
  have h3180_3200 := firstMomentIndexedRows_append (4 : Fin 5) 3180 10 10
    (by omega) firstMomentRowsDigit4Group15Block18 firstMomentRowsDigit4Group15Block19
  have h3000_3040 := firstMomentIndexedRows_append (4 : Fin 5) 3000 20 20
    (by omega) h3000_3020 h3020_3040
  have h3040_3080 := firstMomentIndexedRows_append (4 : Fin 5) 3040 20 20
    (by omega) h3040_3060 h3060_3080
  have h3080_3120 := firstMomentIndexedRows_append (4 : Fin 5) 3080 20 20
    (by omega) h3080_3100 h3100_3120
  have h3120_3160 := firstMomentIndexedRows_append (4 : Fin 5) 3120 20 20
    (by omega) h3120_3140 h3140_3160
  have h3160_3200 := firstMomentIndexedRows_append (4 : Fin 5) 3160 20 20
    (by omega) h3160_3180 h3180_3200
  have h3000_3080 := firstMomentIndexedRows_append (4 : Fin 5) 3000 40 40
    (by omega) h3000_3040 h3040_3080
  have h3080_3160 := firstMomentIndexedRows_append (4 : Fin 5) 3080 40 40
    (by omega) h3080_3120 h3120_3160
  have h3000_3160 := firstMomentIndexedRows_append (4 : Fin 5) 3000 80 80
    (by omega) h3000_3080 h3080_3160
  exact firstMomentIndexedRows_append (4 : Fin 5) 3000 160 40
    (by omega) h3000_3160 h3160_3200

end PrimesRestrictedDigits
