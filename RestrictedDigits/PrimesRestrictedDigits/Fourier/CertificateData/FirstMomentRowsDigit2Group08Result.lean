import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentRowsDigit2Group08
import PrimesRestrictedDigits.Fourier.FirstMomentCertificateRowAggregation

/-! Bounds for one 200-row certificate group. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

theorem firstMomentRowsDigit2Group08 :
    forall offset : Fin 200,
      firstMomentIndexedRow (2 : Fin 5)
        ⟨1600 + offset.val, by omega⟩ := by
  have h1600_1620 := firstMomentIndexedRows_append (2 : Fin 5) 1600 10 10
    (by omega) firstMomentRowsDigit2Group08Block00 firstMomentRowsDigit2Group08Block01
  have h1620_1640 := firstMomentIndexedRows_append (2 : Fin 5) 1620 10 10
    (by omega) firstMomentRowsDigit2Group08Block02 firstMomentRowsDigit2Group08Block03
  have h1640_1660 := firstMomentIndexedRows_append (2 : Fin 5) 1640 10 10
    (by omega) firstMomentRowsDigit2Group08Block04 firstMomentRowsDigit2Group08Block05
  have h1660_1680 := firstMomentIndexedRows_append (2 : Fin 5) 1660 10 10
    (by omega) firstMomentRowsDigit2Group08Block06 firstMomentRowsDigit2Group08Block07
  have h1680_1700 := firstMomentIndexedRows_append (2 : Fin 5) 1680 10 10
    (by omega) firstMomentRowsDigit2Group08Block08 firstMomentRowsDigit2Group08Block09
  have h1700_1720 := firstMomentIndexedRows_append (2 : Fin 5) 1700 10 10
    (by omega) firstMomentRowsDigit2Group08Block10 firstMomentRowsDigit2Group08Block11
  have h1720_1740 := firstMomentIndexedRows_append (2 : Fin 5) 1720 10 10
    (by omega) firstMomentRowsDigit2Group08Block12 firstMomentRowsDigit2Group08Block13
  have h1740_1760 := firstMomentIndexedRows_append (2 : Fin 5) 1740 10 10
    (by omega) firstMomentRowsDigit2Group08Block14 firstMomentRowsDigit2Group08Block15
  have h1760_1780 := firstMomentIndexedRows_append (2 : Fin 5) 1760 10 10
    (by omega) firstMomentRowsDigit2Group08Block16 firstMomentRowsDigit2Group08Block17
  have h1780_1800 := firstMomentIndexedRows_append (2 : Fin 5) 1780 10 10
    (by omega) firstMomentRowsDigit2Group08Block18 firstMomentRowsDigit2Group08Block19
  have h1600_1640 := firstMomentIndexedRows_append (2 : Fin 5) 1600 20 20
    (by omega) h1600_1620 h1620_1640
  have h1640_1680 := firstMomentIndexedRows_append (2 : Fin 5) 1640 20 20
    (by omega) h1640_1660 h1660_1680
  have h1680_1720 := firstMomentIndexedRows_append (2 : Fin 5) 1680 20 20
    (by omega) h1680_1700 h1700_1720
  have h1720_1760 := firstMomentIndexedRows_append (2 : Fin 5) 1720 20 20
    (by omega) h1720_1740 h1740_1760
  have h1760_1800 := firstMomentIndexedRows_append (2 : Fin 5) 1760 20 20
    (by omega) h1760_1780 h1780_1800
  have h1600_1680 := firstMomentIndexedRows_append (2 : Fin 5) 1600 40 40
    (by omega) h1600_1640 h1640_1680
  have h1680_1760 := firstMomentIndexedRows_append (2 : Fin 5) 1680 40 40
    (by omega) h1680_1720 h1720_1760
  have h1600_1760 := firstMomentIndexedRows_append (2 : Fin 5) 1600 80 80
    (by omega) h1600_1680 h1680_1760
  exact firstMomentIndexedRows_append (2 : Fin 5) 1600 160 40
    (by omega) h1600_1760 h1760_1800

end PrimesRestrictedDigits
