import PrimesRestrictedDigits.Fourier.CertificateData.Moment235RowsDigit2Group18
import PrimesRestrictedDigits.Fourier.Moment235CertificateRowAggregation

/-! Bounds for one 200-row certificate group. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

theorem moment235RowsDigit2Group18 :
    forall offset : Fin 200,
      moment235IndexedRow (2 : Fin 5)
        ⟨3600 + offset.val, by omega⟩ := by
  have h3600_3620 := moment235IndexedRows_append (2 : Fin 5) 3600 10 10
    (by omega) moment235RowsDigit2Group18Block00 moment235RowsDigit2Group18Block01
  have h3620_3640 := moment235IndexedRows_append (2 : Fin 5) 3620 10 10
    (by omega) moment235RowsDigit2Group18Block02 moment235RowsDigit2Group18Block03
  have h3640_3660 := moment235IndexedRows_append (2 : Fin 5) 3640 10 10
    (by omega) moment235RowsDigit2Group18Block04 moment235RowsDigit2Group18Block05
  have h3660_3680 := moment235IndexedRows_append (2 : Fin 5) 3660 10 10
    (by omega) moment235RowsDigit2Group18Block06 moment235RowsDigit2Group18Block07
  have h3680_3700 := moment235IndexedRows_append (2 : Fin 5) 3680 10 10
    (by omega) moment235RowsDigit2Group18Block08 moment235RowsDigit2Group18Block09
  have h3700_3720 := moment235IndexedRows_append (2 : Fin 5) 3700 10 10
    (by omega) moment235RowsDigit2Group18Block10 moment235RowsDigit2Group18Block11
  have h3720_3740 := moment235IndexedRows_append (2 : Fin 5) 3720 10 10
    (by omega) moment235RowsDigit2Group18Block12 moment235RowsDigit2Group18Block13
  have h3740_3760 := moment235IndexedRows_append (2 : Fin 5) 3740 10 10
    (by omega) moment235RowsDigit2Group18Block14 moment235RowsDigit2Group18Block15
  have h3760_3780 := moment235IndexedRows_append (2 : Fin 5) 3760 10 10
    (by omega) moment235RowsDigit2Group18Block16 moment235RowsDigit2Group18Block17
  have h3780_3800 := moment235IndexedRows_append (2 : Fin 5) 3780 10 10
    (by omega) moment235RowsDigit2Group18Block18 moment235RowsDigit2Group18Block19
  have h3600_3640 := moment235IndexedRows_append (2 : Fin 5) 3600 20 20
    (by omega) h3600_3620 h3620_3640
  have h3640_3680 := moment235IndexedRows_append (2 : Fin 5) 3640 20 20
    (by omega) h3640_3660 h3660_3680
  have h3680_3720 := moment235IndexedRows_append (2 : Fin 5) 3680 20 20
    (by omega) h3680_3700 h3700_3720
  have h3720_3760 := moment235IndexedRows_append (2 : Fin 5) 3720 20 20
    (by omega) h3720_3740 h3740_3760
  have h3760_3800 := moment235IndexedRows_append (2 : Fin 5) 3760 20 20
    (by omega) h3760_3780 h3780_3800
  have h3600_3680 := moment235IndexedRows_append (2 : Fin 5) 3600 40 40
    (by omega) h3600_3640 h3640_3680
  have h3680_3760 := moment235IndexedRows_append (2 : Fin 5) 3680 40 40
    (by omega) h3680_3720 h3720_3760
  have h3600_3760 := moment235IndexedRows_append (2 : Fin 5) 3600 80 80
    (by omega) h3600_3680 h3680_3760
  exact moment235IndexedRows_append (2 : Fin 5) 3600 160 40
    (by omega) h3600_3760 h3760_3800

end PrimesRestrictedDigits
