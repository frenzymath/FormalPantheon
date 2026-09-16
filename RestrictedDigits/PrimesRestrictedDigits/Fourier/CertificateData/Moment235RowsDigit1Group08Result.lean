import PrimesRestrictedDigits.Fourier.CertificateData.Moment235RowsDigit1Group08
import PrimesRestrictedDigits.Fourier.Moment235CertificateRowAggregation

/-! Bounds for one 200-row certificate group. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

theorem moment235RowsDigit1Group08 :
    forall offset : Fin 200,
      moment235IndexedRow (1 : Fin 5)
        ⟨1600 + offset.val, by omega⟩ := by
  have h1600_1620 := moment235IndexedRows_append (1 : Fin 5) 1600 10 10
    (by omega) moment235RowsDigit1Group08Block00 moment235RowsDigit1Group08Block01
  have h1620_1640 := moment235IndexedRows_append (1 : Fin 5) 1620 10 10
    (by omega) moment235RowsDigit1Group08Block02 moment235RowsDigit1Group08Block03
  have h1640_1660 := moment235IndexedRows_append (1 : Fin 5) 1640 10 10
    (by omega) moment235RowsDigit1Group08Block04 moment235RowsDigit1Group08Block05
  have h1660_1680 := moment235IndexedRows_append (1 : Fin 5) 1660 10 10
    (by omega) moment235RowsDigit1Group08Block06 moment235RowsDigit1Group08Block07
  have h1680_1700 := moment235IndexedRows_append (1 : Fin 5) 1680 10 10
    (by omega) moment235RowsDigit1Group08Block08 moment235RowsDigit1Group08Block09
  have h1700_1720 := moment235IndexedRows_append (1 : Fin 5) 1700 10 10
    (by omega) moment235RowsDigit1Group08Block10 moment235RowsDigit1Group08Block11
  have h1720_1740 := moment235IndexedRows_append (1 : Fin 5) 1720 10 10
    (by omega) moment235RowsDigit1Group08Block12 moment235RowsDigit1Group08Block13
  have h1740_1760 := moment235IndexedRows_append (1 : Fin 5) 1740 10 10
    (by omega) moment235RowsDigit1Group08Block14 moment235RowsDigit1Group08Block15
  have h1760_1780 := moment235IndexedRows_append (1 : Fin 5) 1760 10 10
    (by omega) moment235RowsDigit1Group08Block16 moment235RowsDigit1Group08Block17
  have h1780_1800 := moment235IndexedRows_append (1 : Fin 5) 1780 10 10
    (by omega) moment235RowsDigit1Group08Block18 moment235RowsDigit1Group08Block19
  have h1600_1640 := moment235IndexedRows_append (1 : Fin 5) 1600 20 20
    (by omega) h1600_1620 h1620_1640
  have h1640_1680 := moment235IndexedRows_append (1 : Fin 5) 1640 20 20
    (by omega) h1640_1660 h1660_1680
  have h1680_1720 := moment235IndexedRows_append (1 : Fin 5) 1680 20 20
    (by omega) h1680_1700 h1700_1720
  have h1720_1760 := moment235IndexedRows_append (1 : Fin 5) 1720 20 20
    (by omega) h1720_1740 h1740_1760
  have h1760_1800 := moment235IndexedRows_append (1 : Fin 5) 1760 20 20
    (by omega) h1760_1780 h1780_1800
  have h1600_1680 := moment235IndexedRows_append (1 : Fin 5) 1600 40 40
    (by omega) h1600_1640 h1640_1680
  have h1680_1760 := moment235IndexedRows_append (1 : Fin 5) 1680 40 40
    (by omega) h1680_1720 h1720_1760
  have h1600_1760 := moment235IndexedRows_append (1 : Fin 5) 1600 80 80
    (by omega) h1600_1680 h1680_1760
  exact moment235IndexedRows_append (1 : Fin 5) 1600 160 40
    (by omega) h1600_1760 h1760_1800

end PrimesRestrictedDigits
