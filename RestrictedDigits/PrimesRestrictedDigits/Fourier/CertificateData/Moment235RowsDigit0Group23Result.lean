import PrimesRestrictedDigits.Fourier.CertificateData.Moment235RowsDigit0Group23
import PrimesRestrictedDigits.Fourier.Moment235CertificateRowAggregation

/-! Bounds for one 200-row certificate group. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

theorem moment235RowsDigit0Group23 :
    forall offset : Fin 200,
      moment235IndexedRow (0 : Fin 5)
        ⟨4600 + offset.val, by omega⟩ := by
  have h4600_4620 := moment235IndexedRows_append (0 : Fin 5) 4600 10 10
    (by omega) moment235RowsDigit0Group23Block00 moment235RowsDigit0Group23Block01
  have h4620_4640 := moment235IndexedRows_append (0 : Fin 5) 4620 10 10
    (by omega) moment235RowsDigit0Group23Block02 moment235RowsDigit0Group23Block03
  have h4640_4660 := moment235IndexedRows_append (0 : Fin 5) 4640 10 10
    (by omega) moment235RowsDigit0Group23Block04 moment235RowsDigit0Group23Block05
  have h4660_4680 := moment235IndexedRows_append (0 : Fin 5) 4660 10 10
    (by omega) moment235RowsDigit0Group23Block06 moment235RowsDigit0Group23Block07
  have h4680_4700 := moment235IndexedRows_append (0 : Fin 5) 4680 10 10
    (by omega) moment235RowsDigit0Group23Block08 moment235RowsDigit0Group23Block09
  have h4700_4720 := moment235IndexedRows_append (0 : Fin 5) 4700 10 10
    (by omega) moment235RowsDigit0Group23Block10 moment235RowsDigit0Group23Block11
  have h4720_4740 := moment235IndexedRows_append (0 : Fin 5) 4720 10 10
    (by omega) moment235RowsDigit0Group23Block12 moment235RowsDigit0Group23Block13
  have h4740_4760 := moment235IndexedRows_append (0 : Fin 5) 4740 10 10
    (by omega) moment235RowsDigit0Group23Block14 moment235RowsDigit0Group23Block15
  have h4760_4780 := moment235IndexedRows_append (0 : Fin 5) 4760 10 10
    (by omega) moment235RowsDigit0Group23Block16 moment235RowsDigit0Group23Block17
  have h4780_4800 := moment235IndexedRows_append (0 : Fin 5) 4780 10 10
    (by omega) moment235RowsDigit0Group23Block18 moment235RowsDigit0Group23Block19
  have h4600_4640 := moment235IndexedRows_append (0 : Fin 5) 4600 20 20
    (by omega) h4600_4620 h4620_4640
  have h4640_4680 := moment235IndexedRows_append (0 : Fin 5) 4640 20 20
    (by omega) h4640_4660 h4660_4680
  have h4680_4720 := moment235IndexedRows_append (0 : Fin 5) 4680 20 20
    (by omega) h4680_4700 h4700_4720
  have h4720_4760 := moment235IndexedRows_append (0 : Fin 5) 4720 20 20
    (by omega) h4720_4740 h4740_4760
  have h4760_4800 := moment235IndexedRows_append (0 : Fin 5) 4760 20 20
    (by omega) h4760_4780 h4780_4800
  have h4600_4680 := moment235IndexedRows_append (0 : Fin 5) 4600 40 40
    (by omega) h4600_4640 h4640_4680
  have h4680_4760 := moment235IndexedRows_append (0 : Fin 5) 4680 40 40
    (by omega) h4680_4720 h4720_4760
  have h4600_4760 := moment235IndexedRows_append (0 : Fin 5) 4600 80 80
    (by omega) h4600_4680 h4680_4760
  exact moment235IndexedRows_append (0 : Fin 5) 4600 160 40
    (by omega) h4600_4760 h4760_4800

end PrimesRestrictedDigits
