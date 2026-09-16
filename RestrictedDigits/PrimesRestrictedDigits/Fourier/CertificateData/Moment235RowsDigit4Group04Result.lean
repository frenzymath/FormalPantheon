import PrimesRestrictedDigits.Fourier.CertificateData.Moment235RowsDigit4Group04
import PrimesRestrictedDigits.Fourier.Moment235CertificateRowAggregation

/-! Bounds for one 200-row certificate group. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

theorem moment235RowsDigit4Group04 :
    forall offset : Fin 200,
      moment235IndexedRow (4 : Fin 5)
        ⟨800 + offset.val, by omega⟩ := by
  have h800_820 := moment235IndexedRows_append (4 : Fin 5) 800 10 10
    (by omega) moment235RowsDigit4Group04Block00 moment235RowsDigit4Group04Block01
  have h820_840 := moment235IndexedRows_append (4 : Fin 5) 820 10 10
    (by omega) moment235RowsDigit4Group04Block02 moment235RowsDigit4Group04Block03
  have h840_860 := moment235IndexedRows_append (4 : Fin 5) 840 10 10
    (by omega) moment235RowsDigit4Group04Block04 moment235RowsDigit4Group04Block05
  have h860_880 := moment235IndexedRows_append (4 : Fin 5) 860 10 10
    (by omega) moment235RowsDigit4Group04Block06 moment235RowsDigit4Group04Block07
  have h880_900 := moment235IndexedRows_append (4 : Fin 5) 880 10 10
    (by omega) moment235RowsDigit4Group04Block08 moment235RowsDigit4Group04Block09
  have h900_920 := moment235IndexedRows_append (4 : Fin 5) 900 10 10
    (by omega) moment235RowsDigit4Group04Block10 moment235RowsDigit4Group04Block11
  have h920_940 := moment235IndexedRows_append (4 : Fin 5) 920 10 10
    (by omega) moment235RowsDigit4Group04Block12 moment235RowsDigit4Group04Block13
  have h940_960 := moment235IndexedRows_append (4 : Fin 5) 940 10 10
    (by omega) moment235RowsDigit4Group04Block14 moment235RowsDigit4Group04Block15
  have h960_980 := moment235IndexedRows_append (4 : Fin 5) 960 10 10
    (by omega) moment235RowsDigit4Group04Block16 moment235RowsDigit4Group04Block17
  have h980_1000 := moment235IndexedRows_append (4 : Fin 5) 980 10 10
    (by omega) moment235RowsDigit4Group04Block18 moment235RowsDigit4Group04Block19
  have h800_840 := moment235IndexedRows_append (4 : Fin 5) 800 20 20
    (by omega) h800_820 h820_840
  have h840_880 := moment235IndexedRows_append (4 : Fin 5) 840 20 20
    (by omega) h840_860 h860_880
  have h880_920 := moment235IndexedRows_append (4 : Fin 5) 880 20 20
    (by omega) h880_900 h900_920
  have h920_960 := moment235IndexedRows_append (4 : Fin 5) 920 20 20
    (by omega) h920_940 h940_960
  have h960_1000 := moment235IndexedRows_append (4 : Fin 5) 960 20 20
    (by omega) h960_980 h980_1000
  have h800_880 := moment235IndexedRows_append (4 : Fin 5) 800 40 40
    (by omega) h800_840 h840_880
  have h880_960 := moment235IndexedRows_append (4 : Fin 5) 880 40 40
    (by omega) h880_920 h920_960
  have h800_960 := moment235IndexedRows_append (4 : Fin 5) 800 80 80
    (by omega) h800_880 h880_960
  exact moment235IndexedRows_append (4 : Fin 5) 800 160 40
    (by omega) h800_960 h960_1000

end PrimesRestrictedDigits
