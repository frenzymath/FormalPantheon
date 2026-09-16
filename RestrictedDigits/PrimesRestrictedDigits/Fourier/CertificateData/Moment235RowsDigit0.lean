import PrimesRestrictedDigits.Fourier.CertificateData.Moment235RowsDigit0Group24Result
import PrimesRestrictedDigits.Fourier.CertificateData.Moment235RowsDigit0Group12Result

/-! Bounds and reflection for all digit-0 certificate rows. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

theorem moment235RowsDigit0LowerHalf :
    forall future : Fin 5000,
      moment235IndexedRow (0 : Fin 5)
        ⟨future.val, lt_trans future.isLt (by omega)⟩ := by
  have h0_400 := moment235IndexedRows_append (0 : Fin 5) 0 200 200
    (by omega) moment235RowsDigit0Group00 moment235RowsDigit0Group01
  have h400_800 := moment235IndexedRows_append (0 : Fin 5) 400 200 200
    (by omega) moment235RowsDigit0Group02 moment235RowsDigit0Group03
  have h800_1200 := moment235IndexedRows_append (0 : Fin 5) 800 200 200
    (by omega) moment235RowsDigit0Group04 moment235RowsDigit0Group05
  have h1200_1600 := moment235IndexedRows_append (0 : Fin 5) 1200 200 200
    (by omega) moment235RowsDigit0Group06 moment235RowsDigit0Group07
  have h1600_2000 := moment235IndexedRows_append (0 : Fin 5) 1600 200 200
    (by omega) moment235RowsDigit0Group08 moment235RowsDigit0Group09
  have h2000_2400 := moment235IndexedRows_append (0 : Fin 5) 2000 200 200
    (by omega) moment235RowsDigit0Group10 moment235RowsDigit0Group11
  have h2400_2800 := moment235IndexedRows_append (0 : Fin 5) 2400 200 200
    (by omega) moment235RowsDigit0Group12 moment235RowsDigit0Group13
  have h2800_3200 := moment235IndexedRows_append (0 : Fin 5) 2800 200 200
    (by omega) moment235RowsDigit0Group14 moment235RowsDigit0Group15
  have h3200_3600 := moment235IndexedRows_append (0 : Fin 5) 3200 200 200
    (by omega) moment235RowsDigit0Group16 moment235RowsDigit0Group17
  have h3600_4000 := moment235IndexedRows_append (0 : Fin 5) 3600 200 200
    (by omega) moment235RowsDigit0Group18 moment235RowsDigit0Group19
  have h4000_4400 := moment235IndexedRows_append (0 : Fin 5) 4000 200 200
    (by omega) moment235RowsDigit0Group20 moment235RowsDigit0Group21
  have h4400_4800 := moment235IndexedRows_append (0 : Fin 5) 4400 200 200
    (by omega) moment235RowsDigit0Group22 moment235RowsDigit0Group23
  have h0_800 := moment235IndexedRows_append (0 : Fin 5) 0 400 400
    (by omega) h0_400 h400_800
  have h800_1600 := moment235IndexedRows_append (0 : Fin 5) 800 400 400
    (by omega) h800_1200 h1200_1600
  have h1600_2400 := moment235IndexedRows_append (0 : Fin 5) 1600 400 400
    (by omega) h1600_2000 h2000_2400
  have h2400_3200 := moment235IndexedRows_append (0 : Fin 5) 2400 400 400
    (by omega) h2400_2800 h2800_3200
  have h3200_4000 := moment235IndexedRows_append (0 : Fin 5) 3200 400 400
    (by omega) h3200_3600 h3600_4000
  have h4000_4800 := moment235IndexedRows_append (0 : Fin 5) 4000 400 400
    (by omega) h4000_4400 h4400_4800
  have h0_1600 := moment235IndexedRows_append (0 : Fin 5) 0 800 800
    (by omega) h0_800 h800_1600
  have h1600_3200 := moment235IndexedRows_append (0 : Fin 5) 1600 800 800
    (by omega) h1600_2400 h2400_3200
  have h3200_4800 := moment235IndexedRows_append (0 : Fin 5) 3200 800 800
    (by omega) h3200_4000 h4000_4800
  have h0_3200 := moment235IndexedRows_append (0 : Fin 5) 0 1600 1600
    (by omega) h0_1600 h1600_3200
  have h3200_5000 := moment235IndexedRows_append (0 : Fin 5) 3200 1600 200
    (by omega) h3200_4800 moment235RowsDigit0Group24
  have h0_5000 := moment235IndexedRows_append (0 : Fin 5) 0 3200 1800
    (by omega) h0_3200 h3200_5000
  intro future
  simpa using h0_5000 future

theorem moment235RowsDigit0 :
    forall future : Fin 10000,
      moment235IndexedRow (0 : Fin 5) future :=
  moment235IndexedRow_of_lowerHalf (0 : Fin 5)
    moment235RowsDigit0LowerHalf

end PrimesRestrictedDigits
