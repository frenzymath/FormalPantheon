import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentRowsDigit3Group24Result
import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentRowsDigit3Group12Result
import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentRowsDigit3Group15Result
import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentRowsDigit3Group18Result
import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentRowsDigit3Group21Result

/-! Bounds and reflection for all digit-3 certificate rows. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

theorem firstMomentRowsDigit3LowerHalf :
    forall future : Fin 5000,
      firstMomentIndexedRow (3 : Fin 5)
        ⟨future.val, lt_trans future.isLt (by omega)⟩ := by
  have h0_400 := firstMomentIndexedRows_append (3 : Fin 5) 0 200 200
    (by omega) firstMomentRowsDigit3Group00 firstMomentRowsDigit3Group01
  have h400_800 := firstMomentIndexedRows_append (3 : Fin 5) 400 200 200
    (by omega) firstMomentRowsDigit3Group02 firstMomentRowsDigit3Group03
  have h800_1200 := firstMomentIndexedRows_append (3 : Fin 5) 800 200 200
    (by omega) firstMomentRowsDigit3Group04 firstMomentRowsDigit3Group05
  have h1200_1600 := firstMomentIndexedRows_append (3 : Fin 5) 1200 200 200
    (by omega) firstMomentRowsDigit3Group06 firstMomentRowsDigit3Group07
  have h1600_2000 := firstMomentIndexedRows_append (3 : Fin 5) 1600 200 200
    (by omega) firstMomentRowsDigit3Group08 firstMomentRowsDigit3Group09
  have h2000_2400 := firstMomentIndexedRows_append (3 : Fin 5) 2000 200 200
    (by omega) firstMomentRowsDigit3Group10 firstMomentRowsDigit3Group11
  have h2400_2800 := firstMomentIndexedRows_append (3 : Fin 5) 2400 200 200
    (by omega) firstMomentRowsDigit3Group12 firstMomentRowsDigit3Group13
  have h2800_3200 := firstMomentIndexedRows_append (3 : Fin 5) 2800 200 200
    (by omega) firstMomentRowsDigit3Group14 firstMomentRowsDigit3Group15
  have h3200_3600 := firstMomentIndexedRows_append (3 : Fin 5) 3200 200 200
    (by omega) firstMomentRowsDigit3Group16 firstMomentRowsDigit3Group17
  have h3600_4000 := firstMomentIndexedRows_append (3 : Fin 5) 3600 200 200
    (by omega) firstMomentRowsDigit3Group18 firstMomentRowsDigit3Group19
  have h4000_4400 := firstMomentIndexedRows_append (3 : Fin 5) 4000 200 200
    (by omega) firstMomentRowsDigit3Group20 firstMomentRowsDigit3Group21
  have h4400_4800 := firstMomentIndexedRows_append (3 : Fin 5) 4400 200 200
    (by omega) firstMomentRowsDigit3Group22 firstMomentRowsDigit3Group23
  have h0_800 := firstMomentIndexedRows_append (3 : Fin 5) 0 400 400
    (by omega) h0_400 h400_800
  have h800_1600 := firstMomentIndexedRows_append (3 : Fin 5) 800 400 400
    (by omega) h800_1200 h1200_1600
  have h1600_2400 := firstMomentIndexedRows_append (3 : Fin 5) 1600 400 400
    (by omega) h1600_2000 h2000_2400
  have h2400_3200 := firstMomentIndexedRows_append (3 : Fin 5) 2400 400 400
    (by omega) h2400_2800 h2800_3200
  have h3200_4000 := firstMomentIndexedRows_append (3 : Fin 5) 3200 400 400
    (by omega) h3200_3600 h3600_4000
  have h4000_4800 := firstMomentIndexedRows_append (3 : Fin 5) 4000 400 400
    (by omega) h4000_4400 h4400_4800
  have h0_1600 := firstMomentIndexedRows_append (3 : Fin 5) 0 800 800
    (by omega) h0_800 h800_1600
  have h1600_3200 := firstMomentIndexedRows_append (3 : Fin 5) 1600 800 800
    (by omega) h1600_2400 h2400_3200
  have h3200_4800 := firstMomentIndexedRows_append (3 : Fin 5) 3200 800 800
    (by omega) h3200_4000 h4000_4800
  have h0_3200 := firstMomentIndexedRows_append (3 : Fin 5) 0 1600 1600
    (by omega) h0_1600 h1600_3200
  have h3200_5000 := firstMomentIndexedRows_append (3 : Fin 5) 3200 1600 200
    (by omega) h3200_4800 firstMomentRowsDigit3Group24
  have h0_5000 := firstMomentIndexedRows_append (3 : Fin 5) 0 3200 1800
    (by omega) h0_3200 h3200_5000
  intro future
  simpa using h0_5000 future

theorem firstMomentRowsDigit3 :
    forall future : Fin 10000,
      firstMomentIndexedRow (3 : Fin 5) future :=
  firstMomentIndexedRow_of_lowerHalf (3 : Fin 5)
    firstMomentRowsDigit3LowerHalf

end PrimesRestrictedDigits
