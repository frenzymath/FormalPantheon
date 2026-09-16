import PrimesRestrictedDigits.Fourier.CertificateData.FirstMomentRowsDigit1Group22
import PrimesRestrictedDigits.Fourier.FirstMomentCertificateRowAggregation

/-! Bounds for one 200-row certificate group. -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace PrimesRestrictedDigits

theorem firstMomentRowsDigit1Group22 :
    forall offset : Fin 200,
      firstMomentIndexedRow (1 : Fin 5)
        ⟨4400 + offset.val, by omega⟩ := by
  have h4400_4420 := firstMomentIndexedRows_append (1 : Fin 5) 4400 10 10
    (by omega) firstMomentRowsDigit1Group22Block00 firstMomentRowsDigit1Group22Block01
  have h4420_4440 := firstMomentIndexedRows_append (1 : Fin 5) 4420 10 10
    (by omega) firstMomentRowsDigit1Group22Block02 firstMomentRowsDigit1Group22Block03
  have h4440_4460 := firstMomentIndexedRows_append (1 : Fin 5) 4440 10 10
    (by omega) firstMomentRowsDigit1Group22Block04 firstMomentRowsDigit1Group22Block05
  have h4460_4480 := firstMomentIndexedRows_append (1 : Fin 5) 4460 10 10
    (by omega) firstMomentRowsDigit1Group22Block06 firstMomentRowsDigit1Group22Block07
  have h4480_4500 := firstMomentIndexedRows_append (1 : Fin 5) 4480 10 10
    (by omega) firstMomentRowsDigit1Group22Block08 firstMomentRowsDigit1Group22Block09
  have h4500_4520 := firstMomentIndexedRows_append (1 : Fin 5) 4500 10 10
    (by omega) firstMomentRowsDigit1Group22Block10 firstMomentRowsDigit1Group22Block11
  have h4520_4540 := firstMomentIndexedRows_append (1 : Fin 5) 4520 10 10
    (by omega) firstMomentRowsDigit1Group22Block12 firstMomentRowsDigit1Group22Block13
  have h4540_4560 := firstMomentIndexedRows_append (1 : Fin 5) 4540 10 10
    (by omega) firstMomentRowsDigit1Group22Block14 firstMomentRowsDigit1Group22Block15
  have h4560_4580 := firstMomentIndexedRows_append (1 : Fin 5) 4560 10 10
    (by omega) firstMomentRowsDigit1Group22Block16 firstMomentRowsDigit1Group22Block17
  have h4580_4600 := firstMomentIndexedRows_append (1 : Fin 5) 4580 10 10
    (by omega) firstMomentRowsDigit1Group22Block18 firstMomentRowsDigit1Group22Block19
  have h4400_4440 := firstMomentIndexedRows_append (1 : Fin 5) 4400 20 20
    (by omega) h4400_4420 h4420_4440
  have h4440_4480 := firstMomentIndexedRows_append (1 : Fin 5) 4440 20 20
    (by omega) h4440_4460 h4460_4480
  have h4480_4520 := firstMomentIndexedRows_append (1 : Fin 5) 4480 20 20
    (by omega) h4480_4500 h4500_4520
  have h4520_4560 := firstMomentIndexedRows_append (1 : Fin 5) 4520 20 20
    (by omega) h4520_4540 h4540_4560
  have h4560_4600 := firstMomentIndexedRows_append (1 : Fin 5) 4560 20 20
    (by omega) h4560_4580 h4580_4600
  have h4400_4480 := firstMomentIndexedRows_append (1 : Fin 5) 4400 40 40
    (by omega) h4400_4440 h4440_4480
  have h4480_4560 := firstMomentIndexedRows_append (1 : Fin 5) 4480 40 40
    (by omega) h4480_4520 h4520_4560
  have h4400_4560 := firstMomentIndexedRows_append (1 : Fin 5) 4400 80 80
    (by omega) h4400_4480 h4480_4560
  exact firstMomentIndexedRows_append (1 : Fin 5) 4400 160 40
    (by omega) h4400_4560 h4560_4600

end PrimesRestrictedDigits
