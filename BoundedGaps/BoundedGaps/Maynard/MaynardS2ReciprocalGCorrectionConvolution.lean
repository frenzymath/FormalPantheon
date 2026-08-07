import BoundedGaps.Maynard.MaynardS2ReciprocalGCorrectionEndpoint

noncomputable section

/-! Exact finite convolution identity for the reciprocal-g squarefree mean. -/

namespace BoundedGaps.Maynard

open Finset Nat ArithmeticFunction
open scoped BigOperators

noncomputable def maynardS2ReciprocalGSquarefreeMean (W Q : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 Q, maynardS2ReciprocalGSquarefreeAF W n

theorem maynardS2ReciprocalGCorrectionAF_mul_coprimeHarmonicAF (W : ℕ) :
    maynardS2ReciprocalGCorrectionAF W * coprimeHarmonicAF W =
      maynardS2ReciprocalGSquarefreeAF W := by
  unfold maynardS2ReciprocalGCorrectionAF
  rw [mul_assoc, coprimeMobiusInvAF_mul_coprimeHarmonicAF, mul_one]

theorem maynardS2ReciprocalGSquarefreeMean_eq_correction_coprimeHarmonic
    (W Q : ℕ) :
    maynardS2ReciprocalGSquarefreeMean W Q =
      ∑ d ∈ Finset.Ioc 0 Q,
        maynardS2ReciprocalGCorrectionAF W d *
          coprimeHarmonicSum W (Q / d) := by
  have htarget : maynardS2ReciprocalGSquarefreeMean W Q =
      ∑ n ∈ Finset.Ioc 0 Q,
        maynardS2ReciprocalGSquarefreeAF W n := by
    unfold maynardS2ReciprocalGSquarefreeMean
    have hinterval : Finset.Icc 1 Q = Finset.Ioc 0 Q := by
      ext n
      simp
      omega
    rw [hinterval]
  rw [htarget, ← maynardS2ReciprocalGCorrectionAF_mul_coprimeHarmonicAF]
  rw [ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  rw [show Finset.Ioc 0 (Q / d) = Finset.Icc 1 (Q / d) by
    ext n
    simp
    omega]
  unfold coprimeHarmonicSum
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  rw [coprimeHarmonicAF_apply]
  have hnNe : n ≠ 0 :=
    (zero_lt_one.trans_le (Finset.mem_Icc.mp hn).1).ne'
  rw [if_neg hnNe]

end BoundedGaps.Maynard
