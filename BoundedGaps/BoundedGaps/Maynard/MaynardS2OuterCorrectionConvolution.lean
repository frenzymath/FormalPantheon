import BoundedGaps.Maynard.MaynardS2OuterCorrectionEndpoint

noncomputable section

/-! Exact finite convolution identity for the S2 outer squarefree mean. -/

namespace BoundedGaps.Maynard

open Finset Nat ArithmeticFunction
open scoped BigOperators

noncomputable def maynardS2OuterSquarefreeMean (W Q : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 Q, maynardS2OuterSquarefreeAF W n

theorem maynardS2OuterCorrectionAF_mul_coprimeHarmonicAF (W : ℕ) :
    maynardS2OuterCorrectionAF W * coprimeHarmonicAF W =
      maynardS2OuterSquarefreeAF W := by
  unfold maynardS2OuterCorrectionAF
  rw [mul_assoc, coprimeMobiusInvAF_mul_coprimeHarmonicAF, mul_one]

theorem maynardS2OuterSquarefreeMean_eq_correction_coprimeHarmonic
    (W Q : ℕ) :
    maynardS2OuterSquarefreeMean W Q =
      ∑ d ∈ Finset.Ioc 0 Q,
        maynardS2OuterCorrectionAF W d * coprimeHarmonicSum W (Q / d) := by
  have htarget : maynardS2OuterSquarefreeMean W Q =
      ∑ n ∈ Finset.Ioc 0 Q, maynardS2OuterSquarefreeAF W n := by
    unfold maynardS2OuterSquarefreeMean
    have hinterval : Finset.Icc 1 Q = Finset.Ioc 0 Q := by
      ext n
      simp
      omega
    rw [hinterval]
  rw [htarget, ← maynardS2OuterCorrectionAF_mul_coprimeHarmonicAF]
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
