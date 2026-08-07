import BoundedGaps.Maynard.ConcreteS2TotientKernel
import BoundedGaps.Maynard.MaynardS2GDivisorExpansion

noncomputable section

/-!
# Concrete common-divisor S2 kernel

This composes the exact pre-sieving totient factor with Maynard's finite
`g(p)=p-2` common-divisor expansion for the frozen Engelsma family.
-/

namespace BoundedGaps.Maynard

noncomputable def engelsmaMaynardS2RestrictedGKernel
    (alpha : ℝ) (N : ℕ) (h : BoundedGaps.engelsmaTuple) : ℝ :=
  compatibleDivisorPairRestrictedS2CommonDivisorTupleSum
    BoundedGaps.engelsmaTuple
    (maynardSupportFamily BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha) engelsmaMaynardModulus N)
    (maynardCoefficientFamily BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha) engelsmaMaynardModulus
      engelsmaSmallKCandidate N) h

set_option maxRecDepth 3000 in
theorem engelsmaMaynardS2ShiftKernel_eq_invTotient_mul_GKernel
    (alpha : ℝ) (N : ℕ) (h : BoundedGaps.engelsmaTuple) :
    engelsmaMaynardS2ShiftKernel alpha N h =
      (Nat.totient (engelsmaMaynardModulus N) : ℝ)⁻¹ *
        engelsmaMaynardS2RestrictedGKernel alpha N h := by
  rw [engelsmaMaynardS2ShiftKernel_eq_invTotient_mul]
  congr 1
  unfold engelsmaMaynardS2RestrictedTotientKernel
    engelsmaMaynardS2RestrictedGKernel
  apply compatibleDivisorPairRestrictedTotientKernel_eq_commonDivisorS2TupleSum
  intro d hd
  exact maynardSupportFamily_mem_isMaynard hd

theorem engelsmaMaynardS2Main_eq_invTotient_mul_GKernel_sum
    (alpha : ℝ) (N : ℕ) :
    engelsmaMaynardS2Main alpha N =
      ∑ h ∈ BoundedGaps.engelsmaTuple.attach,
        engelsmaShiftedPrimeIntervalCount N h *
          ((Nat.totient (engelsmaMaynardModulus N) : ℝ)⁻¹ *
            engelsmaMaynardS2RestrictedGKernel alpha N h) := by
  rw [engelsmaMaynardS2Main_eq_shiftKernel_sum]
  apply Finset.sum_congr rfl
  intro h hh
  rw [engelsmaMaynardS2ShiftKernel_eq_invTotient_mul_GKernel]

end BoundedGaps.Maynard
