import BoundedGaps.Maynard.ConcreteS2ShiftKernel
import BoundedGaps.Maynard.MaynardS2TotientFactorization

noncomputable section

/-!
# Concrete coordinatewise-totient S2 kernel

This specializes the exact CRT-modulus totient factorization to the frozen
Engelsma family. No asymptotic estimate is used here.
-/

namespace BoundedGaps.Maynard

noncomputable def engelsmaMaynardS2RestrictedTotientKernel
    (alpha : ℝ) (N : ℕ) (h : BoundedGaps.engelsmaTuple) : ℝ :=
  compatibleDivisorPairRestrictedTotientKernel BoundedGaps.engelsmaTuple
    (maynardSupportFamily BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha) engelsmaMaynardModulus N)
    (maynardCoefficientFamily BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha) engelsmaMaynardModulus
      engelsmaSmallKCandidate N) h

set_option maxRecDepth 3000 in
theorem engelsmaMaynardS2ShiftKernel_eq_invTotient_mul
    (alpha : ℝ) (N : ℕ) (h : BoundedGaps.engelsmaTuple) :
    engelsmaMaynardS2ShiftKernel alpha N h =
      (Nat.totient (engelsmaMaynardModulus N) : ℝ)⁻¹ *
        engelsmaMaynardS2RestrictedTotientKernel alpha N h := by
  classical
  unfold engelsmaMaynardS2ShiftKernel
    engelsmaMaynardS2RestrictedTotientKernel
  apply restrictedDivisorPairModulusTotientSum_eq_invTotient_mul
  intro d hd
  exact maynardSupportFamily_mem_isMaynard hd

end BoundedGaps.Maynard
