import BoundedGaps.Maynard.ConcreteS2ShiftKernel
import BoundedGaps.Maynard.ImprovedGPY.S2RestrictedMainReindex

noncomputable section

/-!
# Concrete restricted S2 shift-coefficient alignment

The existing concrete shift kernel is definitionally the generic restricted
main coefficient specialized to the Engelsma support and coefficient family.
-/

namespace BoundedGaps.Maynard

theorem engelsmaMaynardS2ShiftKernel_eq_restrictedMainArithmeticCoefficient
    (alpha : ℝ) (N : ℕ) (h : BoundedGaps.engelsmaTuple) :
    engelsmaMaynardS2ShiftKernel alpha N h =
      restrictedMainArithmeticCoefficient
        BoundedGaps.engelsmaTuple
        (maynardSupportFamily BoundedGaps.engelsmaTuple
          (engelsmaMaynardRadius alpha) engelsmaMaynardModulus N)
        (engelsmaMaynardModulus N)
        (maynardCoefficientFamily BoundedGaps.engelsmaTuple
          (engelsmaMaynardRadius alpha) engelsmaMaynardModulus
          engelsmaSmallKCandidate N) h := by
  unfold engelsmaMaynardS2ShiftKernel restrictedMainArithmeticCoefficient
  dsimp

end BoundedGaps.Maynard
