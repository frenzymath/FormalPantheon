import BoundedGaps.Maynard.ConcreteS1
import BoundedGaps.Maynard.MaynardS1CrossCorrection

noncomputable section

/-!
# Concrete S1 diagonal and cross correction

This specializes the exact finite split to the frozen Engelsma family.
-/

namespace BoundedGaps.Maynard

noncomputable def engelsmaMaynardYDiagonal (alpha : ℝ) (N : ℕ) : ℝ :=
  maynardYDiagonalSum BoundedGaps.engelsmaTuple
    (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N)
    (maynardYValue BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N)
      engelsmaSmallKCandidate)

noncomputable def engelsmaMaynardS1CrossCorrection
    (alpha : ℝ) (N : ℕ) : ℝ :=
  incompatibleDivisorPairCommonDivisorTupleSum BoundedGaps.engelsmaTuple
    (maynardDivisorTupleSupport BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N))
    (maynardCoefficient BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N)
      engelsmaSmallKCandidate)

theorem engelsmaMaynardS1Main_eq_diagonal_sub_cross
    (alpha : ℝ) (N : ℕ) :
    engelsmaMaynardS1Main alpha N =
      (N : ℝ) / engelsmaMaynardModulus N *
        (engelsmaMaynardYDiagonal alpha N -
          engelsmaMaynardS1CrossCorrection alpha N) := by
  unfold engelsmaMaynardS1Main engelsmaMaynardYDiagonal
    engelsmaMaynardS1CrossCorrection maynardSupportFamily
    maynardCoefficientFamily
  rw [← compatibleDivisorPairCommonDivisorTupleMobiusSum_eq_auxiliaryMobiusSum]
  rw [← compatibleDivisorPairCommonDivisorTupleSum_eq_mobiusSum]
  rw [compatibleCommonDivisorTupleSum_eq_yValueDiagonal_sub_incompatible]

end BoundedGaps.Maynard
