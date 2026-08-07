import BoundedGaps.Maynard.ConcreteS2
import BoundedGaps.Maynard.ImprovedGPY.S2RestrictedMainReindex

noncomputable section

/-!
# Concrete restricted S2 main shift export

This is the Engelsma specialization of the finite restricted-main reindex.
The prime-count difference is exposed per shift while the exact finite
cross-coprime divisor-pair coefficient remains visible.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

theorem engelsmaMaynardS2Main_eq_shift_sum
    (alpha : ℝ) (N : ℕ) :
    engelsmaMaynardS2Main alpha N =
      ∑ m ∈ BoundedGaps.engelsmaTuple.attach,
        (((primeCountTotal (2 * N + m.1 - 1) : ℝ) -
          (primeCountTotal (N + m.1 - 1) : ℝ)) *
          restrictedMainArithmeticCoefficient
            BoundedGaps.engelsmaTuple
            (maynardSupportFamily BoundedGaps.engelsmaTuple
              (engelsmaMaynardRadius alpha) engelsmaMaynardModulus N)
            (engelsmaMaynardModulus N)
            (maynardCoefficientFamily BoundedGaps.engelsmaTuple
              (engelsmaMaynardRadius alpha) engelsmaMaynardModulus
              engelsmaSmallKCandidate N) m) := by
  unfold engelsmaMaynardS2Main
  exact compatiblePairRestrictedMainOuter_eq_shift_sum
    (engelsmaMaynardS2SupportProof alpha N)

end BoundedGaps.Maynard
