import BoundedGaps.Maynard.ConcreteS2GKernel
import BoundedGaps.Maynard.MaynardS2RestrictedReindex

noncomputable section

/-!
# Concrete restricted S2 quadratic split

The frozen common-divisor kernel is the unrestricted quadratic transform
minus its explicitly retained incompatible cross-coordinate correction.
-/

namespace BoundedGaps.Maynard

noncomputable def engelsmaMaynardS2RestrictedQuadratic
    (alpha : ℝ) (N : ℕ) (h : BoundedGaps.engelsmaTuple) : ℝ :=
  maynardS2RestrictedQuadraticTransform BoundedGaps.engelsmaTuple
    (engelsmaMaynardRadius alpha N)
    (maynardSupportFamily BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha) engelsmaMaynardModulus N)
    (maynardCoefficientFamily BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha) engelsmaMaynardModulus
      engelsmaSmallKCandidate N) h

noncomputable def engelsmaMaynardS2RestrictedCrossCorrection
    (alpha : ℝ) (N : ℕ) (h : BoundedGaps.engelsmaTuple) : ℝ :=
  incompatibleDivisorPairRestrictedS2CommonDivisorTupleSum
    BoundedGaps.engelsmaTuple
    (maynardSupportFamily BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha) engelsmaMaynardModulus N)
    (maynardCoefficientFamily BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha) engelsmaMaynardModulus
      engelsmaSmallKCandidate N) h

set_option maxRecDepth 3000 in
theorem engelsmaMaynardS2RestrictedGKernel_eq_quadratic_sub_cross
    (alpha : ℝ) (N : ℕ) (h : BoundedGaps.engelsmaTuple) :
    engelsmaMaynardS2RestrictedGKernel alpha N h =
      engelsmaMaynardS2RestrictedQuadratic alpha N h -
        engelsmaMaynardS2RestrictedCrossCorrection alpha N h := by
  let D := maynardSupportFamily BoundedGaps.engelsmaTuple
    (engelsmaMaynardRadius alpha) engelsmaMaynardModulus N
  let lambda := maynardCoefficientFamily BoundedGaps.engelsmaTuple
    (engelsmaMaynardRadius alpha) engelsmaMaynardModulus
    engelsmaSmallKCandidate N
  have hD : ∀ d ∈ D,
      IsMaynardDivisorTuple BoundedGaps.engelsmaTuple
        (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N) d := by
    intro d hd
    exact maynardSupportFamily_mem_isMaynard hd
  unfold engelsmaMaynardS2RestrictedGKernel
    engelsmaMaynardS2RestrictedQuadratic
    engelsmaMaynardS2RestrictedCrossCorrection
  rw [compatibleRestrictedS2SubtypeSum_eq_membershipSum]
  rw [compatibleRestrictedS2_eq_unrestricted_sub_incompatible]
  rw [unrestrictedRestrictedS2_eq_quadraticTransform h hD]

theorem engelsmaMaynardS2Main_eq_invTotient_mul_quadratic_sub_cross_sum
    (alpha : ℝ) (N : ℕ) :
    engelsmaMaynardS2Main alpha N =
      ∑ h ∈ BoundedGaps.engelsmaTuple.attach,
        engelsmaShiftedPrimeIntervalCount N h *
          ((Nat.totient (engelsmaMaynardModulus N) : ℝ)⁻¹ *
            (engelsmaMaynardS2RestrictedQuadratic alpha N h -
              engelsmaMaynardS2RestrictedCrossCorrection alpha N h)) := by
  rw [engelsmaMaynardS2Main_eq_invTotient_mul_GKernel_sum]
  apply Finset.sum_congr rfl
  intro h hh
  rw [engelsmaMaynardS2RestrictedGKernel_eq_quadratic_sub_cross]

end BoundedGaps.Maynard
