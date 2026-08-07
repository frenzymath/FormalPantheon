import BoundedGaps.Maynard.ConcreteS2RestrictedReindex
import BoundedGaps.Maynard.MaynardS2RestrictedYDiagonal

noncomputable section

/-!
# Concrete restricted S2 Y-diagonal

This specializes the exact restricted transform normalization to the frozen
Engelsma coefficient and support families.
-/

namespace BoundedGaps.Maynard

noncomputable def engelsmaMaynardS2RestrictedYDiagonal
    (alpha : ℝ) (N : ℕ) (h : BoundedGaps.engelsmaTuple) : ℝ :=
  maynardS2RestrictedYDiagonalSum BoundedGaps.engelsmaTuple
    (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N)
    (maynardCoefficientFamily BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha) engelsmaMaynardModulus
      engelsmaSmallKCandidate N) h

set_option maxRecDepth 3000 in
theorem engelsmaMaynardS2RestrictedQuadratic_eq_yDiagonal
    (alpha : ℝ) (N : ℕ) (h : BoundedGaps.engelsmaTuple) :
    engelsmaMaynardS2RestrictedQuadratic alpha N h =
      engelsmaMaynardS2RestrictedYDiagonal alpha N h := by
  unfold engelsmaMaynardS2RestrictedQuadratic
    engelsmaMaynardS2RestrictedYDiagonal maynardSupportFamily
  exact maynardS2RestrictedQuadraticTransform_eq_yDiagonal h

theorem engelsmaMaynardS2Main_eq_invTotient_mul_yDiagonal_sub_cross_sum
    (alpha : ℝ) (N : ℕ) :
    engelsmaMaynardS2Main alpha N =
      ∑ h ∈ BoundedGaps.engelsmaTuple.attach,
        engelsmaShiftedPrimeIntervalCount N h *
          ((Nat.totient (engelsmaMaynardModulus N) : ℝ)⁻¹ *
            (engelsmaMaynardS2RestrictedYDiagonal alpha N h -
              engelsmaMaynardS2RestrictedCrossCorrection alpha N h)) := by
  rw [engelsmaMaynardS2Main_eq_invTotient_mul_quadratic_sub_cross_sum]
  apply Finset.sum_congr rfl
  intro h hh
  rw [engelsmaMaynardS2RestrictedQuadratic_eq_yDiagonal]

end BoundedGaps.Maynard
