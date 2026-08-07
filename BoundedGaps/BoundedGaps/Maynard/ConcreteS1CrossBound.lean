import BoundedGaps.Maynard.ConcreteS1Diagonal
import BoundedGaps.Maynard.MaynardS1CrossCorrectionBound

noncomputable section

/-!
# The finite concrete S1 cross-correction bound

The generic logarithmic estimate is specialized to the frozen Engelsma Y
family while retaining its explicit eventual arithmetic hypotheses.
-/

namespace BoundedGaps.Maynard

theorem abs_maynardYValue_le
    (H : Finset ℕ) (R W : ℕ) (F : (H → ℝ) → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hF : ∀ t, |F t| ≤ B)
    (r : H → ℕ) :
    |maynardYValue H R W F r| ≤ B := by
  unfold maynardYValue
  split_ifs
  · exact hF _
  · simpa using hB

theorem abs_engelsmaMaynardYValue_le
    (alpha : ℝ) (N : ℕ)
    (r : BoundedGaps.engelsmaTuple → ℕ) :
    |maynardYValue BoundedGaps.engelsmaTuple
        (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N)
        engelsmaSmallKCandidate r| ≤ smallKCandidateBound := by
  exact abs_maynardYValue_le _ _ _ _ smallKCandidateBound_nonneg
    engelsmaSmallKCandidate_abs_le r

theorem abs_engelsmaMaynardS1CrossCorrection_le_log
    {alpha : ℝ} {N : ℕ}
    (hR : 0 < engelsmaMaynardRadius alpha N)
    (hD : 0 < tripleLogCutoff (N - 1))
    (hWL : (engelsmaMaynardModulus N : ℝ) ≤
      1 + Real.log (engelsmaMaynardRadius alpha N)) :
    |engelsmaMaynardS1CrossCorrection alpha N| ≤
      smallKCandidateBound ^ 2 *
        ((8 * Real.exp 8 / (tripleLogCutoff (N - 1) : ℝ)) *
          ((offDiagonalPairs BoundedGaps.engelsmaTuple).card : ℝ) *
            (Real.exp 8) ^
              ((offDiagonalPairs BoundedGaps.engelsmaTuple).card - 1)) *
        (8 * ((Nat.totient (engelsmaMaynardModulus N) : ℝ) /
          engelsmaMaynardModulus N) *
            (1 + Real.log (engelsmaMaynardRadius alpha N))) ^
          Fintype.card BoundedGaps.engelsmaTuple := by
  unfold engelsmaMaynardS1CrossCorrection
  have hcoeff : maynardCoefficient BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N)
      engelsmaSmallKCandidate =
      maynardCoefficientFromY BoundedGaps.engelsmaTuple
        (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N)
        (maynardYValue BoundedGaps.engelsmaTuple
          (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N)
          engelsmaSmallKCandidate) := by
    funext d
    exact maynardCoefficient_eq_fromYValue _ _ _ _ d
  rw [hcoeff]
  unfold engelsmaMaynardModulus at hWL ⊢
  have hy := isSupportedMaynardY_maynardYValue
    BoundedGaps.engelsmaTuple
    (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N)
    engelsmaSmallKCandidate
  have hbound := abs_incompatibleSum_le_log
    (H := BoundedGaps.engelsmaTuple)
    (R := engelsmaMaynardRadius alpha N)
    (D := tripleLogCutoff (N - 1))
    (B := smallKCandidateBound)
    hR hD smallKCandidateBound_nonneg
    hWL (abs_engelsmaMaynardYValue_le alpha N) hy
  exact hbound

end BoundedGaps.Maynard
