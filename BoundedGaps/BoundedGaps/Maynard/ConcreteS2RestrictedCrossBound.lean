import BoundedGaps.Maynard.ConcreteS1CrossBound
import BoundedGaps.Maynard.ConcreteS2RestrictedReindex
import BoundedGaps.Maynard.MaynardS2RestrictedYComparison
import BoundedGaps.Maynard.MaynardS2RestrictedStarredCorrectionBound

noncomputable section

/-!
# Finite concrete bound for the restricted S2 cross correction

The supported coordinate-one transform envelope is inserted into the exact
restricted-starred correction bound. This implements the finite estimate in
Maynard2013v3, proof of Lemma `lmm:S2Expression1`, source lines 384--440.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators
set_option maxRecDepth 12000

noncomputable def engelsmaS2RestrictedTransformEnvelope
    (alpha : ℝ) (N : ℕ) (m : BoundedGaps.engelsmaTuple) : ℝ :=
  smallKCandidateBound *
    (8 * ((Nat.totient (engelsmaMaynardModulus N) : ℝ) /
      engelsmaMaynardModulus N) *
      (1 + Real.log (engelsmaMaynardRadius alpha N))) *
    (1 + ((Finset.univ.erase m).card : ℝ) *
      (8 / (tripleLogCutoff (N - 1) : ℝ) +
        (8 * Real.exp 8 / (tripleLogCutoff (N - 1) : ℝ)) *
          (1 + 8 * Real.exp 8 / (tripleLogCutoff (N - 1) : ℝ)) ^
            ((Finset.univ.erase m).card - 1)))

theorem engelsmaS2RestrictedTransformEnvelope_nonneg
    {alpha : ℝ} {N : ℕ} {m : BoundedGaps.engelsmaTuple}
    (hD : 0 < tripleLogCutoff (N - 1))
    (hWL : (engelsmaMaynardModulus N : ℝ) ≤
      1 + Real.log (engelsmaMaynardRadius alpha N)) :
    0 ≤ engelsmaS2RestrictedTransformEnvelope alpha N m := by
  have hlog : 0 ≤ 1 + Real.log (engelsmaMaynardRadius alpha N) :=
    (Nat.cast_nonneg (engelsmaMaynardModulus N)).trans hWL
  have hDreal : (0 : ℝ) < tripleLogCutoff (N - 1) := by
    exact_mod_cast hD
  have hphiW : 0 ≤
      (Nat.totient (engelsmaMaynardModulus N) : ℝ) /
        engelsmaMaynardModulus N := by
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hP : 0 ≤ 8 *
      ((Nat.totient (engelsmaMaynardModulus N) : ℝ) /
        engelsmaMaynardModulus N) *
      (1 + Real.log (engelsmaMaynardRadius alpha N)) := by
    exact mul_nonneg (mul_nonneg (by norm_num) hphiW) hlog
  have hE : 0 ≤ 1 + ((Finset.univ.erase m).card : ℝ) *
      (8 / (tripleLogCutoff (N - 1) : ℝ) +
        (8 * Real.exp 8 / (tripleLogCutoff (N - 1) : ℝ)) *
          (1 + 8 * Real.exp 8 / (tripleLogCutoff (N - 1) : ℝ)) ^
            ((Finset.univ.erase m).card - 1)) := by
    positivity
  unfold engelsmaS2RestrictedTransformEnvelope
  exact mul_nonneg (mul_nonneg smallKCandidateBound_nonneg hP) hE

theorem abs_engelsmaS2RestrictedY_le_envelope
    {alpha : ℝ} {N : ℕ} (m : BoundedGaps.engelsmaTuple)
    {r : BoundedGaps.engelsmaTuple → ℕ}
    (hD : 0 < tripleLogCutoff (N - 1))
    (hWL : (engelsmaMaynardModulus N : ℝ) ≤
      1 + Real.log (engelsmaMaynardRadius alpha N))
    (hr : IsMaynardDivisorTuple BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N) r)
    (hrm : r m = 1) :
    |maynardS2RestrictedYFromCoefficients BoundedGaps.engelsmaTuple
        (maynardDivisorTupleSupport BoundedGaps.engelsmaTuple
          (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N))
        (maynardCoefficientFromY BoundedGaps.engelsmaTuple
          (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N)
          (maynardYValue BoundedGaps.engelsmaTuple
            (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N)
            engelsmaSmallKCandidate)) m r| ≤
      engelsmaS2RestrictedTransformEnvelope alpha N m := by
  have h := abs_maynardS2RestrictedY_le_log
    (isSupportedMaynardY_maynardYValue BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N)
      engelsmaSmallKCandidate)
    m hD hWL hr hrm smallKCandidateBound_nonneg
    (abs_engelsmaMaynardYValue_le alpha N)
  simpa [engelsmaS2RestrictedTransformEnvelope, engelsmaMaynardModulus]
    using h

theorem abs_engelsmaMaynardS2RestrictedCrossCorrection_le_commonMass
    {alpha : ℝ} {N : ℕ} (m : BoundedGaps.engelsmaTuple)
    (hR : 1 < engelsmaMaynardRadius alpha N)
    (hD : 2 ≤ tripleLogCutoff (N - 1))
    (hWL : (engelsmaMaynardModulus N : ℝ) ≤
      1 + Real.log (engelsmaMaynardRadius alpha N)) :
    |engelsmaMaynardS2RestrictedCrossCorrection alpha N m| ≤
      engelsmaS2RestrictedTransformEnvelope alpha N m ^ 2 *
        roughS2CrossTupleReciprocalGSquareTail BoundedGaps.engelsmaTuple
          (tripleLogCutoff (N - 1)) (engelsmaMaynardRadius alpha N) *
        restrictedS2CommonReciprocalGMass BoundedGaps.engelsmaTuple
          (engelsmaMaynardModulus N) (engelsmaMaynardRadius alpha N) m := by
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
  unfold engelsmaMaynardS2RestrictedCrossCorrection maynardSupportFamily
    maynardCoefficientFamily
  rw [hcoeff]
  apply abs_incompatibleRestrictedS2_le_crossTail_mul_commonMass
    hR hD (engelsmaS2RestrictedTransformEnvelope_nonneg
      (Nat.zero_lt_of_lt hD) hWL)
  intro r hr hrm
  exact abs_engelsmaS2RestrictedY_le_envelope m
    (Nat.zero_lt_of_lt hD) hWL hr hrm

theorem abs_engelsmaMaynardS2RestrictedCrossCorrection_le_explicit
    {alpha : ℝ} {N : ℕ} (m : BoundedGaps.engelsmaTuple)
    (hR : 1 < engelsmaMaynardRadius alpha N)
    (hD : 2 ≤ tripleLogCutoff (N - 1))
    (hWL : (engelsmaMaynardModulus N : ℝ) ≤
      1 + Real.log (engelsmaMaynardRadius alpha N)) :
    |engelsmaMaynardS2RestrictedCrossCorrection alpha N m| ≤
      engelsmaS2RestrictedTransformEnvelope alpha N m ^ 2 *
        ((32 * Real.exp 32 / (tripleLogCutoff (N - 1) : ℝ)) *
          ((offDiagonalPairs BoundedGaps.engelsmaTuple).card : ℝ) *
          (Real.exp 32) ^
            ((offDiagonalPairs BoundedGaps.engelsmaTuple).card - 1)) *
        (maynardS2ReciprocalGSquarefreeMean
          (engelsmaMaynardModulus N) (engelsmaMaynardRadius alpha N)) ^
            (Finset.univ.erase m).card := by
  let T := roughS2CrossTupleReciprocalGSquareTail
    BoundedGaps.engelsmaTuple (tripleLogCutoff (N - 1))
      (engelsmaMaynardRadius alpha N)
  let M := maynardS2ReciprocalGSquarefreeMean
    (engelsmaMaynardModulus N) (engelsmaMaynardRadius alpha N)
  have htail0 : 0 ≤ T := by
    unfold T roughS2CrossTupleReciprocalGSquareTail
    apply Finset.sum_nonneg
    intro s hs
    unfold roughS2CrossTupleReciprocalGSquareWeight
    apply Finset.prod_nonneg
    intro x hx
    apply Finset.prod_nonneg
    intro p hp
    exact maynardS2CrossPrimeSquareWeight_nonneg p
  have hM0 : 0 ≤ M := by
    unfold M maynardS2ReciprocalGSquarefreeMean
    exact Finset.sum_nonneg fun n hn =>
      maynardS2ReciprocalGSquarefreeAF_nonneg _ n
  have hmass := restrictedS2CommonReciprocalGMass_le
    (H := BoundedGaps.engelsmaTuple)
    (W := engelsmaMaynardModulus N)
    (R := engelsmaMaynardRadius alpha N) (m := m)
  have htail := roughS2CrossTupleReciprocalGSquareTail_le
    (H := BoundedGaps.engelsmaTuple)
    (Q := engelsmaMaynardRadius alpha N) hD
  calc
    |engelsmaMaynardS2RestrictedCrossCorrection alpha N m| ≤
        engelsmaS2RestrictedTransformEnvelope alpha N m ^ 2 * T *
          restrictedS2CommonReciprocalGMass BoundedGaps.engelsmaTuple
            (engelsmaMaynardModulus N) (engelsmaMaynardRadius alpha N) m :=
      abs_engelsmaMaynardS2RestrictedCrossCorrection_le_commonMass
        m hR hD hWL
    _ ≤ engelsmaS2RestrictedTransformEnvelope alpha N m ^ 2 * T *
        M ^ (Finset.univ.erase m).card := by
      exact mul_le_mul_of_nonneg_left hmass
        (mul_nonneg (sq_nonneg _) htail0)
    _ ≤ engelsmaS2RestrictedTransformEnvelope alpha N m ^ 2 *
        ((32 * Real.exp 32 / (tripleLogCutoff (N - 1) : ℝ)) *
          ((offDiagonalPairs BoundedGaps.engelsmaTuple).card : ℝ) *
          (Real.exp 32) ^
            ((offDiagonalPairs BoundedGaps.engelsmaTuple).card - 1)) *
        M ^ (Finset.univ.erase m).card := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left htail (sq_nonneg _))
        (pow_nonneg hM0 _)
    _ = _ := by rfl

end BoundedGaps.Maynard
