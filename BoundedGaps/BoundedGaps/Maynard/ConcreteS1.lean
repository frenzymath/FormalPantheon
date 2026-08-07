import BoundedGaps.Maynard.EngelsmaCandidate
import BoundedGaps.Maynard.ImprovedGPY.Mobius
import BoundedGaps.Maynard.MaynardSupportBounds

/-!
# Concrete S1 decomposition

This module instantiates the finite auxiliary-Möbius `S1` identity from
Maynard2013v3, Section 5 (`lmm:S1Expression1`, source lines 273--320), with
the frozen Engelsma candidate and parameter families.
-/

namespace BoundedGaps.Maynard

open Filter Set

noncomputable def engelsmaMaynardS1Main (alpha : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) / engelsmaMaynardModulus N *
    compatibleDivisorPairCommonDivisorTupleAuxiliaryMobiusSum
      BoundedGaps.engelsmaTuple
      (maynardSupportFamily BoundedGaps.engelsmaTuple
        (engelsmaMaynardRadius alpha) engelsmaMaynardModulus N)
      (maynardCoefficientFamily BoundedGaps.engelsmaTuple
        (engelsmaMaynardRadius alpha) engelsmaMaynardModulus
        engelsmaSmallKCandidate N)

noncomputable def engelsmaMaynardS1Error (alpha : ℝ) (N : ℕ) : ℝ :=
  compatibleDivisorPairErrorSum BoundedGaps.engelsmaTuple
    (maynardSupportFamily BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha) engelsmaMaynardModulus N)
    (engelsmaPreSieveResidue N) (engelsmaMaynardModulus N) N
    (maynardCoefficientFamily BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha) engelsmaMaynardModulus
      engelsmaSmallKCandidate N)

set_option maxRecDepth 2000 in
theorem eventually_engelsmaMaynardS1_eq_main_add_error (alpha : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      sieveWeightSum N
          (maynardPreSievedWeightFamily BoundedGaps.engelsmaTuple
            (engelsmaMaynardRadius alpha) engelsmaMaynardModulus
            engelsmaPreSieveResidue engelsmaSmallKCandidate N) =
        engelsmaMaynardS1Main alpha N + engelsmaMaynardS1Error alpha N := by
  classical
  filter_upwards [eventually_engelsmaMaynard_coverage] with N hcoverage
  have hD : ∀ d ∈ maynardSupportFamily BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha) engelsmaMaynardModulus N,
      IsMaynardDivisorTuple BoundedGaps.engelsmaTuple
        (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N) d := by
    intro d hd
    change d ∈ maynardDivisorTupleSupport BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N) at hd
    unfold maynardDivisorTupleSupport at hd
    exact (Finset.mem_filter.mp hd).2
  unfold engelsmaMaynardS1Main engelsmaMaynardS1Error
  change sieveWeightSum N
      (preSievedSquareDivisorWeight BoundedGaps.engelsmaTuple
        (maynardSupportFamily BoundedGaps.engelsmaTuple
          (engelsmaMaynardRadius alpha) engelsmaMaynardModulus N)
        (maynardCoefficientFamily BoundedGaps.engelsmaTuple
          (engelsmaMaynardRadius alpha) engelsmaMaynardModulus
          engelsmaSmallKCandidate N)
        (engelsmaPreSieveResidue N) (engelsmaMaynardModulus N)) = _
  exact sieveWeightSum_preSieved_eq_auxiliaryMobiusSum_add_error
    (lambda := maynardCoefficientFamily BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha) engelsmaMaynardModulus
      engelsmaSmallKCandidate N)
    (v := engelsmaPreSieveResidue N) (N := N) hD hcoverage

theorem tendsto_engelsmaMaynardS1_of_main_error
    {alpha I : ℝ} (halpha : 0 < alpha)
    (hmain : Tendsto
      (fun N : ℕ => engelsmaMaynardS1Main alpha N /
        engelsmaMaynardScale alpha N)
      atTop (nhds I))
    (herror : Tendsto
      (fun N : ℕ => engelsmaMaynardS1Error alpha N /
        engelsmaMaynardScale alpha N)
      atTop (nhds 0)) :
    Tendsto
      (fun N : ℕ => sieveWeightSum N
        (maynardPreSievedWeightFamily BoundedGaps.engelsmaTuple
          (engelsmaMaynardRadius alpha) engelsmaMaynardModulus
          engelsmaPreSieveResidue engelsmaSmallKCandidate N) /
            engelsmaMaynardScale alpha N)
      atTop (nhds I) := by
  have hdiff : Tendsto
      (fun N : ℕ =>
        (sieveWeightSum N
          (maynardPreSievedWeightFamily BoundedGaps.engelsmaTuple
            (engelsmaMaynardRadius alpha) engelsmaMaynardModulus
            engelsmaPreSieveResidue engelsmaSmallKCandidate N) -
          engelsmaMaynardS1Main alpha N) /
            engelsmaMaynardScale alpha N)
      atTop (nhds 0) := by
    apply herror.congr'
    filter_upwards [eventually_engelsmaMaynardS1_eq_main_add_error alpha] with N hN
    rw [hN]
    ring
  apply tendsto_normalized_sum_of_error
    (main := engelsmaMaynardS1Main alpha)
    (scale := engelsmaMaynardScale alpha)
  · exact (eventually_engelsmaMaynardScale_pos halpha).mono
      (fun _ h => ne_of_gt h)
  · exact hmain
  · exact hdiff

set_option maxRecDepth 2000 in
theorem abs_engelsmaMaynardS1Error_le_card_sq_mul
    {alpha : ℝ} (N : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (hbound : ∀ d ∈ maynardSupportFamily BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha) engelsmaMaynardModulus N,
      |maynardCoefficientFamily BoundedGaps.engelsmaTuple
        (engelsmaMaynardRadius alpha) engelsmaMaynardModulus
        engelsmaSmallKCandidate N d| ≤ L) :
    |engelsmaMaynardS1Error alpha N| ≤
      (maynardSupportFamily BoundedGaps.engelsmaTuple
        (engelsmaMaynardRadius alpha) engelsmaMaynardModulus N).card ^ 2 * L ^ 2 := by
  classical
  let D := maynardSupportFamily BoundedGaps.engelsmaTuple
    (engelsmaMaynardRadius alpha) engelsmaMaynardModulus N
  let lambda := maynardCoefficientFamily BoundedGaps.engelsmaTuple
    (engelsmaMaynardRadius alpha) engelsmaMaynardModulus
    engelsmaSmallKCandidate N
  have hD : ∀ d ∈ D,
      IsMaynardDivisorTuple BoundedGaps.engelsmaTuple
        (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N) d := by
    intro d hd
    unfold D at hd
    unfold maynardSupportFamily at hd
    unfold maynardDivisorTupleSupport at hd
    exact (Finset.mem_filter.mp hd).2
  have hW : 0 < engelsmaMaynardModulus N := by
    exact primorial_pos _
  have hmass := compatibleDivisorPairCoefficientMass_le_card_sq_mul
    (D := D) (lambda := lambda) hL (by
      intro d hd
      exact hbound d hd)
  have herr := abs_compatibleDivisorPairErrorSum_le_coefficientMass
    (D := D) (lambda := lambda) (R := engelsmaMaynardRadius alpha N)
    hW hD (v := engelsmaPreSieveResidue N) (N := N)
  change |compatibleDivisorPairErrorSum BoundedGaps.engelsmaTuple D
      (engelsmaPreSieveResidue N) (engelsmaMaynardModulus N) N lambda| ≤ _
  simpa [D, lambda] using herr.trans hmass

set_option maxRecDepth 2000 in
theorem abs_engelsmaMaynardS1Error_le_log_envelope
    {alpha : ℝ} (N : ℕ) :
    |engelsmaMaynardS1Error alpha N| ≤
      (maynardSupportFamily BoundedGaps.engelsmaTuple
        (engelsmaMaynardRadius alpha) engelsmaMaynardModulus N).card ^ 2 *
        ((engelsmaMaynardRadius alpha N : ℝ) * smallKCandidateBound *
          (1 + Real.log (engelsmaMaynardRadius alpha N)) ^
            (2 * Fintype.card BoundedGaps.engelsmaTuple)) ^ 2 := by
  let L : ℝ := (engelsmaMaynardRadius alpha N : ℝ) * smallKCandidateBound *
    (1 + Real.log (engelsmaMaynardRadius alpha N)) ^
      (2 * Fintype.card BoundedGaps.engelsmaTuple)
  have hL : 0 ≤ L := by
    dsimp [L]
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) smallKCandidateBound_nonneg)
      (by positivity)
  have hbound : ∀ d ∈ maynardSupportFamily BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha) engelsmaMaynardModulus N,
      |maynardCoefficientFamily BoundedGaps.engelsmaTuple
        (engelsmaMaynardRadius alpha) engelsmaMaynardModulus
        engelsmaSmallKCandidate N d| ≤ L := by
    intro d hd
    exact abs_engelsmaMaynardCoefficient_le_log_envelope (alpha := alpha) N hd
  simpa [L] using
    abs_engelsmaMaynardS1Error_le_card_sq_mul N L hL hbound

theorem engelsmaMaynardSupport_card_le_log
    {alpha : ℝ} (N : ℕ) :
    ((maynardSupportFamily BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha) engelsmaMaynardModulus N).card : ℝ) ≤
      (engelsmaMaynardRadius alpha N : ℝ) *
        (1 + Real.log (engelsmaMaynardRadius alpha N)) ^
          Fintype.card BoundedGaps.engelsmaTuple := by
  simpa only [maynardSupportFamily] using
    (maynardDivisorTupleSupport_card_le_log BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N))

set_option maxRecDepth 2000 in
theorem abs_engelsmaMaynardS1Error_le_explicit_log_envelope
    {alpha : ℝ} (N : ℕ) :
    |engelsmaMaynardS1Error alpha N| ≤
      ((engelsmaMaynardRadius alpha N : ℝ) *
        (1 + Real.log (engelsmaMaynardRadius alpha N)) ^
          Fintype.card BoundedGaps.engelsmaTuple) ^ 2 *
        ((engelsmaMaynardRadius alpha N : ℝ) * smallKCandidateBound *
          (1 + Real.log (engelsmaMaynardRadius alpha N)) ^
            (2 * Fintype.card BoundedGaps.engelsmaTuple)) ^ 2 := by
  have hcard := engelsmaMaynardSupport_card_le_log (alpha := alpha) N
  have hcardpow :
      ((maynardSupportFamily BoundedGaps.engelsmaTuple
        (engelsmaMaynardRadius alpha) engelsmaMaynardModulus N).card : ℝ) ^ 2 ≤
        ((engelsmaMaynardRadius alpha N : ℝ) *
          (1 + Real.log (engelsmaMaynardRadius alpha N)) ^
            Fintype.card BoundedGaps.engelsmaTuple) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2
  exact (abs_engelsmaMaynardS1Error_le_log_envelope N).trans
    (mul_le_mul_of_nonneg_right hcardpow (sq_nonneg _))

theorem tendsto_engelsmaMaynardS1Error_zero_of_envelope
    {alpha : ℝ} (halpha : 0 < alpha) (L : ℕ → ℝ)
    (hL : ∀ N, 0 ≤ L N)
    (hbound : ∀ N d,
      d ∈ maynardSupportFamily BoundedGaps.engelsmaTuple
        (engelsmaMaynardRadius alpha) engelsmaMaynardModulus N →
      |maynardCoefficientFamily BoundedGaps.engelsmaTuple
        (engelsmaMaynardRadius alpha) engelsmaMaynardModulus
        engelsmaSmallKCandidate N d| ≤ L N)
    (henvelope : Tendsto
      (fun N : ℕ =>
        ((maynardSupportFamily BoundedGaps.engelsmaTuple
          (engelsmaMaynardRadius alpha) engelsmaMaynardModulus N).card : ℝ) ^ 2 *
            (L N) ^ 2 / engelsmaMaynardScale alpha N)
      atTop (nhds 0)) :
    Tendsto
      (fun N : ℕ => engelsmaMaynardS1Error alpha N /
        engelsmaMaynardScale alpha N)
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_ henvelope
  filter_upwards [eventually_engelsmaMaynardScale_pos halpha] with N hscale
  rw [abs_div, abs_of_pos hscale]
  apply div_le_div_of_nonneg_right
  · exact abs_engelsmaMaynardS1Error_le_card_sq_mul
      N (L N) (hL N) (hbound N)
  · exact hscale.le

set_option maxRecDepth 2000 in
theorem tendsto_engelsmaMaynardS1Error_zero_of_log_envelope
    {alpha : ℝ} (halpha : 0 < alpha)
    (henvelope : Tendsto
      (fun N : ℕ =>
        ((maynardSupportFamily BoundedGaps.engelsmaTuple
          (engelsmaMaynardRadius alpha) engelsmaMaynardModulus N).card : ℝ) ^ 2 *
          ((engelsmaMaynardRadius alpha N : ℝ) * smallKCandidateBound *
            (1 + Real.log (engelsmaMaynardRadius alpha N)) ^
              (2 * Fintype.card BoundedGaps.engelsmaTuple)) ^ 2 /
            engelsmaMaynardScale alpha N)
      atTop (nhds 0)) :
    Tendsto
      (fun N : ℕ => engelsmaMaynardS1Error alpha N /
        engelsmaMaynardScale alpha N)
      atTop (nhds 0) := by
  let L : ℕ → ℝ := fun N =>
    (engelsmaMaynardRadius alpha N : ℝ) * smallKCandidateBound *
      (1 + Real.log (engelsmaMaynardRadius alpha N)) ^
        (2 * Fintype.card BoundedGaps.engelsmaTuple)
  apply tendsto_engelsmaMaynardS1Error_zero_of_envelope halpha L
  · intro N
    dsimp [L]
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) smallKCandidateBound_nonneg)
      (by positivity)
  · intro N d hd
    exact abs_engelsmaMaynardCoefficient_le_log_envelope (alpha := alpha) N hd
  · simpa [L] using henvelope

set_option maxRecDepth 2000 in
theorem tendsto_engelsmaMaynardS1Error_zero_of_explicit_log_envelope
    {alpha : ℝ} (halpha : 0 < alpha)
    (henvelope : Tendsto
      (fun N : ℕ =>
        ((engelsmaMaynardRadius alpha N : ℝ) *
          (1 + Real.log (engelsmaMaynardRadius alpha N)) ^
            Fintype.card BoundedGaps.engelsmaTuple) ^ 2 *
          ((engelsmaMaynardRadius alpha N : ℝ) * smallKCandidateBound *
            (1 + Real.log (engelsmaMaynardRadius alpha N)) ^
              (2 * Fintype.card BoundedGaps.engelsmaTuple)) ^ 2 /
            engelsmaMaynardScale alpha N)
      atTop (nhds 0)) :
    Tendsto
      (fun N : ℕ => engelsmaMaynardS1Error alpha N /
        engelsmaMaynardScale alpha N)
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_ henvelope
  filter_upwards [eventually_engelsmaMaynardScale_pos halpha] with N hscale
  rw [abs_div, abs_of_pos hscale]
  apply div_le_div_of_nonneg_right
  · exact abs_engelsmaMaynardS1Error_le_explicit_log_envelope N
  · exact hscale.le

end BoundedGaps.Maynard
