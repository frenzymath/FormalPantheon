import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# Abel continuation for nonprincipal Dirichlet L-functions

This Mathlib-only module continues the Abel integral of a Dirichlet character
from the half-plane of absolute convergence to `0 < re s`, assuming a uniform
bound on its natural partial sums. The project-facing specializations are
reviewed in `SEM-474` and `SEM-544`.
-/

open Asymptotics Complex Filter MeasureTheory Set
open scoped BigOperators Real Topology

namespace BoundedGaps.Maynard

private noncomputable def characterPrefixTail
    {q : ℕ} (chi : DirichletCharacter ℂ q) (y : ℝ) : ℂ :=
  (Ioi (1 : ℝ)).indicator
    (fun u ↦ ∑ k ∈ Finset.Icc 1 ⌊u⌋₊, chi (k : ZMod q)) y

private lemma measurable_characterPrefixTail
    {q : ℕ} (chi : DirichletCharacter ℂ q) :
    Measurable (characterPrefixTail chi) := by
  apply Measurable.indicator _ measurableSet_Ioi
  exact
    (measurable_of_countable
      (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q))).comp
      Nat.measurable_floor

private lemma norm_characterPrefixTail_le
    {q : ℕ} (chi : DirichletCharacter ℂ q) (C : ℝ) (hC : 0 ≤ C)
    (hprefix : ∀ n : ℕ,
      ‖∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q)‖ ≤ C)
    (y : ℝ) :
    ‖characterPrefixTail chi y‖ ≤ C := by
  by_cases hy : y ∈ Ioi (1 : ℝ)
  · rw [characterPrefixTail, indicator_of_mem hy]
    exact hprefix ⌊y⌋₊
  · rw [characterPrefixTail, indicator_of_notMem hy, norm_zero]
    exact hC

private lemma locallyIntegrable_characterPrefixTail
    {q : ℕ} (chi : DirichletCharacter ℂ q) (C : ℝ) (hC : 0 ≤ C)
    (hprefix : ∀ n : ℕ,
      ‖∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q)‖ ≤ C) :
    LocallyIntegrableOn (characterPrefixTail chi) (Ioi 0) := by
  have hnormScale : ‖((C : ℝ) : ℂ)‖ = C := by
    rw [norm_real, Real.norm_eq_abs, abs_of_nonneg hC]
  refine ((locallyIntegrable_const ((C : ℝ) : ℂ)).locallyIntegrableOn
      (Ioi 0)).mono
      (measurable_characterPrefixTail chi).aestronglyMeasurable ?_
  filter_upwards with y
  rw [hnormScale]
  exact norm_characterPrefixTail_le chi C hC hprefix y

private lemma characterPrefixTail_isBigO_atTop
    {q : ℕ} (chi : DirichletCharacter ℂ q) (C : ℝ) (hC : 0 ≤ C)
    (hprefix : ∀ n : ℕ,
      ‖∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q)‖ ≤ C) :
    characterPrefixTail chi =O[atTop] (fun y : ℝ ↦ y ^ (-(0 : ℝ))) := by
  refine isBigO_iff.mpr ⟨C, Eventually.of_forall fun y ↦ ?_⟩
  simpa using norm_characterPrefixTail_le chi C hC hprefix y

private lemma characterPrefixTail_isBigO_nhdsGT_zero
    {q : ℕ} (chi : DirichletCharacter ℂ q) (b : ℝ) :
    characterPrefixTail chi =O[𝓝[>] 0] (fun y : ℝ ↦ y ^ (-b)) := by
  have hlt : ∀ᶠ y : ℝ in 𝓝[>] 0, y < 1 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
  refine isBigO_iff.mpr ⟨1, ?_⟩
  filter_upwards [hlt] with y hy
  simp [characterPrefixTail, not_lt.mpr hy.le]

private lemma differentiableAt_characterPrefixMellin_neg
    {q : ℕ} (chi : DirichletCharacter ℂ q) (C : ℝ) (hC : 0 ≤ C)
    (hprefix : ∀ n : ℕ,
      ‖∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q)‖ ≤ C)
    {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun w ↦ mellin (characterPrefixTail chi) (-w)) s := by
  have hm : DifferentiableAt ℂ (mellin (characterPrefixTail chi)) (-s) := by
    refine mellin_differentiableAt_of_isBigO_rpow
      (a := 0) (b := (-s).re - 1)
      (locallyIntegrable_characterPrefixTail chi C hC hprefix)
      (characterPrefixTail_isBigO_atTop chi C hC hprefix) ?_
      (characterPrefixTail_isBigO_nhdsGT_zero chi ((-s).re - 1)) ?_
    · simpa using (neg_lt_zero.mpr hs)
    · linarith
  exact hm.comp s differentiableAt_id.neg

private lemma characterPrefixMellin_neg_eq_integral
    {q : ℕ} (chi : DirichletCharacter ℂ q) (s : ℂ) :
    mellin (characterPrefixTail chi) (-s) =
      ∫ y in Ioi (1 : ℝ),
        (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, chi (k : ZMod q)) *
          (y : ℂ) ^ (-(s + 1)) := by
  rw [mellin]
  simp only [smul_eq_mul]
  calc
    (∫ y : ℝ in Ioi 0,
        (y : ℂ) ^ (-s - 1) * characterPrefixTail chi y) =
        ∫ y : ℝ in Ioi 0, (Ioi (1 : ℝ)).indicator
          (fun u ↦ (u : ℂ) ^ (-s - 1) *
            ∑ k ∈ Finset.Icc 1 ⌊u⌋₊, chi (k : ZMod q)) y := by
      refine setIntegral_congr_fun measurableSet_Ioi fun y _ ↦ ?_
      by_cases hy : y ∈ Ioi (1 : ℝ)
      · simp [characterPrefixTail, hy]
      · simp [characterPrefixTail, hy]
    _ = ∫ y : ℝ in Ioi 0 ∩ Ioi 1,
        (y : ℂ) ^ (-s - 1) *
          (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, chi (k : ZMod q)) := by
      rw [setIntegral_indicator measurableSet_Ioi]
    _ = ∫ y : ℝ in Ioi 1,
        (y : ℂ) ^ (-s - 1) *
          (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, chi (k : ZMod q)) := by
      rw [Ioi_inter_Ioi, max_eq_right zero_le_one]
    _ = ∫ y : ℝ in Ioi 1,
        (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, chi (k : ZMod q)) *
          (y : ℂ) ^ (-(s + 1)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun y _ ↦ ?_
      rw [show -s - 1 = -(s + 1) by ring, mul_comm]

private lemma characterPartialSums_isBigO_atTop
    {q : ℕ} (chi : DirichletCharacter ℂ q) (C : ℝ)
    (hprefix : ∀ n : ℕ,
      ‖∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q)‖ ≤ C) :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q)) =O[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (0 : ℝ)) := by
  refine isBigO_iff.mpr ⟨C, Eventually.of_forall fun n ↦ ?_⟩
  simpa using hprefix n

private lemma LFunction_eq_characterPrefixMellin_of_one_lt_re
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (C : ℝ)
    (hprefix : ∀ n : ℕ,
      ‖∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q)‖ ≤ C)
    {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction chi s =
      s * mellin (characterPrefixTail chi) (-s) := by
  calc
    DirichletCharacter.LFunction chi s = LSeries (chi ·) s :=
      DirichletCharacter.LFunction_eq_LSeries chi hs
    _ = s * ∫ y in Ioi (1 : ℝ),
        (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, chi (k : ZMod q)) *
          (y : ℂ) ^ (-(s + 1)) :=
      LSeries_eq_mul_integral (chi ·) (r := 0) le_rfl (zero_lt_one.trans hs)
        (DirichletCharacter.LSeriesSummable_of_one_lt_re chi hs)
        (characterPartialSums_isBigO_atTop chi C hprefix)
    _ = s * mellin (characterPrefixTail chi) (-s) := by
      rw [characterPrefixMellin_neg_eq_integral]

/-- A bounded natural character prefix gives the Abel integral representation
throughout the positive half-plane. The proof establishes the integral's
convergence before applying analytic uniqueness. -/
theorem LFunction_eq_abelIntegral_of_prefixBound
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (C : ℝ)
    (hprefix : ∀ n : ℕ,
      ‖∑ k ∈ Finset.Icc 1 n, chi (k : ZMod q)‖ ≤ C)
    (s : ℂ) (hs : 0 < s.re) :
    DirichletCharacter.LFunction chi s =
      s * ∫ y in Set.Ioi (1 : ℝ),
        (∑ k ∈ Finset.Icc 1 ⌊y⌋₊, chi (k : ZMod q)) *
          (y : ℂ) ^ (-(s + 1)) := by
  have hC : 0 ≤ C := by
    simpa using hprefix 0
  let U : Set ℂ := {w | 0 < w.re}
  have hUOpen : IsOpen U := isOpen_lt continuous_const continuous_re
  have hUPre : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hLeft :
      AnalyticOnNhd ℂ (DirichletCharacter.LFunction chi) U :=
    (DirichletCharacter.differentiable_LFunction hchi).differentiableOn.analyticOnNhd hUOpen
  have hRight : AnalyticOnNhd ℂ
      (fun w ↦ w * mellin (characterPrefixTail chi) (-w)) U := by
    refine DifferentiableOn.analyticOnNhd (fun w hw ↦ ?_) hUOpen
    exact (differentiableAt_id.mul
      (differentiableAt_characterPrefixMellin_neg chi C hC hprefix hw)).differentiableWithinAt
  have hEq : EqOn (DirichletCharacter.LFunction chi)
      (fun w ↦ w * mellin (characterPrefixTail chi) (-w)) U := by
    refine hLeft.eqOn_of_preconnected_of_eventuallyEq hRight hUPre
      (show (2 : ℂ) ∈ U by simp [U]) ?_
    refine eventually_of_mem
      ((isOpen_lt continuous_const continuous_re).mem_nhds
        (show 1 < (2 : ℂ).re by norm_num)) ?_
    intro w hw
    exact LFunction_eq_characterPrefixMellin_of_one_lt_re chi C hprefix hw
  rw [hEq hs]
  change s * mellin (characterPrefixTail chi) (-s) = _
  rw [characterPrefixMellin_neg_eq_integral]

end BoundedGaps.Maynard
