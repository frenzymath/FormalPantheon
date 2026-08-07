import Mathlib.Algebra.Field.Periodic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The finite Euler--Maclaurin cutoff

This file proves the exact fractional-part identity used in the smoothed
quadratic-character calculation.  The source is Koukoulopoulos, preliminary
version, Theorem 1.10 (p. 15), specialized in the proof of Theorem 12.8
(pp. 124--125).  The real cutoff is kept explicit; no totalized division at
zero is used.

Semantic review: `SEM-545`.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace BoundedGaps.Maynard

private lemma integrableOn_fract_Icc (a b : ℝ) :
    IntegrableOn (Int.fract : ℝ → ℝ) (Icc a b) := by
  apply Measure.integrableOn_of_bounded measure_Icc_lt_top.ne
  · exact measurable_fract.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg t)]
    exact (Int.fract_lt_one t).le

private lemma intervalIntegrable_fract (a b : ℝ) :
    IntervalIntegrable (Int.fract : ℝ → ℝ) volume a b := by
  have hbase : IntervalIntegrable (Int.fract : ℝ → ℝ) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)]
    exact integrableOn_fract_Icc 0 1
  exact (Int.fract_periodic ℝ).intervalIntegrable₀ one_ne_zero hbase a b

private lemma integral_fract_unit :
    (∫ t : ℝ in Set.Ioc 0 1, Int.fract t) = 1 / 2 := by
  calc
    (∫ t : ℝ in Set.Ioc 0 1, Int.fract t) =
        ∫ t : ℝ in Set.Ioc 0 1, t := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc,
        ae_restrict_of_ae (volume.ae_ne (1 : ℝ))] with t ht htne
      exact Int.fract_eq_self.mpr ⟨ht.1.le, lt_of_le_of_ne ht.2 htne⟩
    _ = 1 / 2 := by
      rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      norm_num

private lemma integral_fract_formula {u : ℝ} (hu : 0 < u) :
    (∫ t : ℝ in Set.Ioc 0 u, Int.fract t) =
      (⌊u⌋₊ : ℝ) / 2 + (u - (⌊u⌋₊ : ℝ)) ^ 2 / 2 := by
  let n : ℕ := ⌊u⌋₊
  have hbase : IntervalIntegrable (Int.fract : ℝ → ℝ) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)]
    exact integrableOn_fract_Icc 0 1
  have hall (a b : ℝ) :
      IntervalIntegrable (Int.fract : ℝ → ℝ) volume a b :=
    (Int.fract_periodic ℝ).intervalIntegrable₀ one_ne_zero hbase a b
  have hbaseValue : (∫ t : ℝ in 0..1, Int.fract t) = 1 / 2 := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact integral_fract_unit
  have hnValue : (∫ t : ℝ in 0..(n : ℝ), Int.fract t) = (n : ℝ) / 2 := by
    have hperiod := (Int.fract_periodic ℝ).intervalIntegral_add_zsmul_eq
      (n : ℤ) 0 hall
    simpa [hbaseValue, nsmul_eq_mul, div_eq_mul_inv] using hperiod
  have hn_le : (n : ℝ) ≤ u := by
    dsimp [n]
    exact Nat.floor_le hu.le
  have hu_lt : u < (n : ℝ) + 1 := by
    dsimp [n]
    exact Nat.lt_floor_add_one u
  have hrem : (∫ t : ℝ in (n : ℝ)..u, Int.fract t) =
      (u - (n : ℝ)) ^ 2 / 2 := by
    calc
      (∫ t : ℝ in (n : ℝ)..u, Int.fract t) =
          ∫ t : ℝ in (n : ℝ)..u, (t - (n : ℝ)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t ∈ Set.uIcc (n : ℝ) u := ht
        rw [Set.uIcc_of_le hn_le] at ht'
        rw [← Int.fract_sub_natCast t n]
        exact Int.fract_eq_self.mpr ⟨sub_nonneg.mpr ht'.1,
          (sub_lt_iff_lt_add).mpr
            (ht'.2.trans_lt (by simpa [add_comm] using hu_lt))⟩
      _ = (u - (n : ℝ)) ^ 2 / 2 := by
        rw [intervalIntegral.integral_sub]
        · rw [integral_id, intervalIntegral.integral_const]
          simp only [smul_eq_mul]
          ring
        · exact continuous_id.intervalIntegrable (μ := volume) _ _
        · exact continuous_const.intervalIntegrable (μ := volume) _ _
  rw [← intervalIntegral.integral_of_le hu.le]
  change (∫ t : ℝ in 0..u, Int.fract t) =
    (n : ℝ) / 2 + (u - (n : ℝ)) ^ 2 / 2
  rw [← intervalIntegral.integral_add_adjacent_intervals (hall 0 n) (hall n u),
    hnValue, hrem]

/-- Natural division is the real-floor cutoff at a positive denominator. -/
theorem nat_le_div_iff_cast_le_div
    {X a b : ℕ} (ha : 0 < a) :
    b ≤ X / a ↔ (b : ℝ) ≤ (X : ℝ) / (a : ℝ) := by
  rw [Nat.le_div_iff_mul_le ha]
  rw [le_div_iff₀ (by exact_mod_cast ha)]
  exact_mod_cast Iff.rfl

/-- The exact linear Euler--Maclaurin formula for a positive real cutoff. -/
theorem sum_linear_cutoff_eq_half_sub_fractIntegral
    {u : ℝ} (hu : 0 < u) :
    (∑ b ∈ Finset.Icc 1 ⌊u⌋₊,
      (1 - (b : ℝ) / u)) =
      u / 2 - (1 / u) *
        (∫ t : ℝ in Set.Ioc 0 u, Int.fract t) := by
  rw [integral_fract_formula hu]
  rw [Finset.sum_sub_distrib, Finset.sum_const]
  have hsum_id : ∀ n : ℕ,
      (∑ b ∈ Finset.Icc 1 n, (b : ℝ)) =
        (n : ℝ) * ((n : ℝ) + 1) / 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_Icc_succ_top (by omega), ih]
        push_cast
        ring
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, hsum_id]
  simp only [Nat.card_Icc]
  push_cast
  field_simp [hu.ne']
  ring

end BoundedGaps.Maynard
