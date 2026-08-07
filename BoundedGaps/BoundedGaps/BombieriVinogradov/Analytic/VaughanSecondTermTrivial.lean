import BoundedGaps.BombieriVinogradov.Analytic.VaughanSecondTermReduction
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Vaughan's second-term level-one bound

This file formalizes the corrected level-one branch immediately before
`AkbaryHambrook2013v2`, equation (6.10). The source's intermediate strict
harmonic estimate is replaced by the valid non-strict estimate.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable section

/-- The reciprocal mass of the positive second-term divisor indices is
bounded by the harmonic estimate at the real cutoff. -/
theorem sum_inv_vaughanSecondTermIndices_le_one_add_log
    {V : ℝ} (hV : 1 ≤ V) (y : ℕ) :
    (∑ d ∈ vaughanSecondTermIndices V y, ((d : ℝ))⁻¹) ≤
      1 + Real.log V := by
  have hsubset :
      vaughanSecondTermIndices V y ⊆ Finset.Icc 1 ⌊V⌋₊ := by
    intro d hd
    rcases Finset.mem_filter.mp hd with ⟨hdy, hdV⟩
    exact Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hdy).1, Nat.le_floor hdV⟩
  calc
    (∑ d ∈ vaughanSecondTermIndices V y, ((d : ℝ))⁻¹) ≤
        ∑ d ∈ Finset.Icc 1 ⌊V⌋₊, ((d : ℝ))⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro d _hd _hnot
      positivity
    _ = ((harmonic ⌊V⌋₊ : ℚ) : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    _ ≤ 1 + Real.log V := harmonic_floor_le_one_add_log V hV

private theorem norm_dirichletCharacterIntervalSum_level_one_le_upper
    {a b : ℕ} (ha : 1 ≤ a) (chi : DirichletCharacter ℂ 1) :
    ‖dirichletCharacterIntervalSum a b 1 chi‖ ≤ (b : ℝ) := by
  rw [dirichletCharacterIntervalSum]
  calc
    ‖∑ n ∈ Finset.Icc a b, chi n‖ ≤
        ∑ n ∈ Finset.Icc a b, ‖chi n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc a b, (1 : ℝ) := by
      gcongr with n _hn
      exact chi.norm_le_one n
    _ = ((Finset.Icc a b).card : ℝ) := by simp
    _ ≤ (b : ℝ) := by
      rw [Nat.card_Icc]
      exact_mod_cast (show b + 1 - a ≤ b by omega)

/-- Corrected non-strict level-one estimate underlying the source's `q = 1`
branch before equation (6.10). -/
theorem norm_vaughanTwistedSumTwo_level_one_le_endpoint_mul_log_mul_one_add_log
    {V : ℝ} {y : ℕ} (hV : 1 ≤ V) (hy : 1 ≤ y)
    (chi : DirichletCharacter ℂ 1) :
    ‖vaughanTwistedSumTwo V y 1 chi‖ ≤
      (y : ℝ) * Real.log (y : ℝ) * (1 + Real.log V) := by
  have hlogy : 0 ≤ Real.log (y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hy)
  have hsuffix (d : ℕ) (hd : d ∈ vaughanSecondTermIndices V y) :
      dirichletCharacterSuffixMaximum y (y / d) 1 chi ≤
        (y : ℝ) * ((d : ℝ))⁻¹ := by
    have hmax :
        dirichletCharacterSuffixMaximum y (y / d) 1 chi ≤
          ((y / d : ℕ) : ℝ) := by
      rw [dirichletCharacterSuffixMaximum, dif_pos hy]
      apply Finset.sup'_le
      intro a ha
      exact norm_dirichletCharacterIntervalSum_level_one_le_upper
        (Finset.mem_Icc.mp ha).1 chi
    calc
      dirichletCharacterSuffixMaximum y (y / d) 1 chi ≤
          ((y / d : ℕ) : ℝ) := hmax
      _ ≤ (y : ℝ) / (d : ℝ) := Nat.cast_div_le
      _ = (y : ℝ) * ((d : ℝ))⁻¹ := by rw [div_eq_mul_inv]
  calc
    ‖vaughanTwistedSumTwo V y 1 chi‖ ≤
        Real.log (y : ℝ) *
          ∑ d ∈ vaughanSecondTermIndices V y,
            dirichletCharacterSuffixMaximum y (y / d) 1 chi :=
      norm_vaughanTwistedSumTwo_le_log_mul_sum_suffixMaximum hy chi
    _ ≤ Real.log (y : ℝ) *
        ∑ d ∈ vaughanSecondTermIndices V y,
          (y : ℝ) * ((d : ℝ))⁻¹ := by
      gcongr with d hd
      exact hsuffix d hd
    _ = (y : ℝ) * Real.log (y : ℝ) *
        ∑ d ∈ vaughanSecondTermIndices V y, ((d : ℝ))⁻¹ := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ (y : ℝ) * Real.log (y : ℝ) * (1 + Real.log V) := by
      gcongr
      exact sum_inv_vaughanSecondTermIndices_le_one_add_log hV y

/-- The strict final level-one estimate used in Akbary--Hambrook equation
(6.10), including the empty endpoint `y = 0`. -/
theorem norm_vaughanTwistedSumTwo_level_one_lt_endpoint_mul_log_sq
    {V : ℝ} {x y : ℕ}
    (hx : 4 ≤ x) (hV : 1 ≤ V) (hyx : y ≤ x)
    (chi : DirichletCharacter ℂ 1) :
    ‖vaughanTwistedSumTwo V y 1 chi‖ <
      (x : ℝ) * (Real.log ((x : ℝ) * V)) ^ 2 := by
  have hxpos : (0 : ℝ) < x := by
    exact_mod_cast (show 0 < x by omega)
  have hxone : (1 : ℝ) < x := by
    exact_mod_cast (show 1 < x by omega)
  have hVpos : (0 : ℝ) < V := zero_lt_one.trans_le hV
  have hlogV : 0 ≤ Real.log V := Real.log_nonneg hV
  have hlogTwo : (2 / 3 : ℝ) < Real.log 2 := by
    convert Real.lt_log_one_add_of_pos (x := (1 : ℝ)) (by norm_num) using 1 <;>
      norm_num
  have hlogFour : (4 / 3 : ℝ) < Real.log 4 := by
    calc
      (4 / 3 : ℝ) = 2 * (2 / 3) := by ring
      _ < 2 * Real.log 2 := by nlinarith
      _ = Real.log 4 := by
        rw [show (4 : ℝ) = 2 * 2 by norm_num,
          Real.log_mul (by norm_num) (by norm_num)]
        ring
  have hlogFourLe : Real.log (4 : ℝ) ≤ Real.log (x : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hx)
  have hlogx : 1 < Real.log (x : ℝ) := by linarith
  have hlogStrict :
      Real.log (x : ℝ) * (1 + Real.log V) <
        (Real.log ((x : ℝ) * V)) ^ 2 := by
    rw [Real.log_mul hxpos.ne' hVpos.ne']
    nlinarith [mul_pos (zero_lt_one.trans hlogx) (sub_pos.mpr hlogx),
      sq_nonneg (Real.log V)]
  by_cases hyzero : y = 0
  · subst y
    rw [vaughanTwistedSumTwo_eq_divisorLogSums]
    simp [vaughanSecondTermIndices]
    have hxle : (x : ℝ) ≤ (x : ℝ) * V := by nlinarith
    exact mul_pos hxpos
      (sq_pos_of_pos (Real.log_pos (hxone.trans_le hxle)))
  · have hy : 1 ≤ y := Nat.one_le_iff_ne_zero.mpr hyzero
    have hyReal : (y : ℝ) ≤ x := by exact_mod_cast hyx
    have hypos : (0 : ℝ) < y := by
      exact_mod_cast (show 0 < y by omega)
    have hlogy : 0 ≤ Real.log (y : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hy)
    have hlogyx : Real.log (y : ℝ) ≤ Real.log (x : ℝ) :=
      Real.log_le_log hypos hyReal
    have hprefix :
        (y : ℝ) * Real.log (y : ℝ) * (1 + Real.log V) ≤
          (x : ℝ) * Real.log (x : ℝ) * (1 + Real.log V) := by
      have hylog :
          (y : ℝ) * Real.log (y : ℝ) ≤
            (x : ℝ) * Real.log (x : ℝ) :=
        mul_le_mul hyReal hlogyx hlogy (le_of_lt hxpos)
      exact mul_le_mul_of_nonneg_right hylog (by linarith)
    calc
      ‖vaughanTwistedSumTwo V y 1 chi‖ ≤
          (y : ℝ) * Real.log (y : ℝ) * (1 + Real.log V) :=
        norm_vaughanTwistedSumTwo_level_one_le_endpoint_mul_log_mul_one_add_log
          hV hy chi
      _ ≤ (x : ℝ) * Real.log (x : ℝ) * (1 + Real.log V) :=
        hprefix
      _ < (x : ℝ) * (Real.log ((x : ℝ) * V)) ^ 2 := by
        simpa only [mul_assoc] using mul_lt_mul_of_pos_left hlogStrict hxpos

end

end BoundedGaps.Maynard
