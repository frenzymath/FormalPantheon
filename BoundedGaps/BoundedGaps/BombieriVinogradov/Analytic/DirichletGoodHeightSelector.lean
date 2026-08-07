import BoundedGaps.BombieriVinogradov.Analytic.DirichletTwoSidedBadHeights
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Quantitative good-height selection

This file applies a finite grid argument to SEM-511's two-sided candidate
inventory. It selects a height in a closed unit interval with uniform
conductor-height clearance. Classification of ordinary L-function zeros into
the inventory is a separate successor.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 85--86 and
114--115. The arbitrary-character conductor-height scale is project-derived.
Semantic review: `SEM-512`.
-/

namespace BoundedGaps.Maynard

open Set

noncomputable section

private theorem exists_unitInterval_point_away_from_finite
    (S : Set ℝ) (hS : S.Finite) (T : ℝ) :
    ∃ T' : ℝ, T' ∈ Icc T (T + 1) ∧
      ∀ gamma ∈ S,
        1 / (2 * ((S.ncard : ℝ) + 1)) ≤ |T' - gamma| := by
  classical
  let n := S.ncard
  let delta : ℝ := 1 / ((n : ℝ) + 1)
  let radius : ℝ := delta / 2
  let grid : Fin (n + 1) → ℝ := fun i => T + (i : ℝ) * delta
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hradius :
      1 / (2 * ((S.ncard : ℝ) + 1)) = radius := by
    dsimp [radius, delta, n]
    field_simp
  have hgrid_mem (i : Fin (n + 1)) : grid i ∈ Icc T (T + 1) := by
    have hi : i.val ≤ n := Nat.lt_succ_iff.mp i.isLt
    have hiReal : (i.val : ℝ) ≤ n := by exact_mod_cast hi
    constructor
    · dsimp [grid]
      have hmul : 0 ≤ (i.val : ℝ) * delta :=
        mul_nonneg (Nat.cast_nonneg _) hdelta.le
      linarith
    · have hmul : (i.val : ℝ) * delta ≤ 1 := by
        calc
          (i.val : ℝ) * delta ≤ (n : ℝ) * delta :=
            mul_le_mul_of_nonneg_right hiReal hdelta.le
          _ ≤ ((n : ℝ) + 1) * delta := by
            gcongr
            norm_num
          _ = 1 := by
            dsimp [delta]
            field_simp
      dsimp [grid]
      linarith
  by_contra! h
  have hnear : ∀ i : Fin (n + 1), ∃ gamma : S,
      |grid i - (gamma : ℝ)| < radius := by
    intro i
    obtain ⟨gamma, hgamma, hi⟩ := h (grid i) (hgrid_mem i)
    exact ⟨⟨gamma, hgamma⟩, by simpa [hradius] using hi⟩
  let f : Fin (n + 1) → S := fun i => Classical.choose (hnear i)
  have hf_near (i : Fin (n + 1)) :
      |grid i - (f i : ℝ)| < radius :=
    Classical.choose_spec (hnear i)
  letI := hS.fintype
  have hcard : Fintype.card S < Fintype.card (Fin (n + 1)) := by
    simp only [Set.fintypeCard_eq_ncard, Fintype.card_fin]
    dsimp [n]
    omega
  obtain ⟨i, j, hij, hfij⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt f hcard
  have hsep_lt {i j : Fin (n + 1)} (hij : i < j) :
      delta ≤ |grid i - grid j| := by
    have hijNat : i.val + 1 ≤ j.val := Nat.succ_le_iff.mpr hij
    have hijReal : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by
      exact_mod_cast hijNat
    have horder : grid i ≤ grid j := by
      dsimp [grid]
      gcongr
      exact_mod_cast hij.le
    rw [abs_of_nonpos (sub_nonpos.mpr horder)]
    dsimp [grid]
    nlinarith [hdelta]
  have hsep : delta ≤ |grid i - grid j| := by
    rcases lt_or_gt_of_ne hij with hij' | hji'
    · exact hsep_lt hij'
    · simpa [abs_sub_comm] using hsep_lt hji'
  have hclose : |grid i - grid j| < radius + radius := calc
    |grid i - grid j| =
        |(grid i - (f i : ℝ)) + ((f j : ℝ) - grid j)| := by
          have hfij' : (f i : ℝ) = (f j : ℝ) :=
            congrArg Subtype.val hfij
          rw [hfij']
          congr 1
          ring
    _ ≤ |grid i - (f i : ℝ)| + |(f j : ℝ) - grid j| :=
      abs_add_le _ _
    _ < radius + radius :=
      add_lt_add (hf_near i) (by simpa [abs_sub_comm] using hf_near j)
  have htwo : radius + radius = delta := by
    dsimp [radius]
    ring
  rw [htwo] at hclose
  exact (not_lt_of_ge hsep) hclose

/-- One absolute constant selects a height clearing the complete SEM-511
two-sided candidate inventory. -/
theorem exists_nat_dirichletTwoSidedBadHeights_clearance :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ (q : ℕ) [NeZero q]
        (chi : DirichletCharacter ℂ q) (T : ℝ),
          2 ≤ T →
            ∃ T' : ℝ, T' ∈ Icc T (T + 1) ∧
              ∀ gamma ∈ dirichletTwoSidedBadHeights chi T,
                1 / ((C : ℝ) *
                    Real.log ((q : ℝ) * (T + 2))) ≤
                  |T' - gamma| := by
  obtain ⟨A, hA, hcount⟩ :=
    exists_nat_ncard_dirichletTwoSidedBadHeights_le
  refine ⟨146 * A, by omega, ?_⟩
  intro q _ chi T hT
  let S := dirichletTwoSidedBadHeights chi T
  let L := Real.log ((q : ℝ) * (T + 2))
  obtain ⟨T', hT'mem, hclear⟩ :=
    exists_unitInterval_point_away_from_finite S
      (dirichletTwoSidedBadHeights_finite chi T) T
  refine ⟨T', hT'mem, ?_⟩
  intro gamma hgamma
  change gamma ∈ S at hgamma
  change 1 / (((146 * A : ℕ) : ℝ) * L) ≤ |T' - gamma|
  have hq : (1 : ℝ) ≤ q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hscale : (4 : ℝ) ≤ (q : ℝ) * (T + 2) := by
    nlinarith [mul_le_mul hq (show (4 : ℝ) ≤ T + 2 by linarith)
      (by norm_num : (0 : ℝ) ≤ 4) (by positivity : (0 : ℝ) ≤ q)]
  have hlogFour : (1 : ℝ) < Real.log 4 := by
    rw [Real.log_four_eq]
    nlinarith [Real.log_two_gt_d9]
  have hLone : (1 : ℝ) ≤ L := by
    have hlogScale : Real.log 4 ≤ L := by
      dsimp [L]
      exact Real.log_le_log (by norm_num) hscale
    exact hlogFour.le.trans hlogScale
  have hcount' : (S.ncard : ℝ) ≤ 72 * (A : ℝ) * L := by
    simpa [S, L] using hcount q chi T hT
  have hAreal : (1 : ℝ) ≤ A := by exact_mod_cast (by omega : 1 ≤ A)
  have hAL : (1 : ℝ) ≤ (A : ℝ) * L := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hAreal) (zero_le_one.trans hLone)]
  have hden' :
      2 * ((S.ncard : ℝ) + 1) ≤ 146 * (A : ℝ) * L := by
    nlinarith
  have hden :
      2 * ((S.ncard : ℝ) + 1) ≤ (((146 * A : ℕ) : ℝ) * L) := by
    simpa using hden'
  exact (one_div_le_one_div_of_le (by positivity) hden).trans
    (hclear gamma hgamma)

end

end BoundedGaps.Maynard
