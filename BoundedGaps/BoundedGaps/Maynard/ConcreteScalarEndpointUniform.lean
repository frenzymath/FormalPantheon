import BoundedGaps.Maynard.ConcreteScalarEndpointGrid
import BoundedGaps.Maynard.ConcreteScalarMonotonicity

noncomputable section

namespace BoundedGaps.Maynard

open Filter Set

theorem eventually_engelsmaSquarefreeMean_mono_exponent_uniform :
    ∀ᶠ N : ℕ in atTop, ∀ a b : ℝ, a ≤ b →
      squarefreeCoprimeInvTotientMean
          (engelsmaMaynardModulus N) (engelsmaMaynardRadius a N) ≤
        squarefreeCoprimeInvTotientMean
          (engelsmaMaynardModulus N) (engelsmaMaynardRadius b N) := by
  filter_upwards [eventually_ge_atTop 2] with N hN
  intro a b hab
  apply squarefreeCoprimeInvTotientMean_mono_cutoff
  unfold engelsmaMaynardRadius maynardDivisorCutoff
  apply Nat.floor_mono
  exact Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (show 1 ≤ N - 1 by omega)) hab

set_option maxRecDepth 10000 in
theorem eventually_engelsmaSquarefreeMean_fractionalRadius_uniform_Icc
    {alpha : ℝ} (halpha : 0 < alpha) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ beta ∈ Set.Icc (0 : ℝ) 1,
      |squarefreeCoprimeInvTotientMean
          (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius (alpha * beta) N) /
        (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
          Real.log (engelsmaMaynardRadius alpha N)) - beta| < epsilon := by
  obtain ⟨m, hm⟩ := exists_nat_gt (3 / epsilon)
  have hmreal : (3 / epsilon : ℝ) < (m : ℝ) := by
    exact_mod_cast hm
  have hmpos : 0 < m := by
    have hmrealpos : (0 : ℝ) < (m : ℝ) := by
      exact (div_pos (show (0 : ℝ) < 3 by norm_num) hepsilon).trans hmreal
    exact_mod_cast hmrealpos
  have hmesh : (1 : ℝ) / m < epsilon / 3 := by
    have hscaled := mul_lt_mul_of_pos_right hmreal
      (div_pos hepsilon (by norm_num : (0 : ℝ) < 3))
    have hmul : (1 : ℝ) < (m : ℝ) * (epsilon / 3) := by
      have hleft : (3 / epsilon : ℝ) * (epsilon / 3) = 1 := by
        field_simp
      rw [hleft] at hscaled
      exact hscaled
    apply (div_lt_iff₀ (by exact_mod_cast hmpos)).2
    nlinarith [hmul]
  let B : Finset ℝ :=
    (Finset.range (m + 1)).image (fun j : ℕ => (j : ℝ) / m)
  have hB : ∀ beta ∈ B, 0 ≤ beta := by
    intro beta hbeta
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hbeta
    positivity
  have hgrid := eventually_engelsmaSquarefreeMean_fractionalRadius_finset
    halpha B hB (div_pos hepsilon (by norm_num : (0 : ℝ) < 3))
  have hmono := eventually_engelsmaSquarefreeMean_mono_exponent_uniform
  have hL := tendsto_log_engelsmaMaynardRadius_atTop halpha
  filter_upwards [hgrid, hmono, hL.eventually (eventually_gt_atTop 0)] with
      N hgridN hmonoN hLN
  let F : ℝ → ℝ := fun beta =>
    squarefreeCoprimeInvTotientMean
        (engelsmaMaynardModulus N)
        (engelsmaMaynardRadius (alpha * beta) N) /
      (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
        Real.log (engelsmaMaynardRadius alpha N))
  intro beta hbeta
  change |F beta - beta| < epsilon
  have hSpos : 0 < preSieveSingularSeries (tripleLogCutoff (N - 1)) :=
    preSieveSingularSeries_pos _
  have hdenpos : 0 <
      preSieveSingularSeries (tripleLogCutoff (N - 1)) *
        Real.log (engelsmaMaynardRadius alpha N) := by
    exact mul_pos hSpos hLN
  have hgrid' : ∀ gamma ∈ B, |F gamma - gamma| < epsilon / 3 := by
    intro gamma hgamma
    simpa [F] using hgridN gamma hgamma
  have hmono' : ∀ a b : ℝ, a ≤ b → F a ≤ F b := by
    intro a b hab
    apply (div_le_div_iff_of_pos_right hdenpos).2
    apply hmonoN
    exact mul_le_mul_of_nonneg_left hab halpha.le
  have hbeta0 := hbeta.1
  have hbeta1 := hbeta.2
  by_cases hbetaEq : beta = 1
  · subst beta
    have hmem : (1 : ℝ) ∈ B := by
      apply Finset.mem_image.mpr
      refine ⟨m, Finset.mem_range.mpr (Nat.lt_succ_self m), ?_⟩
      field_simp
    have h := hgrid' 1 hmem
    simpa only [sub_self] using h.trans (by linarith)
  · have hbetaLt : beta < 1 := lt_of_le_of_ne hbeta1 hbetaEq
    let j : ℕ := Nat.floor ((m : ℝ) * beta)
    have hprodNonneg : 0 ≤ (m : ℝ) * beta :=
      mul_nonneg (by positivity) hbeta0
    have hjlt : j < m := by
      dsimp [j]
      apply (Nat.floor_lt' (show m ≠ 0 by omega)).2
      nlinarith [mul_lt_mul_of_pos_left hbetaLt
        (by exact_mod_cast hmpos : (0 : ℝ) < m)]
    let lo : ℝ := (j : ℝ) / m
    let hi : ℝ := ((j + 1 : ℕ) : ℝ) / m
    have hlo : lo ≤ beta := by
      dsimp [lo, j]
      apply (div_le_iff₀ (by exact_mod_cast hmpos)).2
      have hfloor := Nat.floor_le hprodNonneg
      simpa [mul_comm] using hfloor
    have hhi : beta < hi := by
      dsimp [hi, j]
      apply (lt_div_iff₀ (by exact_mod_cast hmpos)).2
      have hfloor := Nat.lt_floor_add_one ((m : ℝ) * beta)
      convert hfloor using 1
      · ring
      · norm_num
    have hhiGrid : j + 1 ≤ m := Nat.succ_le_of_lt hjlt
    have hLoMem : lo ∈ B := by
      apply Finset.mem_image.mpr
      exact ⟨j, Finset.mem_range.mpr (Nat.lt_succ_of_lt hjlt), rfl⟩
    have hHiMem : hi ∈ B := by
      apply Finset.mem_image.mpr
      exact ⟨j + 1, Finset.mem_range.mpr (Nat.lt_succ_of_le hhiGrid), rfl⟩
    have hFlo := hgrid' lo hLoMem
    have hFhi := hgrid' hi hHiMem
    have hFmonoLo := hmono' lo beta hlo
    have hFmonoHi := hmono' beta hi hhi.le
    have hFloLower : lo - epsilon / 3 < F lo := by
      have h := (abs_lt.mp hFlo).1
      linarith
    have hFhiUpper : F hi < hi + epsilon / 3 := by
      have h := (abs_lt.mp hFhi).2
      linarith
    have hupper : F beta - beta < epsilon := by
      have hstep : hi - lo = (1 : ℝ) / m := by
        dsimp [hi, lo]
        push_cast
        field_simp
        ring
      have hgap : hi - beta ≤ (1 : ℝ) / m := by
        nlinarith [hlo, hstep]
      linarith
    have hlower : -epsilon < F beta - beta := by
      have hstep : hi - lo = (1 : ℝ) / m := by
        dsimp [hi, lo]
        push_cast
        field_simp
        ring
      have hgap : beta - lo ≤ (1 : ℝ) / m := by
        nlinarith [hhi, hstep]
      linarith
    exact (abs_lt).2 ⟨hlower, hupper⟩

end BoundedGaps.Maynard
