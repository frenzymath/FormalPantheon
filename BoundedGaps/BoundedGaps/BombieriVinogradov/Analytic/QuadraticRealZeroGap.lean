import BoundedGaps.BombieriVinogradov.Analytic.NearOneLFunction
import BoundedGaps.BombieriVinogradov.Analytic.QuadraticLValueLowerBound
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Effective real-zero gap for quadratic Dirichlet L-functions

The near-one derivative estimate is integrated along the real axis and
combined with the effective positive lower bound for `L(1, chi)`.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 124--125,
equations (12.11)--(12.12) and Theorem 12.8.  Semantic review: `SEM-548`.
-/

noncomputable section

open Set

namespace BoundedGaps.Maynard

private lemma one_lt_log_modulus_of_character_ne_one
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) :
    1 < Real.log (q : ℝ) := by
  have hqThree : 3 ≤ q := by
    by_contra hq
    have hqPos : 0 < q := NeZero.pos q
    have hqNeOne : q ≠ 1 := fun h ↦ hchi (chi.level_one' h)
    have hqTwo : q = 2 := by omega
    subst q
    have hcard : Nat.card (DirichletCharacter ℂ 2) = 1 := by
      rw [DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
      norm_num
    exact hchi ((Nat.card_eq_one_iff_unique.mp hcard).1.elim chi 1)
  have hqThreeReal : (3 : ℝ) ≤ q := by exact_mod_cast hqThree
  exact (by norm_num : (1 : ℝ) < 1.0986122885).trans
    (Real.log_three_gt_d9.trans_le
      (Real.log_le_log (by norm_num) hqThreeReal))

/-- Norm form of the fundamental-theorem step from a near-one real point to
one. -/
theorem norm_LFunction_one_sub_ofReal_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {beta : ℝ}
    (hbetaNear :
      1 - 1 / (4 * Real.log (q : ℝ)) ≤ beta)
    (hbetaOne : beta ≤ 1) :
    ‖DirichletCharacter.LFunction chi (1 : ℂ) -
        DirichletCharacter.LFunction chi (beta : ℂ)‖ ≤
      512 * (Real.log (q : ℝ)) ^ 2 * (1 - beta) := by
  let f : ℝ → ℂ := fun sigma ↦
    DirichletCharacter.LFunction chi (sigma : ℂ)
  let f' : ℝ → ℂ := fun sigma ↦
    deriv (DirichletCharacter.LFunction chi) (sigma : ℂ)
  have hderiv : ∀ sigma ∈ Icc beta 1,
      HasDerivWithinAt f (f' sigma) (Icc beta 1) sigma := by
    intro sigma _
    exact ((DirichletCharacter.differentiable_LFunction hchi
      (sigma : ℂ)).hasDerivAt.comp_ofReal).hasDerivWithinAt
  have hbound : ∀ sigma ∈ Ico beta 1,
      ‖f' sigma‖ ≤ 512 * (Real.log (q : ℝ)) ^ 2 := by
    intro sigma hsigma
    dsimp [f']
    apply norm_deriv_LFunction_ofReal_near_one_le hq chi hchi
    · exact hbetaNear.trans hsigma.1
    · exact hsigma.2.le
  have hmean := norm_image_sub_le_of_norm_deriv_le_segment'
    hderiv hbound (1 : ℝ) (right_mem_Icc.mpr hbetaOne)
  simpa [f] using hmean

/-- Explicit weak gap between one and every real zero at or below one of a
square-principal nonprincipal character. -/
theorem effectiveQuadraticRealZeroGap
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (hsquare : chi ^ 2 = 1)
    {beta : ℝ} (hbetaOne : beta ≤ 1)
    (hzero : DirichletCharacter.LFunction chi (beta : ℂ) = 0) :
    1 / ((2 ^ 22 : ℝ) * Real.sqrt (q : ℝ) *
        (Real.log (q : ℝ)) ^ 4) ≤
      1 - beta := by
  let L := Real.log (q : ℝ)
  let D := (2 ^ 22 : ℝ) * Real.sqrt (q : ℝ) * L ^ 4
  have hLpos : 0 < L := Real.log_pos (by exact_mod_cast hq)
  have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hq.le
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt (q : ℝ) := by
    simpa using Real.sqrt_le_sqrt hqOne
  have hLone : 1 < L := by
    exact one_lt_log_modulus_of_character_ne_one chi hchi
  have hLpow : L ≤ L ^ 4 := by
    simpa using pow_le_pow_right₀ hLone.le (show 1 ≤ 4 by norm_num)
  have hdenom : 4 * L ≤ D := by
    have hprod : L ≤ Real.sqrt (q : ℝ) * L ^ 4 := by
      calc
        L ≤ L ^ 4 := hLpow
        _ = 1 * L ^ 4 := by ring
        _ ≤ Real.sqrt (q : ℝ) * L ^ 4 := by gcongr
    dsimp [D]
    nlinarith
  have hfarTarget : 1 / D ≤ 1 / (4 * L) :=
    one_div_le_one_div_of_le (by positivity) hdenom
  by_cases hbetaNear : 1 - 1 / (4 * L) ≤ beta
  · have hmean := norm_LFunction_one_sub_ofReal_le hq chi hchi
      (by simpa [L] using hbetaNear) hbetaOne
    have hmeanZero :
        ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ ≤
          512 * L ^ 2 * (1 - beta) := by
      simpa [hzero, L] using hmean
    have hLower := effectiveQuadraticLValueLowerBound hq chi hchi hsquare
    have hLowerRe :
        1 / (8192 * Real.sqrt (q : ℝ) * L ^ 2) ≤
          (DirichletCharacter.LFunction chi (1 : ℂ)).re := by
      have hLowerReRaw := (Complex.le_def.mp hLower).1
      change
        1 / (8192 * Real.sqrt (q : ℝ) * L ^ 2) ≤
          (DirichletCharacter.LFunction chi (1 : ℂ)).re at hLowerReRaw
      exact hLowerReRaw
    have hcombined :
        1 / (8192 * Real.sqrt (q : ℝ) * L ^ 2) ≤
          512 * L ^ 2 * (1 - beta) :=
      hLowerRe.trans (Complex.re_le_norm _ |>.trans hmeanZero)
    have hscalePos : 0 < 512 * L ^ 2 := by positivity
    have hsqrtPos : 0 < Real.sqrt (q : ℝ) := by positivity
    calc
      1 / D =
          (1 / (8192 * Real.sqrt (q : ℝ) * L ^ 2)) /
            (512 * L ^ 2) := by
        dsimp [D]
        field_simp [hLpos.ne', hsqrtPos.ne']
        norm_num
      _ ≤ (512 * L ^ 2 * (1 - beta)) / (512 * L ^ 2) :=
        (div_le_div_iff_of_pos_right hscalePos).2 hcombined
      _ = 1 - beta := by field_simp
  · exact hfarTarget.trans (by
      have : 1 / (4 * L) < 1 - beta := by linarith
      exact this.le)

/-- Real-axis nonvanishing in the explicit weak quadratic zero-free
interval. -/
theorem effectiveQuadraticLFunction_ofReal_ne_zero
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (hsquare : chi ^ 2 = 1)
    {sigma : ℝ}
    (hsigma :
      1 - 1 / ((2 ^ 22 : ℝ) * Real.sqrt (q : ℝ) *
        (Real.log (q : ℝ)) ^ 4) < sigma) :
    DirichletCharacter.LFunction chi (sigma : ℂ) ≠ 0 := by
  by_cases hsigmaOne : sigma ≤ 1
  · intro hzero
    have hgap := effectiveQuadraticRealZeroGap hq chi hchi hsquare
      hsigmaOne hzero
    linarith
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re chi
      (.inl hchi) (by simp; linarith)

end BoundedGaps.Maynard
