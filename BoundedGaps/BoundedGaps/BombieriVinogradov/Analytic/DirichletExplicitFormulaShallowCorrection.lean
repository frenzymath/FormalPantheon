import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaPrimitiveShallowCandidates

/-!
# Shallow explicit-formula correction absorption

`KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 114--115,
Theorem 11.3 and equation (11.5), display the optional principal main term `x`
and the nontrivial-zero sum. SEM-525's exact modified-kernel contour
contribution instead has principal term `x - 1` and, for an even nonprincipal
primitive character, the additional origin contribution `-log x`.

This file packages those mutually exclusive additive corrections and absorbs
them into the source scale `x * log(x*q)^2 / T` under `x >= T >= 2`. It does
not estimate a contour edge or assert the explicit formula. Semantic review:
`SEM-526`.
-/

noncomputable section

namespace BoundedGaps.Maynard

open Complex
open scoped BigOperators

noncomputable local instance shallowMainTermCorrectionDecidable
    (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- The source's optional principal main term minus its grouped nontrivial-zero
kernel sum. This is an algebraic target, not an explicit-formula theorem. -/
noncomputable def dirichletExplicitFormulaMainZeroTerms
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (x T : ℝ) : ℂ :=
  (if chi = 1 then (x : ℂ) else 0) -
    dirichletNontrivialZeroKernelSum chi x T

/-- The additive difference between the exact shallow modified-kernel
candidate sum and the source's displayed main/zero terms. -/
noncomputable def dirichletExplicitFormulaShallowMainTermCorrection
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  if chi = 1 then -1
  else if chi.Even then -(Real.log x : ℂ) else 0

/-- The scalar error scale in Koukoulopoulos Theorem 11.3. -/
def dirichletExplicitFormulaErrorScale
    (x : ℝ) (q : ℕ) (T : ℝ) : ℝ :=
  x * Real.log (x * (q : ℝ)) ^ 2 / T

/-- The exact primitive shallow candidate sum is the source main/zero
expression plus the principal or even-origin correction. -/
theorem
    sum_dirichletExplicitFormulaShallowCandidateContribution_eq_mainZeroTerms_add_correction_of_isPrimitive
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi.IsPrimitive) (x T : ℝ) (hx : 1 < x) :
    (∑ rho ∈
        dirichletExplicitFormulaShallowCandidateSingularitiesFinset chi x T,
      dirichletExplicitFormulaCandidateContribution chi x rho) =
      dirichletExplicitFormulaMainZeroTerms chi x T +
        dirichletExplicitFormulaShallowMainTermCorrection chi x := by
  rw [sum_dirichletExplicitFormulaShallowCandidateContribution_eq_of_isPrimitive
    chi hchi x T hx]
  classical
  by_cases hchiOne : chi = 1
  · simp [dirichletExplicitFormulaMainZeroTerms,
      dirichletExplicitFormulaShallowMainTermCorrection, hchiOne]
    ring
  · by_cases heven : chi.Even
    · simp [dirichletExplicitFormulaMainZeroTerms,
        dirichletExplicitFormulaShallowMainTermCorrection, hchiOne, heven]
      ring
    · simp [dirichletExplicitFormulaMainZeroTerms,
        dirichletExplicitFormulaShallowMainTermCorrection, hchiOne, heven]

private theorem norm_dirichletExplicitFormulaShallowMainTermCorrection_eq
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 1 < x) :
    ‖dirichletExplicitFormulaShallowMainTermCorrection chi x‖ =
      if chi = 1 then 1 else if chi.Even then Real.log x else 0 := by
  classical
  have hlog : 0 < Real.log x := Real.log_pos hx
  by_cases hchiOne : chi = 1
  · simp [dirichletExplicitFormulaShallowMainTermCorrection, hchiOne]
  · by_cases heven : chi.Even
    · simp [dirichletExplicitFormulaShallowMainTermCorrection,
        hchiOne, heven, Complex.norm_real, abs_of_pos hlog]
    · simp [dirichletExplicitFormulaShallowMainTermCorrection,
        hchiOne, heven]

/-- On the source range `x >= 2`, both mutually exclusive corrections have
norm at most `2 * log x`. -/
theorem norm_dirichletExplicitFormulaShallowMainTermCorrection_le_two_mul_log
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 2 ≤ x) :
    ‖dirichletExplicitFormulaShallowMainTermCorrection chi x‖ ≤
      2 * Real.log x := by
  have hxone : 1 < x := lt_of_lt_of_le one_lt_two hx
  rw [norm_dirichletExplicitFormulaShallowMainTermCorrection_eq chi hxone]
  have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos
      (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  have hlogmono : Real.log 2 ≤ Real.log x :=
    Real.log_le_log (by norm_num) hx
  have hone : (1 : ℝ) ≤ 2 * Real.log x := by linarith
  have hlog : 0 ≤ Real.log x := (Real.log_pos hxone).le
  classical
  by_cases hchiOne : chi = 1
  · simp [hchiOne, hone]
  · by_cases heven : chi.Even
    · simp only [if_neg hchiOne, if_pos heven]
      linarith
    · simp [hchiOne, heven, hlog]

/-- The principal and origin corrections are absorbed by four copies of the
literal Theorem 11.3 error scale. -/
theorem
    norm_dirichletExplicitFormulaShallowMainTermCorrection_le_four_mul_errorScale
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {x T : ℝ} (hT : 2 ≤ T) (hTx : T ≤ x) :
    ‖dirichletExplicitFormulaShallowMainTermCorrection chi x‖ ≤
      4 * dirichletExplicitFormulaErrorScale x q T := by
  have hx : 2 ≤ x := hT.trans hTx
  have hxpos : 0 < x := zero_lt_two.trans_le hx
  have hTpos : 0 < T := zero_lt_two.trans_le hT
  have hq : (1 : ℝ) ≤ q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hxqx : x ≤ x * (q : ℝ) := by
    simpa using mul_le_mul_of_nonneg_left hq hxpos.le
  have hlogxProduct : Real.log x ≤ Real.log (x * (q : ℝ)) :=
    Real.log_le_log hxpos hxqx
  have hlogProductHalf : (1 / 2 : ℝ) ≤
      Real.log (x * (q : ℝ)) := by
    have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have h := Real.one_sub_inv_le_log_of_pos
        (show (0 : ℝ) < 2 by norm_num)
      norm_num at h ⊢
      exact h
    have hlogTwoX : Real.log 2 ≤ Real.log x :=
      Real.log_le_log (by norm_num) hx
    linarith
  have hxT : 1 ≤ x / T :=
    (le_div_iff₀ hTpos).2 (by simpa using hTx)
  have hlogxLeSquare :
      2 * Real.log x ≤ 4 * Real.log (x * (q : ℝ)) ^ 2 := by
    have hlinear : 2 * Real.log x ≤
        2 * Real.log (x * (q : ℝ)) := by linarith
    have hsquare : 2 * Real.log (x * (q : ℝ)) ≤
        4 * Real.log (x * (q : ℝ)) ^ 2 := by
      nlinarith [sq_nonneg (Real.log (x * (q : ℝ)) - 1 / 2)]
    exact hlinear.trans hsquare
  calc
    ‖dirichletExplicitFormulaShallowMainTermCorrection chi x‖ ≤
        2 * Real.log x :=
      norm_dirichletExplicitFormulaShallowMainTermCorrection_le_two_mul_log
        chi hx
    _ ≤ 4 * Real.log (x * (q : ℝ)) ^ 2 := hlogxLeSquare
    _ ≤ 4 * dirichletExplicitFormulaErrorScale x q T := by
      rw [dirichletExplicitFormulaErrorScale, div_eq_mul_inv, mul_assoc]
      have hratio : 1 ≤ x * T⁻¹ := by
        simpa [div_eq_mul_inv] using hxT
      nlinarith [sq_nonneg (Real.log (x * (q : ℝ)))]

/-- The exact candidate sum differs from the source main/zero expression by
at most four copies of the displayed explicit-formula error scale. -/
theorem
    norm_sum_dirichletExplicitFormulaShallowCandidateContribution_sub_mainZeroTerms_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi.IsPrimitive) {x T : ℝ} (hT : 2 ≤ T) (hTx : T ≤ x) :
    ‖(∑ rho ∈
          dirichletExplicitFormulaShallowCandidateSingularitiesFinset chi x T,
        dirichletExplicitFormulaCandidateContribution chi x rho) -
        dirichletExplicitFormulaMainZeroTerms chi x T‖ ≤
      4 * dirichletExplicitFormulaErrorScale x q T := by
  rw [sum_dirichletExplicitFormulaShallowCandidateContribution_eq_mainZeroTerms_add_correction_of_isPrimitive
    chi hchi x T (lt_of_lt_of_le one_lt_two (hT.trans hTx)),
    add_sub_cancel_left]
  exact
    norm_dirichletExplicitFormulaShallowMainTermCorrection_le_four_mul_errorScale
      chi hT hTx

end BoundedGaps.Maynard
