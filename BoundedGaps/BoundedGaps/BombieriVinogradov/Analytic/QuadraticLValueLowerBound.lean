import BoundedGaps.BombieriVinogradov.Analytic.DirichletLFunctionConjugation
import BoundedGaps.BombieriVinogradov.Analytic.QuadraticLValueCutoff
import BoundedGaps.BombieriVinogradov.Analytic.QuadraticZetaLFunctionComparison
import BoundedGaps.BombieriVinogradov.Analytic.QuadraticZetaSquareScaleLower

/-!
# Effective lower bound for quadratic L-values at one

The positive smoothed quadratic convolution is compared with its
`L(1, chi)` main term at the explicit cutoff from `QuadraticLValueCutoff`.
This gives a weak but fully effective lower bound, uniformly for primitive
and imprimitive square-principal nonprincipal characters.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 124--125,
Theorem 12.8. Semantic review: `SEM-547`.
-/

noncomputable section

open scoped ComplexOrder

namespace BoundedGaps.Maynard

/-- At one, the L-function of a square-principal nonprincipal character is
real. -/
theorem LFunction_one_im_eq_zero_of_sq_eq_one
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (hsquare : chi ^ 2 = 1) :
    (DirichletCharacter.LFunction chi (1 : ℂ)).im = 0 := by
  have hconj := LFunction_conj_of_sq_eq_one chi hchi hsquare (1 : ℂ)
  apply Complex.conj_eq_iff_im.mp
  simpa using hconj.symm

private theorem norm_quadraticZetaLinearSmoothedSum_sub_half_LFunction_cutoff_le
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) :
    ‖quadraticZetaLinearSmoothedSum chi (quadraticLValueCutoff q) -
        ((quadraticLValueCutoff q : ℂ) / 2) *
          DirichletCharacter.LFunction chi (1 : ℂ)‖ ≤
      (6 + 4 * Real.log (quadraticLValueCutoff q : ℝ)) *
        Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
  have hXpos : 0 < quadraticLValueCutoff q := by
    exact lt_of_lt_of_le (by norm_num) (four_le_quadraticLValueCutoff hq)
  have hrem := norm_quadraticZetaSwappedEulerRemainder_le hq chi hchi hXpos
  have hcomparison :=
    norm_quadraticZetaLinearSmoothedSum_sub_half_LFunction_le
      hq chi hchi hXpos
        (4 * (1 + Real.log (quadraticLValueCutoff q : ℝ)) *
          Real.sqrt (q : ℝ) * Real.log (q : ℝ)) hrem
  calc
    ‖quadraticZetaLinearSmoothedSum chi (quadraticLValueCutoff q) -
        ((quadraticLValueCutoff q : ℂ) / 2) *
          DirichletCharacter.LFunction chi (1 : ℂ)‖ ≤
      2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) +
        4 * (1 + Real.log (quadraticLValueCutoff q : ℝ)) *
          Real.sqrt (q : ℝ) * Real.log (q : ℝ) := hcomparison
    _ = (6 + 4 * Real.log (quadraticLValueCutoff q : ℝ)) *
        Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by ring

/-- Effective Theorem 12.8 specialization with all constants displayed. -/
theorem effectiveQuadraticLValueLowerBound
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (hsquare : chi ^ 2 = 1) :
    (((1 / (8192 * Real.sqrt (q : ℝ) *
        (Real.log (q : ℝ)) ^ 2) : ℝ) : ℂ)) ≤
      DirichletCharacter.LFunction chi (1 : ℂ) := by
  let X := quadraticLValueCutoff q
  let T := quadraticZetaLinearSmoothedSum chi X
  let L := DirichletCharacter.LFunction chi (1 : ℂ)
  let R := Real.sqrt (X : ℝ)
  have hXfour : 4 ≤ X := by
    simpa [X] using four_le_quadraticLValueCutoff hq
  have hXpos : 0 < X := by omega
  have hXrealPos : (0 : ℝ) < X := by exact_mod_cast hXpos
  have hRpos : 0 < R := by
    exact Real.sqrt_pos.2 hXrealPos
  have hLim : L.im = 0 := by
    simpa [L] using LFunction_one_im_eq_zero_of_sq_eq_one chi hchi hsquare
  have hTlower : (((3 / 8 : ℝ) * R : ℝ) : ℂ) ≤ T := by
    simpa [X, T, R] using
      three_eighths_mul_real_sqrt_le_quadraticZetaLinearSmoothedSum
        hsquare hXfour
  have hTre : (3 / 8 : ℝ) * R ≤ T.re := by
    simpa using (Complex.le_def.mp hTlower).1
  have hTim : T.im = 0 := by
    simpa using (Complex.le_def.mp hTlower).2.symm
  have hnorm :
      ‖T - ((X : ℂ) / 2) * L‖ ≤ (1 / 8 : ℝ) * R := by
    have hcomparison :=
      norm_quadraticZetaLinearSmoothedSum_sub_half_LFunction_cutoff_le
        hq chi hchi
    have herror := quadraticLValueComparisonError_le hq
    exact (by simpa [X, T, L, R] using hcomparison.trans herror)
  have hdiffRe :
      T.re - ((X : ℝ) / 2) * L.re ≤ (1 / 8 : ℝ) * R := by
    have habs := (Complex.abs_re_le_norm (T - ((X : ℂ) / 2) * L)).trans hnorm
    have hupper := (abs_le.mp habs).2
    simpa [Complex.mul_re, hLim] using hupper
  have hmainLower :
      (1 / 4 : ℝ) * R ≤ ((X : ℝ) / 2) * L.re := by
    linarith
  have hhalfXPos : 0 < (X : ℝ) / 2 := by positivity
  have hLlower : (1 / (2 * R) : ℝ) ≤ L.re := by
    apply (mul_le_mul_iff_of_pos_left hhalfXPos).mp
    calc
      ((X : ℝ) / 2) * (1 / (2 * R) : ℝ) = (1 / 4 : ℝ) * R := by
        have hRsq : R ^ 2 = (X : ℝ) := by
          dsimp [R]
          exact Real.sq_sqrt hXrealPos.le
        field_simp [hRpos.ne']
        nlinarith
      _ ≤ ((X : ℝ) / 2) * L.re := hmainLower
  have hsqrtUpper :
      R ≤ 4096 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2 := by
    simpa [X, R] using sqrt_quadraticLValueCutoff_le hq
  have hdenom :
      2 * R ≤ 8192 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2 := by
    nlinarith
  have hreciprocal :
      (1 / (8192 * Real.sqrt (q : ℝ) *
          (Real.log (q : ℝ)) ^ 2) : ℝ) ≤ 1 / (2 * R) :=
    one_div_le_one_div_of_le (by positivity) hdenom
  refine Complex.le_def.mpr ⟨?_, ?_⟩
  · change (1 / (8192 * Real.sqrt (q : ℝ) *
        (Real.log (q : ℝ)) ^ 2) : ℝ) ≤
      (DirichletCharacter.LFunction chi (1 : ℂ)).re
    simpa only [L] using hreciprocal.trans hLlower
  · change (0 : ℝ) = (DirichletCharacter.LFunction chi (1 : ℂ)).im
    simpa only [L] using hLim.symm

end BoundedGaps.Maynard
