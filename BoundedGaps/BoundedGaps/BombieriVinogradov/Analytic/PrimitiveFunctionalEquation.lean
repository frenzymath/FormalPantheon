import BoundedGaps.BombieriVinogradov.Analytic.PrimitiveGaussSum
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Primitive Dirichlet functional equation

This file rewrites Mathlib's completed primitive functional equation as an
exact identity for the ordinary Dirichlet `LFunction` on `Re s <= 1/2`.
The source normalization is Koukoulopoulos, printed p. 111, equation (11.3)
and Theorem 11.1; see semantic review SEM-475.
-/

namespace BoundedGaps.Maynard

open Complex

private lemma gammaFactor_inv_one_sub_ne_zero
    {q : ℕ} (chi : DirichletCharacter ℂ q) {s : ℂ}
    (hs : s.re ≤ (1 / 2 : ℝ)) :
    DirichletCharacter.gammaFactor chi⁻¹ (1 - s) ≠ 0 := by
  rcases chi⁻¹.even_or_odd with heven | hodd
  · rw [heven.gammaFactor_def]
    exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  · rw [hodd.gammaFactor_def]
    exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)

/-- A primitive Dirichlet root number has unit complex norm.

This is the norm-one observation immediately before Koukoulopoulos, printed
p. 111, Theorem 11.1, using the primitive Gauss-sum norm from printed p. 105,
Theorem 10.4. -/
theorem norm_rootNumber_of_isPrimitive
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive) :
    ‖DirichletCharacter.rootNumber chi‖ = 1 := by
  have hq0 : q ≠ 0 := NeZero.ne q
  have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
  rw [DirichletCharacter.rootNumber, norm_div, norm_div,
    norm_gaussSum_stdAddChar_of_isPrimitive chi hchi, norm_pow,
    Complex.norm_I, one_pow, div_one,
    Complex.norm_natCast_cpow_of_pos hqpos]
  simp [Real.sqrt_eq_rpow, hq0]

/-- The primitive functional equation rewritten for the ordinary L-function
on the closed half-plane `Re(s) <= 1/2`.

The denominator Gamma factor is deliberately allowed to vanish at a trivial
zero. The real-part hypothesis is used only to show that the reflected Gamma
factor is nonzero. -/
theorem LFunction_eq_functionalEquation_of_isPrimitive
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (s : ℂ) (hs : s.re ≤ (1 / 2 : ℝ)) :
    DirichletCharacter.LFunction chi s =
      (q : ℂ) ^ ((1 / 2 : ℂ) - s) *
        DirichletCharacter.rootNumber chi *
        DirichletCharacter.LFunction chi⁻¹ (1 - s) *
        (DirichletCharacter.gammaFactor chi⁻¹ (1 - s) /
          DirichletCharacter.gammaFactor chi s) := by
  have hqne : q ≠ 1 := Nat.ne_of_gt hq
  have hcompleted :
      DirichletCharacter.completedLFunction chi s =
        (q : ℂ) ^ ((1 / 2 : ℂ) - s) *
          DirichletCharacter.rootNumber chi *
          DirichletCharacter.completedLFunction chi⁻¹ (1 - s) := by
    convert hchi.completedLFunction_one_sub (1 - s) using 1 <;> ring_nf
  have hgamma := gammaFactor_inv_one_sub_ne_zero chi hs
  have hreflected :
      DirichletCharacter.completedLFunction chi⁻¹ (1 - s) =
        DirichletCharacter.LFunction chi⁻¹ (1 - s) *
          DirichletCharacter.gammaFactor chi⁻¹ (1 - s) := by
    symm
    exact (eq_div_iff hgamma).mp
      (DirichletCharacter.LFunction_eq_completed_div_gammaFactor chi⁻¹
        (1 - s) (.inr hqne))
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor chi s (.inr hqne),
    hcompleted, hreflected]
  ring

/-- The exact norm factorization obtained from the primitive functional
equation and the unit norm of its root number. -/
theorem norm_LFunction_eq_functionalEquation_of_isPrimitive
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (s : ℂ) (hs : s.re ≤ (1 / 2 : ℝ)) :
    ‖DirichletCharacter.LFunction chi s‖ =
      (q : ℝ) ^ ((1 : ℝ) / 2 - s.re) *
        ‖DirichletCharacter.LFunction chi⁻¹ (1 - s)‖ *
        ‖DirichletCharacter.gammaFactor chi⁻¹ (1 - s) /
          DirichletCharacter.gammaFactor chi s‖ := by
  rw [LFunction_eq_functionalEquation_of_isPrimitive hq chi hchi s hs,
    norm_mul, norm_mul, norm_mul, norm_rootNumber_of_isPrimitive chi hchi,
    Complex.norm_natCast_cpow_of_pos (Nat.zero_lt_of_lt hq)]
  norm_num

end BoundedGaps.Maynard
