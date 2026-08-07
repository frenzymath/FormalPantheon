import BoundedGaps.BombieriVinogradov.Analytic.InducingEulerProductZeroGeometry
import BoundedGaps.BombieriVinogradov.Analytic.PrimitiveFunctionalEquation
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Nonvanishing on the prescribed Dirichlet explicit-formula vertical edges

The contour in `KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 115,
has real edges `-N-1/2` and `1+1/log x`. This file proves that the actual
level-character L-function is nonzero on both lines. The half-integer left
edge avoids parity-dependent primitive trivial zeros and the imaginary-axis
zeros of the finite inducing product.

Candidate-set interior conversion and horizontal-edge composition remain
separate. Semantic review: `SEM-514`.
-/

namespace BoundedGaps.Maynard

open Complex

noncomputable section

private local instance conductorNeZero
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) :
    NeZero chi.conductor :=
  ⟨chi.conductor_ne_zero⟩

private theorem gammaFactor_ne_zero_of_re_eq_neg_nat_sub_half
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    (N : ℕ) {s : ℂ} (hs : s.re = -(N : ℝ) - 1 / 2) :
    DirichletCharacter.gammaFactor chi s ≠ 0 := by
  rcases chi.even_or_odd with heven | hodd
  · rw [heven.gammaFactor_def, ne_eq, Gammaℝ_eq_zero_iff, not_exists]
    intro n hn
    have hre := congrArg Complex.re hn
    norm_num at hre
    rw [hs] at hre
    have hnat : 2 * N + 1 = 4 * n := by
      exact_mod_cast (by linarith : (2 : ℝ) * N + 1 = 4 * n)
    omega
  · rw [hodd.gammaFactor_def, ne_eq, Gammaℝ_eq_zero_iff, not_exists]
    intro n hn
    have hre := congrArg Complex.re hn
    norm_num at hre
    rw [hs] at hre
    have hnat : 2 * N = 4 * n + 1 := by
      exact_mod_cast (by linarith : (2 : ℝ) * N = 4 * n + 1)
    omega

private theorem gammaFactor_ne_zero_of_re_pos
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.gammaFactor chi s ≠ 0 := by
  rcases chi.even_or_odd with heven | hodd
  · rw [heven.gammaFactor_def]
    exact Gammaℝ_ne_zero_of_re_pos hs
  · rw [hodd.gammaFactor_def]
    exact Gammaℝ_ne_zero_of_re_pos (by simp; linarith)

private theorem primitive_LFunction_ne_zero_of_re_eq_neg_nat_sub_half
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (N : ℕ) {s : ℂ} (hs : s.re = -(N : ℝ) - 1 / 2) :
    DirichletCharacter.LFunction chi s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [zero_re] at hre
    rw [hs] at hre
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [one_re] at hre
    rw [hs] at hre
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have hreflected0 : 1 - s ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm hs1)
  have hreflected1 : 1 - s ≠ 1 := by
    intro h
    apply hs0
    linear_combination -h
  have hgamma : DirichletCharacter.gammaFactor chi s ≠ 0 :=
    gammaFactor_ne_zero_of_re_eq_neg_nat_sub_half chi N hs
  have hgammaReflected :
      DirichletCharacter.gammaFactor chi⁻¹ (1 - s) ≠ 0 :=
    gammaFactor_ne_zero_of_re_pos chi⁻¹ (by
      simp only [sub_re, one_re]
      rw [hs]
      have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      linarith)
  have hreflectedL :
      DirichletCharacter.LFunction chi⁻¹ (1 - s) ≠ 0 :=
    (chi⁻¹).LFunction_ne_zero_of_one_le_re (.inr hreflected1) (by
      simp only [sub_re, one_re]
      rw [hs]
      have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      linarith)
  have hreflectedCompleted :
      DirichletCharacter.completedLFunction chi⁻¹ (1 - s) ≠ 0 := by
    have heq :
        DirichletCharacter.completedLFunction chi⁻¹ (1 - s) =
          DirichletCharacter.LFunction chi⁻¹ (1 - s) *
            DirichletCharacter.gammaFactor chi⁻¹ (1 - s) := by
      symm
      exact (eq_div_iff hgammaReflected).mp
        (DirichletCharacter.LFunction_eq_completed_div_gammaFactor chi⁻¹
          (1 - s) (.inl hreflected0))
    rw [heq]
    exact mul_ne_zero hreflectedL hgammaReflected
  have hbase : (q : ℂ) ^ ((1 - s) - 1 / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr
      (.inl (Nat.cast_ne_zero.mpr (NeZero.ne q)))
  have hroot : DirichletCharacter.rootNumber chi ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [norm_rootNumber_of_isPrimitive chi hchi]
    exact one_ne_zero
  have hcompleted :
      DirichletCharacter.completedLFunction chi s ≠ 0 := by
    have hfun := hchi.completedLFunction_one_sub (1 - s)
    rw [show 1 - (1 - s) = s by ring] at hfun
    rw [hfun]
    exact mul_ne_zero (mul_ne_zero hbase hroot) hreflectedCompleted
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor chi s
    (.inl hs0)]
  exact div_ne_zero hcompleted hgamma

private theorem LFunction_ne_zero_of_re_eq_neg_nat_sub_half
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (N : ℕ)
    {s : ℂ} (hs : s.re = -(N : ℝ) - 1 / 2) :
    DirichletCharacter.LFunction chi s ≠ 0 := by
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [one_re] at hre
    rw [hs] at hre
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  rw [LFunction_eq_inducingPrimitive_mul_inducingEulerProduct chi (.inr hs1)]
  apply mul_ne_zero
  · exact primitive_LFunction_ne_zero_of_re_eq_neg_nat_sub_half
      chi.primitiveCharacter chi.primitiveCharacter_isPrimitive N hs
  · intro hproduct
    have hre := re_eq_zero_of_inducingEulerProduct_eq_zero chi hproduct
    rw [hs] at hre
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith

/-- The actual Dirichlet L-function is nonzero on both prescribed vertical
edges of the explicit-formula rectangle. -/
theorem LFunction_ne_zero_on_dirichletExplicitFormulaVerticalEdges
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (x : ℝ) (hx : 1 < x) (N : ℕ) (t : ℝ) :
    DirichletCharacter.LFunction chi
        (((-(N : ℝ) - 1 / 2 : ℝ) : ℂ) + t * I) ≠ 0 ∧
      DirichletCharacter.LFunction chi
        (((1 + 1 / Real.log x : ℝ) : ℂ) + t * I) ≠ 0 := by
  constructor
  · apply LFunction_ne_zero_of_re_eq_neg_nat_sub_half chi N
    simp
  · have hsre :
        ((((1 + 1 / Real.log x : ℝ) : ℂ) + t * I)).re =
          1 + 1 / Real.log x := by
      simp
    have hlog : 0 < Real.log x := Real.log_pos hx
    have hsreGt :
        1 < ((((1 + 1 / Real.log x : ℝ) : ℂ) + t * I)).re := by
      rw [hsre]
      linarith [one_div_pos.mpr hlog]
    apply chi.LFunction_ne_zero_of_one_le_re
    · refine .inr ?_
      intro hs
      have hre := congrArg Complex.re hs
      simp only [one_re] at hre
      exact (ne_of_gt hsreGt) hre
    · exact hsreGt.le

end

end BoundedGaps.Maynard
