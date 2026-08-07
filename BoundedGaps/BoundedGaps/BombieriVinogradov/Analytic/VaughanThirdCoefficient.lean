import BoundedGaps.BombieriVinogradov.Analytic.VaughanTwistedDecomposition
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# Vaughan's third-term coefficient bound

This file proves the pointwise coefficient estimate in
Akbary--Hambrook2013v2, Section 6, equation (6.11). It contains no aggregate
third-term estimate or large-sieve input.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators ArithmeticFunction.vonMangoldt

/-- The restricted `Lambda(m) * mu(d)` coefficient grouped by `m * d = t`. -/
noncomputable def vaughanThirdCoefficient
    (U V : ℝ) (t : ℕ) : ℝ :=
  ∑ md ∈ t.divisorsAntidiagonal.filter
      (fun md : ℕ × ℕ ↦
        (md.1 : ℝ) ≤ U ∧ (md.2 : ℝ) ≤ V),
    ArithmeticFunction.vonMangoldt md.1 *
      (ArithmeticFunction.moebius md.2 : ℝ)

/-- Equation (6.11), strengthened by removing the harmless character factor. -/
theorem abs_vaughanThirdCoefficient_le_log
    (U V : ℝ) (t : ℕ) :
    |vaughanThirdCoefficient U V t| ≤ Real.log t := by
  unfold vaughanThirdCoefficient
  calc
    |∑ md ∈ t.divisorsAntidiagonal.filter
        (fun md : ℕ × ℕ ↦ (md.1 : ℝ) ≤ U ∧ (md.2 : ℝ) ≤ V),
        ArithmeticFunction.vonMangoldt md.1 *
          (ArithmeticFunction.moebius md.2 : ℝ)| ≤
      ∑ md ∈ t.divisorsAntidiagonal.filter
        (fun md : ℕ × ℕ ↦ (md.1 : ℝ) ≤ U ∧ (md.2 : ℝ) ≤ V),
        |ArithmeticFunction.vonMangoldt md.1 *
          (ArithmeticFunction.moebius md.2 : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ md ∈ t.divisorsAntidiagonal.filter
        (fun md : ℕ × ℕ ↦ (md.1 : ℝ) ≤ U ∧ (md.2 : ℝ) ≤ V),
        ArithmeticFunction.vonMangoldt md.1 := by
      apply Finset.sum_le_sum
      intro md _hmd
      have hmuInt := ArithmeticFunction.abs_moebius_le_one (n := md.2)
      have hmu : |(ArithmeticFunction.moebius md.2 : ℝ)| ≤ 1 := by
        exact_mod_cast hmuInt
      rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      simpa using mul_le_mul_of_nonneg_left hmu
        ArithmeticFunction.vonMangoldt_nonneg
    _ ≤ ∑ md ∈ t.divisorsAntidiagonal,
        ArithmeticFunction.vonMangoldt md.1 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun md _hmd _hnot ↦ ArithmeticFunction.vonMangoldt_nonneg)
    _ = ∑ m ∈ t.divisors, ArithmeticFunction.vonMangoldt m := by
      exact Nat.sum_divisorsAntidiagonal
        (fun m _d ↦ ArithmeticFunction.vonMangoldt m)
    _ = Real.log t := ArithmeticFunction.vonMangoldt_sum

/-- Complex-norm form of the third-coefficient estimate. -/
theorem norm_vaughanThirdCoefficient_le_log
    (U V : ℝ) (t : ℕ) :
    ‖((vaughanThirdCoefficient U V t : ℝ) : ℂ)‖ ≤ Real.log t := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact abs_vaughanThirdCoefficient_le_log U V t

/-- Literal character-weighted form of equation (6.11). -/
theorem norm_vaughanThirdCoefficient_mul_character_le_log
    (U V : ℝ) (t q : ℕ) (χ : DirichletCharacter ℂ q) :
    ‖((vaughanThirdCoefficient U V t : ℝ) : ℂ) * χ t‖ ≤ Real.log t := by
  rw [norm_mul]
  calc
    ‖((vaughanThirdCoefficient U V t : ℝ) : ℂ)‖ * ‖χ t‖ ≤
        ‖((vaughanThirdCoefficient U V t : ℝ) : ℂ)‖ * 1 :=
      mul_le_mul_of_nonneg_left (χ.norm_le_one t) (norm_nonneg _)
    _ = ‖((vaughanThirdCoefficient U V t : ℝ) : ℂ)‖ := mul_one _
    _ ≤ Real.log t := norm_vaughanThirdCoefficient_le_log U V t

/-- The coefficient norm is bounded by the logarithm of any positive cutoff
above its index. -/
theorem norm_vaughanThirdCoefficient_le_log_cutoff
    {U V : ℝ} {t : ℕ} (ht : 0 < t) (htU : (t : ℝ) ≤ U) :
    ‖((vaughanThirdCoefficient U V t : ℝ) : ℂ)‖ ≤ Real.log U := by
  exact (norm_vaughanThirdCoefficient_le_log U V t).trans
    (Real.log_le_log (by exact_mod_cast ht) htU)

/-- Character-weighted cutoff form of the third-coefficient estimate. -/
theorem norm_vaughanThirdCoefficient_mul_character_le_log_cutoff
    {U V : ℝ} {t q : ℕ} (χ : DirichletCharacter ℂ q)
    (ht : 0 < t) (htU : (t : ℝ) ≤ U) :
    ‖((vaughanThirdCoefficient U V t : ℝ) : ℂ) * χ t‖ ≤ Real.log U := by
  exact (norm_vaughanThirdCoefficient_mul_character_le_log U V t q χ).trans
    (Real.log_le_log (by exact_mod_cast ht) htU)

end BoundedGaps.Maynard
