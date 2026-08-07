import BoundedGaps.BombieriVinogradov.Analytic.QuadraticZetaEulerMaclaurin
import BoundedGaps.BombieriVinogradov.Analytic.QuadraticZetaSmoothedSquareLower
import BoundedGaps.BombieriVinogradov.Analytic.PositiveDivisorPairReindex
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Direct Euler remainder for the quadratic zeta cutoff

The finite divisor reindex and the source-facing Euler--Maclaurin identity are
proved separately from the later swapped-integral estimate.  This keeps the
positive-factor endpoint and every complex/real coercion visible.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, Theorem 12.8,
pp. 124--125.  Semantic review: `SEM-545`.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace BoundedGaps.Maynard

private theorem mem_positiveFactorPairs_quadratic
    {X : ℕ} (p : ℕ × ℕ) :
    p ∈ positiveFactorPairs X ↔
      p.1 ∈ Finset.Icc 1 X ∧ p.2 ∈ Finset.Icc 1 (X / p.1) := by
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hp, hprod⟩
    rcases Finset.mem_product.mp hp with ⟨hp₁, hp₂⟩
    rw [Finset.mem_Ioc] at hp₁ hp₂
    exact ⟨Finset.mem_Icc.mpr ⟨hp₁.1, hp₁.2⟩,
      Finset.mem_Icc.mpr ⟨hp₂.1,
        (Nat.le_div_iff_mul_le hp₁.1).mpr (by
          simpa only [Nat.mul_comm] using hprod)⟩⟩
  · rintro ⟨hm, hk⟩
    rw [Finset.mem_Icc] at hm hk
    have hprod : p.1 * p.2 ≤ X := by
      simpa only [Nat.mul_comm] using
        (Nat.le_div_iff_mul_le hm.1).mp hk.2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr
        ⟨Finset.mem_Ioc.mpr hm,
          Finset.mem_Ioc.mpr
            ⟨hk.1, hk.2.trans (Nat.div_le_self X p.1)⟩⟩,
        hprod⟩

private theorem sum_divisors_cutoff_eq_nested_quadratic
    {X : ℕ} (f : ℕ → ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 X, ∑ d ∈ n.divisors, f n d) =
      ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 (X / a), f (a * b) a := by
  calc
    (∑ n ∈ Finset.Icc 1 X, ∑ d ∈ n.divisors, f n d) =
        ∑ n ∈ Finset.Ioc 0 X, ∑ d ∈ n.divisors, f n d := by
      rw [show Finset.Icc 1 X = Finset.Ioc 0 X by
        simpa using Finset.Icc_succ_left_eq_Ioc 0 X]
    _ = ∑ p ∈ positiveFactorPairs X, f (p.1 * p.2) p.1 :=
      sum_divisors_up_to_eq_sum_positiveFactorPairs f
    _ = ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 (X / a),
          f (a * b) a := by
      exact Finset.sum_finset_product' (f := fun a b ↦ f (a * b) a)
        (positiveFactorPairs X) (Finset.Icc 1 X)
        (fun a ↦ Finset.Icc 1 (X / a))
        mem_positiveFactorPairs_quadratic

private theorem zetaMul_cutoff_eq_nested_quadratic
    {q X : ℕ} (chi : DirichletCharacter ℂ q) (w : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 X, chi.zetaMul n * w n) =
      ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 (X / a),
        chi (a : ZMod q) * w (a * b) := by
  have hz : (∑ n ∈ Finset.Icc 1 X, chi.zetaMul n * w n) =
      ∑ n ∈ Finset.Icc 1 X,
        (∑ d ∈ n.divisors, chi (d : ZMod q)) * w n := by
    apply Finset.sum_congr rfl
    intro n hn
    congr 1
    rw [DirichletCharacter.zetaMul,
      ArithmeticFunction.coe_zeta_mul_apply]
    apply Finset.sum_congr rfl
    intro d hd
    simp only [toArithmeticFunction, ArithmeticFunction.coe_mk,
      if_neg (Nat.pos_of_mem_divisors hd).ne']
  rw [hz]
  simp_rw [Finset.sum_mul]
  rw [sum_divisors_cutoff_eq_nested_quadratic]

/-- The direct fractional-part remainder before the finite integral swap. -/
noncomputable def quadraticZetaDirectEulerRemainder
    {q : ℕ} (chi : DirichletCharacter ℂ q) (X : ℕ) : ℂ :=
  (1 / (X : ℂ)) *
    ∑ a ∈ Finset.Icc 1 X,
      (a : ℂ) * chi (a : ZMod q) *
        (∫ t : ℝ in Set.Ioc 0 ((X : ℝ) / (a : ℝ)),
          ((Int.fract t : ℝ) : ℂ))

/-- The smoothed quadratic convolution equals its direct Euler expansion. -/
theorem quadraticZetaLinearSmoothedSum_eq_directEulerRemainder
    {q X : ℕ} (chi : DirichletCharacter ℂ q) (hX : 0 < X) :
    quadraticZetaLinearSmoothedSum chi X =
      ((X : ℂ) / 2) *
        (∑ a ∈ Finset.Icc 1 X,
          chi (a : ZMod q) / (a : ℂ)) -
      quadraticZetaDirectEulerRemainder chi X := by
  let weight : ℕ → ℂ := fun n ↦
    ((1 - (n : ℝ) / (X : ℝ) : ℝ) : ℂ)
  have hXreal : (0 : ℝ) < X := by exact_mod_cast hX
  have hinner : ∀ a ∈ Finset.Icc 1 X,
      (∑ b ∈ Finset.Icc 1 (X / a), weight (a * b)) =
        (X : ℂ) / (2 * (a : ℂ)) -
          ((a : ℂ) / (X : ℂ)) *
            (∫ t : ℝ in Set.Ioc 0 ((X : ℝ) / (a : ℝ)),
              ((Int.fract t : ℝ) : ℂ)) := by
    intro a ha
    have haPos : 0 < a := (Finset.mem_Icc.mp ha).1
    have haReal : (0 : ℝ) < a := by exact_mod_cast haPos
    let u : ℝ := (X : ℝ) / (a : ℝ)
    have hu : 0 < u := div_pos hXreal haReal
    have heuler := sum_linear_cutoff_eq_half_sub_fractIntegral hu
    have hfloor : ⌊u⌋₊ = X / a := by
      simpa [u] using (Nat.floor_div_eq_div (K := ℝ) X a)
    rw [hfloor] at heuler
    have hweight : ∀ b : ℕ,
        (1 - (a : ℝ) * (b : ℝ) / (X : ℝ)) =
          1 - (b : ℝ) / u := by
      intro b
      dsimp [u]
      field_simp [hXreal.ne', haReal.ne']
    have hreal :
        (∑ b ∈ Finset.Icc 1 (X / a),
          (1 - (a : ℝ) * (b : ℝ) / (X : ℝ))) =
          u / 2 - (1 / u) *
            (∫ t : ℝ in Set.Ioc 0 u, Int.fract t) := by
      rw [show (∑ b ∈ Finset.Icc 1 (X / a),
          (1 - (a : ℝ) * (b : ℝ) / (X : ℝ))) =
          ∑ b ∈ Finset.Icc 1 (X / a),
            (1 - (b : ℝ) / u) by
        apply Finset.sum_congr rfl
        intro b hb
        exact hweight b]
      exact heuler
    calc
      (∑ b ∈ Finset.Icc 1 (X / a), weight (a * b)) =
          (((∑ b ∈ Finset.Icc 1 (X / a),
            (1 - (a : ℝ) * (b : ℝ) / (X : ℝ))) : ℝ) : ℂ) := by
        rw [Complex.ofReal_sum]
        apply Finset.sum_congr rfl
        intro b hb
        simp [weight, Nat.cast_mul]
      _ = _ := by
        rw [hreal, Complex.ofReal_sub, Complex.ofReal_mul]
        rw [show ((∫ t : ℝ in Set.Ioc 0 u, Int.fract t : ℝ) : ℂ) =
            ∫ t : ℝ in Set.Ioc 0 u, ((Int.fract t : ℝ) : ℂ) by
          exact integral_ofReal.symm]
        dsimp [u]
        push_cast
        field_simp [hXreal.ne', haReal.ne']
  rw [quadraticZetaLinearSmoothedSum]
  change (∑ n ∈ Finset.Icc 1 X, chi.zetaMul n * weight n) = _
  rw [zetaMul_cutoff_eq_nested_quadratic]
  calc
    (∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 (X / a),
        chi (a : ZMod q) * weight (a * b)) =
        ∑ a ∈ Finset.Icc 1 X,
          chi (a : ZMod q) *
            ((X : ℂ) / (2 * (a : ℂ)) -
              ((a : ℂ) / (X : ℂ)) *
                (∫ t : ℝ in Set.Ioc 0 ((X : ℝ) / (a : ℝ)),
                  ((Int.fract t : ℝ) : ℂ))) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [← Finset.mul_sum, hinner a ha]
    _ = ∑ a ∈ Finset.Icc 1 X,
          (((X : ℂ) / 2) *
              (chi (a : ZMod q) / (a : ℂ)) -
            (1 / (X : ℂ)) *
              ((a : ℂ) * chi (a : ZMod q) *
                (∫ t : ℝ in Set.Ioc 0 ((X : ℝ) / (a : ℝ)),
                  ((Int.fract t : ℝ) : ℂ)))) := by
      apply Finset.sum_congr rfl
      intro a ha
      have haNe : (a : ℂ) ≠ 0 := by
        have haPos : 0 < a := lt_of_lt_of_le Nat.zero_lt_one
          (Finset.mem_Icc.mp ha).1
        exact_mod_cast haPos.ne'
      have hXne : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
      field_simp [haNe, hXne]
    _ = ((X : ℂ) / 2) *
          (∑ a ∈ Finset.Icc 1 X,
            chi (a : ZMod q) / (a : ℂ)) -
        quadraticZetaDirectEulerRemainder chi X := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
      unfold quadraticZetaDirectEulerRemainder
      rw [Finset.mul_sum]

end BoundedGaps.Maynard
