import BoundedGaps.Maynard.MaynardS2OuterMultiplicativeFunction
import BoundedGaps.Maynard.MaynardS2MainFactorDeviation

noncomputable section

/-!
# Finite singular-series tail for the S2 outer gamma

Maynard2013v3, source lines 552--560, applies the GGPY singular series to the
outer local gamma.  Its non-pre-sieved Euler factors differ from one by a
reciprocal-square correction, giving a uniform finite tail bound.
-/

namespace BoundedGaps.Maynard

noncomputable def maynardS2OuterSingularLocalFactor (p : ℕ) : ℝ :=
  (1 - maynardS2OuterGamma p / (p : ℝ))⁻¹ *
    (1 - 1 / (p : ℝ))

noncomputable def maynardS2OuterSingularCorrection (p : ℕ) : ℝ :=
  ((p : ℝ) ^ 2 - 3 * p + 1) /
    ((p : ℝ) ^ 3 * ((p : ℝ) - 2))

theorem maynardS2OuterSingularLocalFactor_prime_eq
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    maynardS2OuterSingularLocalFactor p =
      1 - maynardS2OuterSingularCorrection p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp3R : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hpm2 : 0 < (p : ℝ) - 2 := by nlinarith
  have hden : 0 < (p : ℝ) ^ 3 - (p : ℝ) ^ 2 - 2 * p + 1 := by
    nlinarith [sq_nonneg ((p : ℝ) - 2)]
  have hgammaDiv : maynardS2OuterGamma p / (p : ℝ) =
      ((p : ℝ) - 1) ^ 2 /
        ((p : ℝ) ^ 3 - (p : ℝ) ^ 2 - 2 * p + 1) := by
    rw [maynardS2OuterGamma_eq_fraction hden.ne']
    field_simp [hpR.ne']
  have honeSub : 1 - maynardS2OuterGamma p / (p : ℝ) =
      (p : ℝ) ^ 2 * ((p : ℝ) - 2) /
        ((p : ℝ) ^ 3 - (p : ℝ) ^ 2 - 2 * p + 1) := by
    rw [hgammaDiv]
    apply (eq_div_iff hden.ne').2
    rw [sub_mul, div_mul_cancel₀ _ hden.ne']
    ring
  have hprod : 0 < (p : ℝ) ^ 2 * ((p : ℝ) - 2) :=
    mul_pos (sq_pos_of_pos hpR) hpm2
  unfold maynardS2OuterSingularLocalFactor
    maynardS2OuterSingularCorrection
  rw [honeSub]
  field_simp [hpR.ne', hpm2.ne', hden.ne', hprod.ne']
  ring

theorem maynardS2OuterSingularCorrection_prime_bounds
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    0 ≤ maynardS2OuterSingularCorrection p ∧
      maynardS2OuterSingularCorrection p ≤ primeTotientSquareWeight p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp3R : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hpm1 : 0 < (p : ℝ) - 1 := by nlinarith
  have hpm2 : 0 < (p : ℝ) - 2 := by nlinarith
  have hnum : 0 < (p : ℝ) ^ 2 - 3 * p + 1 := by
    have hprod : 0 ≤ (p : ℝ) * ((p : ℝ) - 3) :=
      mul_nonneg hpR.le (sub_nonneg.mpr hp3R)
    nlinarith [hprod]
  have hden : 0 < (p : ℝ) ^ 3 * ((p : ℝ) - 2) :=
    mul_pos (pow_pos hpR 3) hpm2
  have hcorrLe : maynardS2OuterSingularCorrection p ≤
      (1 : ℝ) / (p : ℝ) ^ 2 := by
    unfold maynardS2OuterSingularCorrection
    apply (div_le_div_iff₀ hden (sq_pos_of_pos hpR)).2
    have hnumLe : (p : ℝ) ^ 2 - 3 * p + 1 ≤ p * (p - 2) := by
      nlinarith [hpR]
    have := mul_le_mul_of_nonneg_right hnumLe (sq_nonneg (p : ℝ))
    nlinarith
  constructor
  · unfold maynardS2OuterSingularCorrection
    positivity
  · calc
      maynardS2OuterSingularCorrection p ≤ (1 : ℝ) / (p : ℝ) ^ 2 := hcorrLe
      _ ≤ (1 : ℝ) / ((p : ℝ) - 1) ^ 2 := by
        apply div_le_div_of_nonneg_left zero_le_one (sq_pos_of_pos hpm1)
        nlinarith [sq_nonneg ((p : ℝ) - 1)]
      _ = primeTotientSquareWeight p := by
        unfold primeTotientSquareWeight
        rw [Nat.totient_prime hp, Nat.cast_sub hp.one_le]
        norm_num

noncomputable def maynardS2OuterSingularTail (D Q : ℕ) : ℝ :=
  ∏ p ∈ (Finset.Ico (D + 1) Q).filter Nat.Prime,
    maynardS2OuterSingularLocalFactor p

theorem abs_maynardS2OuterSingularTail_sub_one_le
    {D Q : ℕ} (hD : 2 ≤ D) :
    |maynardS2OuterSingularTail D Q - 1| ≤ 8 / (D : ℝ) := by
  let P := (Finset.Ico (D + 1) Q).filter Nat.Prime
  let c := maynardS2OuterSingularCorrection
  have hp3 {p : ℕ} (hp : p ∈ P) : 3 ≤ p := by
    have hpLower : D + 1 ≤ p :=
      (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1
    omega
  have hprime {p : ℕ} (hp : p ∈ P) : p.Prime :=
    (Finset.mem_filter.mp hp).2
  have hcorr0 (p : ℕ) (hp : p ∈ P) : 0 ≤ c p :=
    (maynardS2OuterSingularCorrection_prime_bounds
      (hprime hp) (hp3 hp)).1
  have hcorr1 (p : ℕ) (hp : p ∈ P) : c p ≤ 1 := by
    have hle := (maynardS2OuterSingularCorrection_prime_bounds
      (hprime hp) (hp3 hp)).2
    have hphiPos : (0 : ℝ) < Nat.totient p := by
      exact_mod_cast Nat.totient_pos.mpr (hprime hp).pos
    have hphiOne : (1 : ℝ) ≤ Nat.totient p := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (Nat.totient_pos.mpr (hprime hp).pos)))
    have hweight : primeTotientSquareWeight p ≤ 1 := by
      unfold primeTotientSquareWeight
      apply (div_le_one (sq_pos_of_pos hphiPos)).2
      nlinarith
    exact hle.trans hweight
  have hfactor : maynardS2OuterSingularTail D Q =
      ∏ p ∈ P, (1 - c p) := by
    unfold maynardS2OuterSingularTail P c
    apply Finset.prod_congr rfl
    intro p hp
    exact maynardS2OuterSingularLocalFactor_prime_eq
      (Finset.mem_filter.mp hp).2 (by
        have hpLower := (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1
        omega)
  have hdev := one_sub_prod_one_sub_nonneg_le_sum P c hcorr0 hcorr1
  have hprodNonneg : 0 ≤ ∏ p ∈ P, (1 - c p) := by
    apply Finset.prod_nonneg
    intro p hp
    exact sub_nonneg.mpr (hcorr1 p hp)
  have hprodLe : (∏ p ∈ P, (1 - c p)) ≤ 1 := by
    linarith [hdev.1]
  rw [hfactor, abs_of_nonpos (sub_nonpos.mpr hprodLe), neg_sub]
  calc
    1 - ∏ p ∈ P, (1 - c p) ≤ ∑ p ∈ P, c p := hdev.2
    _ ≤ ∑ p ∈ P, primeTotientSquareWeight p := by
      apply Finset.sum_le_sum
      intro p hp
      exact (maynardS2OuterSingularCorrection_prime_bounds
        (hprime hp) (hp3 hp)).2
    _ = primeTotientSquareTail D Q := by rfl
    _ ≤ 8 / (D : ℝ) := primeTotientSquareTail_le (by omega)

end BoundedGaps.Maynard
