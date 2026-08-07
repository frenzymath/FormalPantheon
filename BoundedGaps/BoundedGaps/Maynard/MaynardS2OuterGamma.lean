import BoundedGaps.Maynard.MaynardS2GDivisorExpansion

noncomputable section

/-!
# Prime-local gamma for the S2 outer `g`-weighted mean

Maynard2013v3, source line 552, uses a second gamma in the outer divisor sum.
This file records the exact prime identity behind that choice.
-/

namespace BoundedGaps.Maynard

noncomputable def maynardS2OuterGamma (p : ℕ) : ℝ :=
  1 - ((p : ℝ) ^ 2 - 3 * p + 1) /
    ((p : ℝ) ^ 3 - (p : ℝ) ^ 2 - 2 * p + 1)

noncomputable def maynardS2OuterScalarWeight (p : ℕ) : ℝ :=
  (Nat.totient p : ℝ) ^ 2 /
    ((maynardS2G p : ℝ) * (p : ℝ) ^ 2)

theorem maynardS2OuterGamma_eq_fraction
    {p : ℕ}
    (hden : (p : ℝ) ^ 3 - (p : ℝ) ^ 2 - 2 * p + 1 ≠ 0) :
    maynardS2OuterGamma p =
      (p : ℝ) * ((p : ℝ) - 1) ^ 2 /
        ((p : ℝ) ^ 3 - (p : ℝ) ^ 2 - 2 * p + 1) := by
  apply (eq_div_iff hden).2
  unfold maynardS2OuterGamma
  rw [sub_mul, div_mul_cancel₀ _ hden]
  ring

theorem maynardS2OuterGamma_prime_bounds
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    0 ≤ maynardS2OuterGamma p / (p : ℝ) ∧
      maynardS2OuterGamma p / (p : ℝ) ≤ 1 - (1 / 2 : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp3R : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hden : 0 < (p : ℝ) ^ 3 - (p : ℝ) ^ 2 - 2 * p + 1 := by
    nlinarith [sq_nonneg ((p : ℝ) - 2)]
  rw [maynardS2OuterGamma_eq_fraction hden.ne']
  constructor
  · positivity
  · rw [div_le_iff₀ hpR]
    rw [div_le_iff₀ hden]
    norm_num
    have hcubic : 0 ≤ (p : ℝ) ^ 2 * ((p : ℝ) - 3) :=
      mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hp3R)
    nlinarith [hcubic]

theorem maynardS2OuterGamma_prime_weight
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    maynardS2OuterGamma p /
        ((p : ℝ) - maynardS2OuterGamma p) =
      maynardS2OuterScalarWeight p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp3R : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hp2 : 2 ≤ p := by omega
  have hpG : (maynardS2G p : ℝ) = p - 2 := by
    rw [maynardS2G_prime hp]
    norm_num [Nat.cast_sub hp2]
  have hpPhi : (Nat.totient p : ℝ) = p - 1 := by
    rw [Nat.totient_prime hp]
    norm_num [Nat.cast_sub hp.one_le]
  have hden : 0 < (p : ℝ) ^ 3 - (p : ℝ) ^ 2 - 2 * p + 1 := by
    nlinarith [sq_nonneg ((p : ℝ) - 2)]
  have hden' : 0 < (1 : ℝ) - p * 2 - p ^ 2 + p ^ 3 := by
    nlinarith [hden]
  have hgp : (0 : ℝ) < p - 2 := by nlinarith [hp3R]
  rw [maynardS2OuterGamma_eq_fraction hden.ne']
  have hdiff : (p : ℝ) -
      p * (p - 1) ^ 2 /
        (p ^ 3 - p ^ 2 - 2 * p + 1) =
      p ^ 3 * (p - 2) /
        (p ^ 3 - p ^ 2 - 2 * p + 1) := by
    apply (eq_div_iff hden.ne').2
    rw [sub_mul, div_mul_cancel₀ _ hden.ne']
    ring
  rw [hdiff]
  unfold maynardS2OuterScalarWeight
  rw [hpG, hpPhi]
  have hQ : (p : ℝ) * (p * (p - 1) - 2) + 1 ≠ 0 := by
    nlinarith [hden]
  field_simp [hden'.ne', hgp.ne', hpR.ne']

end BoundedGaps.Maynard
