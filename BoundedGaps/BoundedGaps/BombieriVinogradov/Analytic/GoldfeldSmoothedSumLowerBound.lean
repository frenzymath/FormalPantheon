import BoundedGaps.BombieriVinogradov.Analytic.GoldfeldSmoothedSum

/-!
# Goldfeld's smoothed-sum lower bound

This file proves the elementary positivity step in Koukoulopoulos Theorem
12.9, printed p. 126.  The cutoff makes the sum finite, every summand is
nonnegative, and the summand at one is exactly one.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, Theorem 12.9, printed
p. 126.

Semantic review: `SEM-554`.
-/

noncomputable section

open scoped ComplexOrder

namespace BoundedGaps.Maynard

private theorem goldfeldSmoothedSummand_nonneg
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (hsquare1 : chi1 ^ 2 = 1) (hsquare : chi ^ 2 = 1)
    (beta x : ℝ) (n : ℕ) :
    0 ≤ goldfeldBetaCoefficient chi1 chi beta n *
      (goldfeldPlateau ((n : ℝ) / x) : ℂ) := by
  apply mul_nonneg
  · simpa [goldfeldBetaCoefficient] using
      LSeries.term_nonneg
        (goldfeldCoefficient_nonneg chi1 chi hsquare1 hsquare n) beta
  · exact (RCLike.ofReal_nonneg (K := ℂ)).2
      (goldfeldPlateau_nonneg _)

private theorem goldfeldSmoothedSummand_summable
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (beta : ℝ) {x : ℝ} (hx : 0 < x) :
    Summable fun n : ℕ =>
      goldfeldBetaCoefficient chi1 chi beta n *
        (goldfeldPlateau ((n : ℝ) / x) : ℂ) := by
  apply summable_of_ne_finset_zero
    (s := Finset.range (Nat.ceil (2 * x)))
  intro n hn
  have hnceil : Nat.ceil (2 * x) ≤ n := by
    simpa only [Finset.mem_range, not_lt] using hn
  have hcutoff : 2 * x ≤ (n : ℝ) := by
    calc
      2 * x ≤ (Nat.ceil (2 * x) : ℕ) := Nat.le_ceil _
      _ ≤ n := by exact_mod_cast hnceil
  have hratio : 2 ≤ (n : ℝ) / x :=
    (le_div_iff₀ hx).2 hcutoff
  rw [goldfeldPlateau_eq_zero hratio]
  simp

/-- The source auxiliary sum is at least its `n = 1` summand. -/
theorem one_le_goldfeldSmoothedSum
    {q1 q : ℕ} [NeZero q1] [NeZero q]
    (chi1 : DirichletCharacter ℂ q1)
    (chi : DirichletCharacter ℂ q)
    (hsquare1 : chi1 ^ 2 = 1) (hsquare : chi ^ 2 = 1)
    {beta x : ℝ} (hx : 1 ≤ x) :
    (1 : ℂ) ≤ goldfeldSmoothedSum chi1 chi beta x := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hsummable :=
    goldfeldSmoothedSummand_summable chi1 chi beta hxpos
  rw [goldfeldSmoothedSum]
  calc
    (1 : ℂ) = goldfeldBetaCoefficient chi1 chi beta 1 *
        (goldfeldPlateau ((1 : ℝ) / x) : ℂ) := by
      rw [goldfeldBetaCoefficient,
        LSeries.term_of_ne_zero one_ne_zero, goldfeldCoefficient_one]
      have hplateau : goldfeldPlateau ((1 : ℝ) / x) = 1 :=
        goldfeldPlateau_eq_one
          (div_nonneg zero_le_one hxpos.le)
          ((div_le_one hxpos).2 hx)
      rw [hplateau]
      norm_num
    _ ≤ ∑' n : ℕ,
        goldfeldBetaCoefficient chi1 chi beta n *
          (goldfeldPlateau ((n : ℝ) / x) : ℂ) := by
      simpa using hsummable.sum_le_tsum {1} fun n _ =>
        goldfeldSmoothedSummand_nonneg
          chi1 chi hsquare1 hsquare beta x n

end BoundedGaps.Maynard
