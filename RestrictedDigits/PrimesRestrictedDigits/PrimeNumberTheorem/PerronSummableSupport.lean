import PrimesRestrictedDigits.PrimeNumberTheorem.PerronOneTerm
import Mathlib.NumberTheory.LSeries.Basic

/-!
# Countable Perron sums and their support

This file fixes the positive-index convention and convergence facts needed to
lift `MONTGOMERY-VAUGHAN-MNT-I`, Corollary 5.3, p. 140, from finite sums to an
absolutely convergent L-series.
-/

namespace PrimesRestrictedDigits

/-- A starred Perron summand, with the source's positive-index convention. -/
noncomputable def perronStarredTerm
    (a : Nat -> Complex) (x : Real) (n : Nat) : Complex :=
  if n = 0 then 0 else (perronWeight x n : Complex) * a n

/-- The source's starred coefficient sum below a real cutoff. -/
noncomputable def starredPerronSum
    (a : Nat -> Complex) (x : Real) : Complex :=
  ∑' n, perronStarredTerm a x n

/-- A strict near-diagonal error summand, with index zero suppressed. -/
noncomputable def perronNearErrorTerm
    (a : Nat -> Complex) (x T : Real) (n : Nat) : Real :=
  if n = 0 then 0 else ‖a n‖ * perronNearError x T n

/-- The countable strict near-diagonal Perron error. -/
noncomputable def perronNearErrorSum
    (a : Nat -> Complex) (x T : Real) : Real :=
  ∑' n, perronNearErrorTerm a x T n

/-- A term of the absolute Dirichlet coefficient mass on a real line. -/
noncomputable def perronCoefficientMassTerm
    (a : Nat -> Complex) (sigma : Real) (n : Nat) : Real :=
  if n = 0 then 0 else ‖a n‖ / (n : Real) ^ sigma

/-- The absolute Dirichlet coefficient mass on a real line. -/
noncomputable def perronCoefficientMass
    (a : Nat -> Complex) (sigma : Real) : Real :=
  ∑' n, perronCoefficientMassTerm a sigma n

/-- A one-term Perron kernel contribution, with index zero suppressed. -/
noncomputable def perronKernelTerm
    (a : Nat -> Complex) (x sigma T : Real) (n : Nat) : Complex :=
  if n = 0 then 0 else a n * perronKernel (x / (n : Real)) sigma T

/-- The starred coefficient sequence has finite support. The extra endpoint in
the bound retains the half-weight term when the cutoff is a natural number. -/
theorem perronStarredTerm_hasFiniteSupport
    (a : Nat -> Complex) (x : Real) :
    Function.HasFiniteSupport (perronStarredTerm a x) := by
  apply (Set.finite_lt_nat (Nat.ceil x + 1)).subset
  intro n hn
  change perronStarredTerm a x n ≠ 0 at hn
  change n < Nat.ceil x + 1
  by_contra hnbound
  have hceil_lt_n : Nat.ceil x < n :=
    (Nat.lt_succ_self _).trans_le (Nat.le_of_not_gt hnbound)
  have hx_lt_n : x < (n : Real) :=
    lt_of_le_of_lt (Nat.le_ceil x) (by exact_mod_cast hceil_lt_n)
  apply hn
  simp [perronStarredTerm, perronWeight_eq_zero_of_lt hx_lt_n]

/-- The starred coefficient sequence is summable. -/
theorem summable_perronStarredTerm (a : Nat -> Complex) (x : Real) :
    Summable (perronStarredTerm a x) :=
  summable_of_hasFiniteSupport (perronStarredTerm_hasFiniteSupport a x)

/-- The strict near-diagonal error sequence has finite support. -/
theorem perronNearErrorTerm_hasFiniteSupport
    (a : Nat -> Complex) (x T : Real) :
    Function.HasFiniteSupport (perronNearErrorTerm a x T) := by
  apply (Set.finite_lt_nat (Nat.ceil (2 * x))).subset
  intro n hn
  change perronNearErrorTerm a x T n ≠ 0 at hn
  change n < Nat.ceil (2 * x)
  by_contra hnbound
  have hn_ge : Nat.ceil (2 * x) <= n := Nat.le_of_not_gt hnbound
  have hx_le_n : 2 * x <= (n : Real) :=
    le_trans (Nat.le_ceil (2 * x)) (by exact_mod_cast hn_ge)
  have hnearzero : perronNearError x T n = 0 := by
    rw [perronNearError, if_neg]
    intro h
    exact (not_lt_of_ge hx_le_n) h.2.1
  apply hn
  simp [perronNearErrorTerm, hnearzero]

/-- The strict near-diagonal error sequence is summable. -/
theorem summable_perronNearErrorTerm (a : Nat -> Complex) (x T : Real) :
    Summable (perronNearErrorTerm a x T) :=
  summable_of_hasFiniteSupport (perronNearErrorTerm_hasFiniteSupport a x T)

/-- The coefficient-mass term is exactly the norm of the corresponding
L-series term, including the source's omitted zeroth coefficient. -/
theorem perronCoefficientMassTerm_eq_norm_lSeriesTerm
    (a : Nat -> Complex) (sigma : Real) (n : Nat) :
    perronCoefficientMassTerm a sigma n =
      ‖LSeries.term a (sigma : Complex) n‖ := by
  rw [LSeries.norm_term_eq]
  simp [perronCoefficientMassTerm]

/-- Absolute convergence of an L-series makes its coefficient mass summable. -/
theorem LSeriesSummable.summable_perronCoefficientMassTerm
    {a : Nat -> Complex} {sigma : Real}
    (hsum : LSeriesSummable a (sigma : Complex)) :
    Summable (perronCoefficientMassTerm a sigma) := by
  exact hsum.norm.congr fun n => by
    rw [LSeries.norm_term_eq]
    simp [perronCoefficientMassTerm]

/-- Every near-diagonal error summand is nonnegative in the quantitative
Perron range. -/
theorem perronNearErrorTerm_nonneg
    {a : Nat -> Complex} {x T : Real} (hx : 0 < x) (hT : 0 < T)
    (n : Nat) : 0 <= perronNearErrorTerm a x T n := by
  rw [perronNearErrorTerm]
  split_ifs
  · exact le_rfl
  · apply mul_nonneg (norm_nonneg _)
    rw [perronNearError]
    split_ifs with h
    · apply le_min
      · norm_num
      · have hdiff : 0 < |x - (n : Real)| :=
          abs_pos.mpr (sub_ne_zero.mpr h.2.2)
        positivity
    · exact le_rfl

/-- Every absolute coefficient-mass summand is nonnegative. -/
theorem perronCoefficientMassTerm_nonneg
    {a : Nat -> Complex} {sigma : Real} (n : Nat) :
    0 <= perronCoefficientMassTerm a sigma n := by
  rw [perronCoefficientMassTerm]
  split_ifs
  · exact le_rfl
  · exact div_nonneg (norm_nonneg _)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)

end PrimesRestrictedDigits
