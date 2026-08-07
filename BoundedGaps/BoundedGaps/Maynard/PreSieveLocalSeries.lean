import BoundedGaps.Maynard.PreSievedPrimeMertens
import Mathlib.Data.Nat.Totient

noncomputable section

/-!
# Pre-sieve local density and singular series

This evaluates the two finite arithmetic ingredients in the concrete
specialization of Maynard's weighted summation lemma.
-/

namespace BoundedGaps.Maynard

open Finset Nat Real

noncomputable def preSieveGamma (D p : ℕ) : ℝ :=
  if p ∣ primorial D then 0 else 1

theorem preSieveGamma_prime_bounds (D : ℕ) {p : ℕ} (hp : p.Prime) :
    0 ≤ preSieveGamma D p / (p : ℝ) ∧
      preSieveGamma D p / (p : ℝ) ≤ 1 - (1 / 2 : ℝ) := by
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  constructor
  · unfold preSieveGamma
    split_ifs <;> positivity
  · unfold preSieveGamma
    by_cases hdvd : p ∣ primorial D
    · simp [hdvd]
      norm_num
    · rw [if_neg hdvd]
      have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      have h := one_div_le_one_div_of_le
        (show (0 : ℝ) < 2 by norm_num) hpTwo
      norm_num at h ⊢
      exact h

noncomputable def preSieveSingularSeries (D : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesLE D, (1 - (1 : ℝ) / p)

theorem preSieveSingularSeries_eq_totient_div (D : ℕ) :
    preSieveSingularSeries D =
      (Nat.totient (primorial D) : ℝ) / primorial D := by
  have hQ := Nat.totient_eq_mul_prod_factors (primorial D)
  rw [primeFactors_primorial] at hQ
  have hR : (Nat.totient (primorial D) : ℝ) =
      (primorial D : ℝ) *
        ∏ p ∈ Nat.primesLE D, (1 - (p : ℝ)⁻¹) := by
    have hR0 := congrArg (fun x : ℚ => (x : ℝ)) hQ
    push_cast at hR0
    exact hR0
  unfold preSieveSingularSeries
  have hW : (primorial D : ℝ) ≠ 0 := by
    exact_mod_cast primorial_ne_zero D
  apply (eq_div_iff hW).2
  simp only [one_div]
  rw [hR]
  ring

end BoundedGaps.Maynard
