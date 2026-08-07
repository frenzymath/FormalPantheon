import BoundedGaps.Maynard.ConcreteRoughModulusPrimeLogMass
import BoundedGaps.Maynard.PreSieveLocalSeries

noncomputable section

/-!
# Local density for an augmented pre-sieve

This evaluates the local gamma weight and singular series after adjoining the
varying S2 off-coordinate product to the primorial modulus.
-/

namespace BoundedGaps.Maynard

open Finset Nat Real

noncomputable def augmentedPreSieveGamma (D P p : ℕ) : ℝ :=
  if p ∣ primorial D * P then 0 else 1

noncomputable def augmentedPreSieveSingularSeries (D P : ℕ) : ℝ :=
  ∏ p ∈ (primorial D * P).primeFactors, (1 - (1 : ℝ) / p)

theorem augmentedPreSieveGamma_prime_bounds
    (D P : ℕ) {p : ℕ} (hp : p.Prime) :
    0 ≤ augmentedPreSieveGamma D P p / (p : ℝ) ∧
      augmentedPreSieveGamma D P p / (p : ℝ) ≤ 1 - (1 / 2 : ℝ) := by
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  constructor
  · unfold augmentedPreSieveGamma
    split_ifs <;> positivity
  · unfold augmentedPreSieveGamma
    by_cases hdvd : p ∣ primorial D * P
    · simp [hdvd]
      norm_num
    · rw [if_neg hdvd]
      have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      have h := one_div_le_one_div_of_le
        (show (0 : ℝ) < 2 by norm_num) hpTwo
      norm_num at h ⊢
      exact h

theorem augmentedPreSieveGamma_prime_weight
    (D P : ℕ) {p : ℕ} (hp : p.Prime) :
    augmentedPreSieveGamma D P p /
        ((p : ℝ) - augmentedPreSieveGamma D P p) =
      if p ∣ primorial D * P then 0 else (1 : ℝ) / (p - 1 : ℕ) := by
  unfold augmentedPreSieveGamma
  by_cases hdvd : p ∣ primorial D * P
  · simp [hdvd]
  · rw [if_neg hdvd, if_neg hdvd]
    have hpOne : 1 ≤ p := hp.one_le
    rw [Nat.cast_sub hpOne]
    norm_num

theorem augmentedPreSieveSingularSeries_eq_totient_div
    {D P : ℕ} (hP : 0 < P) :
    augmentedPreSieveSingularSeries D P =
      (Nat.totient (primorial D * P) : ℝ) / (primorial D * P) := by
  have hM : 0 < primorial D * P := Nat.mul_pos (primorial_pos D) hP
  have hQ := Nat.totient_eq_mul_prod_factors (primorial D * P)
  have hR : (Nat.totient (primorial D * P) : ℝ) =
      (primorial D * P : ℝ) *
        ∏ p ∈ (primorial D * P).primeFactors,
          (1 - (p : ℝ)⁻¹) := by
    have hR0 := congrArg (fun x : ℚ => (x : ℝ)) hQ
    push_cast at hR0
    exact hR0
  unfold augmentedPreSieveSingularSeries
  have hMReal : (primorial D * P : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  apply (eq_div_iff hMReal).2
  simp only [one_div]
  rw [hR]
  ring

theorem augmentedPreSieveSingularSeries_eq_preSieve_mul
    {D P : ℕ} (hP : 0 < P) (hcop : Nat.Coprime (primorial D) P) :
    augmentedPreSieveSingularSeries D P =
      preSieveSingularSeries D * ((Nat.totient P : ℝ) / P) := by
  rw [augmentedPreSieveSingularSeries_eq_totient_div hP,
    preSieveSingularSeries_eq_totient_div, Nat.totient_mul hcop]
  have hW : (primorial D : ℝ) ≠ 0 := by exact_mod_cast primorial_ne_zero D
  have hPReal : (P : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
  push_cast
  field_simp [hW, hPReal]

end BoundedGaps.Maynard
