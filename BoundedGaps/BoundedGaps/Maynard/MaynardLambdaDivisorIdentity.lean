import BoundedGaps.Arithmetic.ReciprocalTotientPrefix
import BoundedGaps.Maynard.MaynardLambdaCoefficientMajorant

noncomputable section

/-!
# A coprime reciprocal-totient divisor expansion

The shared arithmetic layer proves the squarefree identity used in
Maynard2013v3, equation `eq:LambdaSize` (source lines 304--316). This file
derives its coprime two-variable specialization.
-/

namespace BoundedGaps.Maynard

open scoped ArithmeticFunction.omega BigOperators

theorem squarefree_coprime_tau_div_totient_expansion
    {k D t : ℕ} (hD : Squarefree D) (ht : Squarefree t)
    (hcop : Nat.Coprime D t) :
    ((k ^ ω t : ℕ) : ℝ) *
        ((D : ℝ) / (Nat.totient (D * t) : ℝ)) =
      ∑ a ∈ D.divisors,
        ((k ^ ω t : ℕ) : ℝ) / (Nat.totient (a * t) : ℝ) := by
  classical
  have hphiD0 : (Nat.totient D : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hD.ne_zero)))
  have hphiT0 : (Nat.totient t : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.totient_pos.mpr (Nat.pos_of_ne_zero ht.ne_zero)))
  calc
    ((k ^ ω t : ℕ) : ℝ) *
          ((D : ℝ) / (Nat.totient (D * t) : ℝ)) =
        ((k ^ ω t : ℕ) : ℝ) *
          (((D : ℝ) / (Nat.totient D : ℝ)) *
            (Nat.totient t : ℝ)⁻¹) := by
      rw [Nat.totient_mul hcop]
      push_cast
      field_simp
    _ = ((k ^ ω t : ℕ) : ℝ) *
          ((∑ a ∈ D.divisors, (Nat.totient a : ℝ)⁻¹) *
            (Nat.totient t : ℝ)⁻¹) := by
      rw [squarefree_div_totient_eq_sum_divisors_inv_totient hD]
    _ = ∑ a ∈ D.divisors,
          ((k ^ ω t : ℕ) : ℝ) *
            ((Nat.totient a : ℝ)⁻¹ * (Nat.totient t : ℝ)⁻¹) := by
      rw [← mul_assoc, Finset.mul_sum, Finset.sum_mul]
      simp [mul_assoc]
    _ = ∑ a ∈ D.divisors,
          ((k ^ ω t : ℕ) : ℝ) / (Nat.totient (a * t) : ℝ) := by
      apply Finset.sum_congr rfl
      intro a ha
      have hacop : Nat.Coprime a t := hcop.of_dvd_left (Nat.dvd_of_mem_divisors ha)
      have hphi : (Nat.totient (a * t) : ℝ) =
          (Nat.totient a : ℝ) * (Nat.totient t : ℝ) := by
        exact_mod_cast Nat.totient_mul hacop
      rw [hphi]
      field_simp

end BoundedGaps.Maynard
