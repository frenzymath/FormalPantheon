import BoundedGaps.Maynard.MaynardS2OuterSingularFactorization

noncomputable section

/-!
# Quantitative finite outer singular-density approximation

Maynard2013v3, source lines 552--560, replaces the outer singular density by
the primorial pre-sieve density up to an `O(1/D)` factor.  The exact finite
version follows from SEM-256 and SEM-258.
-/

namespace BoundedGaps.Maynard

noncomputable def maynardS2OuterFiniteSingularSeries (D Q : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesLE Q, maynardS2OuterModularSingularFactor D p

theorem maynardS2OuterFiniteSingularSeries_eq
    {D Q : ℕ} (hDQ : D ≤ Q) :
    maynardS2OuterFiniteSingularSeries D Q =
      preSieveSingularSeries D *
        maynardS2OuterSingularTail D (Q + 1) := by
  exact maynardS2OuterModularSingularFactorization hDQ

theorem preSieveSingularSeries_pos_from_totient (D : ℕ) :
    0 < preSieveSingularSeries D := by
  rw [preSieveSingularSeries_eq_totient_div]
  exact div_pos
    (by exact_mod_cast Nat.totient_pos.mpr (primorial_pos D))
    (by exact_mod_cast primorial_pos D)

theorem abs_maynardS2OuterFiniteSingularSeries_sub_preSieve_le
    {D Q : ℕ} (hD : 2 ≤ D) (hDQ : D ≤ Q) :
    |maynardS2OuterFiniteSingularSeries D Q -
        preSieveSingularSeries D| ≤
      preSieveSingularSeries D * (8 / (D : ℝ)) := by
  rw [maynardS2OuterFiniteSingularSeries_eq hDQ]
  have hS : 0 ≤ preSieveSingularSeries D :=
    (preSieveSingularSeries_pos_from_totient D).le
  rw [show preSieveSingularSeries D *
      maynardS2OuterSingularTail D (Q + 1) -
        preSieveSingularSeries D =
      preSieveSingularSeries D *
        (maynardS2OuterSingularTail D (Q + 1) - 1) by ring,
    abs_mul, abs_of_nonneg hS]
  exact mul_le_mul_of_nonneg_left
    (abs_maynardS2OuterSingularTail_sub_one_le hD) hS

theorem abs_maynardS2OuterFiniteSingularSeries_div_preSieve_sub_one_le
    {D Q : ℕ} (hD : 2 ≤ D) (hDQ : D ≤ Q) :
    |maynardS2OuterFiniteSingularSeries D Q /
        preSieveSingularSeries D - 1| ≤ 8 / (D : ℝ) := by
  rw [maynardS2OuterFiniteSingularSeries_eq hDQ]
  have hS := preSieveSingularSeries_pos_from_totient D
  rw [mul_div_cancel_left₀ _ hS.ne']
  exact abs_maynardS2OuterSingularTail_sub_one_le hD

end BoundedGaps.Maynard
