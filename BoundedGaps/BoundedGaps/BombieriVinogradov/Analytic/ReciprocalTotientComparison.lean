import BoundedGaps.BombieriVinogradov.Analytic.ProductRoughnessRelaxation

/-!
# Reciprocal-totient comparison

This file applies totient supermultiplicativity to the exact multiplier range
from Akbary--Hambrook2013v2, Section 7, p. 25. The reciprocal-totient prefix
estimate, its explicit constant, and the later logarithmic bounds are separate.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable section

noncomputable local instance roughModulusAboveDecidableForTotientComparison
    (Q1 : ℝ) : DecidablePred (roughModulusAbove Q1) :=
  Classical.decPred _

/-- Reciprocal Euler totients are submultiplicative on positive natural numbers. -/
theorem inv_totient_mul_le_mul_inv_totient
    {d k : ℕ} (hd : 0 < d) (hk : 0 < k) :
    ((d * k).totient : ℝ)⁻¹ ≤
      (d.totient : ℝ)⁻¹ * (k.totient : ℝ)⁻¹ := by
  have hdphi : 0 < (d.totient : ℝ) := by
    exact_mod_cast (Nat.totient_pos.mpr hd)
  have hkphi : 0 < (k.totient : ℝ) := by
    exact_mod_cast (Nat.totient_pos.mpr hk)
  have htotient :
      (d.totient : ℝ) * (k.totient : ℝ) ≤
        ((d * k).totient : ℝ) := by
    exact_mod_cast Nat.totient_super_multiplicative d k
  have hinv :
      ((d * k).totient : ℝ)⁻¹ ≤
        ((d.totient : ℝ) * (k.totient : ℝ))⁻¹ :=
    inv_anti₀ (mul_pos hdphi hkphi) htotient
  simpa only [mul_inv] using hinv

/-- Sum the reciprocal-totient comparison over positive multipliers. -/
theorem sum_inv_totient_mul_le_inv_totient_mul_sum
    (Q d : ℕ) (hd : 0 < d) :
    (∑ k ∈ Finset.Ioc 0 (Q / d),
      ((d * k).totient : ℝ)⁻¹) ≤
      (d.totient : ℝ)⁻¹ *
        ∑ k ∈ Finset.Ioc 0 (Q / d),
          (k.totient : ℝ)⁻¹ := by
  calc
    _ ≤ ∑ k ∈ Finset.Ioc 0 (Q / d),
        (d.totient : ℝ)⁻¹ * (k.totient : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro k hk
      exact inv_totient_mul_le_mul_inv_totient hd
        (Finset.mem_Ioc.mp hk).1
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- Factor the conductor totient out of the rough-conductor multiplier sum. -/
theorem sum_conductorRough_multipliers_le_sum_factoredInvTotient
    (x Q : ℕ) (Q1 : ℝ) :
    (∑ d ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 d,
      (∑ ψ : primitiveCharacters d,
        primitiveCenteredEndpointMaximum x d ψ) *
        ∑ k ∈ Finset.Ioc 0 (Q / d),
          ((d * k).totient : ℝ)⁻¹) ≤
      ∑ d ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 d,
        (∑ ψ : primitiveCharacters d,
          primitiveCenteredEndpointMaximum x d ψ) *
          ((d.totient : ℝ)⁻¹ *
            ∑ k ∈ Finset.Ioc 0 (Q / d),
              (k.totient : ℝ)⁻¹) := by
  apply Finset.sum_le_sum
  intro d hdmem
  apply mul_le_mul_of_nonneg_left
  · exact sum_inv_totient_mul_le_inv_totient_mul_sum Q d
      (Finset.mem_Ioc.mp (Finset.mem_filter.mp hdmem).1).1
  · exact sum_primitiveCenteredEndpointMaximum_nonneg x d

/-- Pass from the product-rough factor-pair sum to factored reciprocal totients. -/
theorem sum_productRough_factorPairs_le_sum_factoredInvTotient
    (x Q : ℕ) (Q1 : ℝ) :
    (∑ p ∈ (positiveFactorPairs Q).filter (fun p ↦
        roughModulusAbove Q1 (p.1 * p.2) ∧ p.1 ≠ 1),
      ((p.1 * p.2).totient : ℝ)⁻¹ *
        ∑ ψ : primitiveCharacters p.1,
          primitiveCenteredEndpointMaximum x p.1 ψ) ≤
      ∑ d ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 d,
        (∑ ψ : primitiveCharacters d,
          primitiveCenteredEndpointMaximum x d ψ) *
          ((d.totient : ℝ)⁻¹ *
            ∑ k ∈ Finset.Ioc 0 (Q / d),
              (k.totient : ℝ)⁻¹) := by
  exact (sum_productRough_factorPairs_le_sum_conductorRough_multipliers
    x Q Q1).trans
      (sum_conductorRough_multipliers_le_sum_factoredInvTotient x Q Q1)

end

end BoundedGaps.Maynard
