import BoundedGaps.BombieriVinogradov.Analytic.WeightedConductorReindex

/-!
# Product-roughness relaxation

This file isolates the first inequality after the exact conductor reindex on
Akbary--Hambrook2013v2, Section 7, p. 25. It enlarges the product roughness
support to rough conductors and then regroups the finite pair sum by conductor.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable section

noncomputable local instance roughModulusAboveDecidableForRelaxation
    (Q1 : ℝ) : DecidablePred (roughModulusAbove Q1) :=
  Classical.decPred _

/-- Product roughness implies conductor roughness when the conductor is
nontrivial. -/
theorem roughModulusAbove_of_dvd
    {Q1 : ℝ} {d q : ℕ} (hd : 1 < d) (hdq : d ∣ q)
    (hq : roughModulusAbove Q1 q) :
    roughModulusAbove Q1 d := by
  rcases hq with ⟨hqgt, hqmin⟩
  refine ⟨hd, hqmin.trans_le ?_⟩
  have hprime : Nat.Prime d.minFac := Nat.minFac_prime (by omega)
  have hdiv : d.minFac ∣ q := (Nat.minFac_dvd d).trans hdq
  exact_mod_cast Nat.minFac_le_of_dvd hprime.two_le hdiv

/-- Primitive centered endpoint mass is nonnegative at every level. -/
theorem sum_primitiveCenteredEndpointMaximum_nonneg (x d : ℕ) :
    0 ≤ ∑ ψ : primitiveCharacters d,
      primitiveCenteredEndpointMaximum x d ψ := by
  apply Finset.sum_nonneg
  intro ψ hψ
  unfold primitiveCenteredEndpointMaximum
  split_ifs with hx
  · exact (norm_nonneg _).trans (Finset.le_sup'
      (fun y ↦ ‖centeredTwistedChebyshevSum y d ψ.1‖)
      (weightedEndpointRange_nonempty hx).choose_spec)
  · rfl

/-- Enlarging product roughness to conductor roughness increases the
nonnegative finite pair sum. -/
theorem sum_productRough_factorPairs_le_sum_conductorRough_factorPairs
    (x Q : ℕ) (Q1 : ℝ) :
    (∑ p ∈ (positiveFactorPairs Q).filter (fun p ↦
        roughModulusAbove Q1 (p.1 * p.2) ∧ p.1 ≠ 1),
      ((p.1 * p.2).totient : ℝ)⁻¹ *
        ∑ ψ : primitiveCharacters p.1,
          primitiveCenteredEndpointMaximum x p.1 ψ) ≤
      ∑ p ∈ (positiveFactorPairs Q).filter (fun p ↦
          roughModulusAbove Q1 p.1),
        ((p.1 * p.2).totient : ℝ)⁻¹ *
          ∑ ψ : primitiveCharacters p.1,
            primitiveCenteredEndpointMaximum x p.1 ψ := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpairs, hrough, hdne⟩
    have hpairmem := Finset.mem_filter.mp hpairs
    have hprodmem := Finset.mem_product.mp hpairmem.1
    have hdpos : 0 < p.1 := (Finset.mem_Ioc.mp hprodmem.1).1
    have hdgt : 1 < p.1 :=
      Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hdpos.ne', hdne⟩
    exact Finset.mem_filter.mpr ⟨hpairs,
      roughModulusAbove_of_dvd hdgt (Nat.dvd_mul_right p.1 p.2) hrough⟩
  · intro p hp hnot
    apply mul_nonneg
    · exact inv_nonneg.mpr (by positivity)
    · exact sum_primitiveCenteredEndpointMaximum_nonneg x p.1

/-- Regroup the conductor-rough pair sum as a conductor sum followed by the
positive multiplier range `k <= Q / d`. -/
theorem sum_conductorRough_factorPairs_eq_sum_multipliers
    (x Q : ℕ) (Q1 : ℝ) :
    (∑ p ∈ (positiveFactorPairs Q).filter (fun p ↦
        roughModulusAbove Q1 p.1),
      ((p.1 * p.2).totient : ℝ)⁻¹ *
        ∑ ψ : primitiveCharacters p.1,
          primitiveCenteredEndpointMaximum x p.1 ψ) =
      ∑ d ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 d,
        (∑ ψ : primitiveCharacters d,
          primitiveCenteredEndpointMaximum x d ψ) *
          ∑ k ∈ Finset.Ioc 0 (Q / d),
            ((d * k).totient : ℝ)⁻¹ := by
  let S : Finset (ℕ × ℕ) :=
    (positiveFactorPairs Q).filter (fun p ↦ roughModulusAbove Q1 p.1)
  let T : Finset ((d : ℕ) × ℕ) :=
    Finset.sigma ((Finset.Ioc 0 Q).filter (roughModulusAbove Q1))
      (fun d ↦ Finset.Ioc 0 (Q / d))
  let F : ℕ × ℕ → ℝ := fun p ↦
    ((p.1 * p.2).totient : ℝ)⁻¹ *
      ∑ ψ : primitiveCharacters p.1,
        primitiveCenteredEndpointMaximum x p.1 ψ
  have hbij :
      (∑ p ∈ S, F p) =
        ∑ z ∈ T, F (z.1, z.2) := by
    apply Finset.sum_bij (fun p hp ↦ ⟨p.1, p.2⟩)
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpairs, hrough⟩
      rcases Finset.mem_filter.mp hpairs with ⟨hprodmem, hprod⟩
      rcases Finset.mem_product.mp hprodmem with ⟨hdmem, hkmem⟩
      have hdpos : 0 < p.1 := (Finset.mem_Ioc.mp hdmem).1
      have hkdiv : p.2 ≤ Q / p.1 := by
        apply (Nat.le_div_iff_mul_le hdpos).2
        simpa [Nat.mul_comm] using hprod
      exact Finset.mem_sigma.mpr ⟨
        Finset.mem_filter.mpr ⟨hdmem, hrough⟩,
        Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hkmem).1, hkdiv⟩⟩
    · intro p hp p' hp' heq
      apply Prod.ext
      · exact congrArg Sigma.fst heq
      · exact congrArg Sigma.snd heq
    · intro z hz
      rcases z with ⟨d, k⟩
      rcases Finset.mem_sigma.mp hz with ⟨hdmemRough, hkmem⟩
      have hdmem : d ∈ Finset.Ioc 0 Q :=
        (Finset.mem_filter.mp hdmemRough).1
      have hrough : roughModulusAbove Q1 d :=
        (Finset.mem_filter.mp hdmemRough).2
      have hdpos : 0 < d := (Finset.mem_Ioc.mp hdmem).1
      have hkpos : 0 < k := (Finset.mem_Ioc.mp hkmem).1
      have hprod : d * k ≤ Q := by
        have h := (Nat.le_div_iff_mul_le hdpos).1
          (Finset.mem_Ioc.mp hkmem).2
        simpa [Nat.mul_comm] using h
      have hkQ : k ≤ Q :=
        (Finset.mem_Ioc.mp hkmem).2.trans (Nat.div_le_self Q d)
      have hpairs : (d, k) ∈ positiveFactorPairs Q := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_product.mpr ⟨hdmem,
          Finset.mem_Ioc.mpr ⟨hkpos, hkQ⟩⟩, hprod⟩
      refine ⟨(d, k), Finset.mem_filter.mpr ⟨hpairs, hrough⟩, ?_⟩
      rfl
    · intro p hp
      rfl
  have hsum := Finset.sum_sigma'
    ((Finset.Ioc 0 Q).filter (roughModulusAbove Q1))
    (fun d ↦ Finset.Ioc 0 (Q / d)) (fun d k ↦ F (d, k))
  calc
    _ = ∑ d ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 d,
        ∑ k ∈ Finset.Ioc 0 (Q / d),
          ((d * k).totient : ℝ)⁻¹ *
            ∑ ψ : primitiveCharacters d,
              primitiveCenteredEndpointMaximum x d ψ := by
      simpa [S, T, F] using hbij.trans hsum.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [mul_comm]

/-- Compose support relaxation with the exact conductor/multiplier regrouping. -/
theorem sum_productRough_factorPairs_le_sum_conductorRough_multipliers
    (x Q : ℕ) (Q1 : ℝ) :
    (∑ p ∈ (positiveFactorPairs Q).filter (fun p ↦
        roughModulusAbove Q1 (p.1 * p.2) ∧ p.1 ≠ 1),
      ((p.1 * p.2).totient : ℝ)⁻¹ *
        ∑ ψ : primitiveCharacters p.1,
          primitiveCenteredEndpointMaximum x p.1 ψ) ≤
      ∑ d ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 d,
        (∑ ψ : primitiveCharacters d,
          primitiveCenteredEndpointMaximum x d ψ) *
          ∑ k ∈ Finset.Ioc 0 (Q / d),
            ((d * k).totient : ℝ)⁻¹ := by
  exact (sum_productRough_factorPairs_le_sum_conductorRough_factorPairs
    x Q Q1).trans_eq
      (sum_conductorRough_factorPairs_eq_sum_multipliers x Q Q1)

end

end BoundedGaps.Maynard
