import BoundedGaps.BombieriVinogradov.Analytic.CenteredProgressionCorrection

/-!
# All-modulus primitive-conductor split

This file reconstructs the exact finite conductor skeleton behind Vaughan's
weighted progression corollary. It reindexes every positive original modulus
as `q = d * k`, removes only the proved-zero centered conductor-one fiber, and
splits at an arbitrary natural conductor cutoff.

Sources: `Vaughan1980`, p. 113, and `AkbaryHambrook2013v2`, Section 7,
pp. 24--25. Semantic review: `SEM-463`.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable section

/-- Centered primitive-character mass with conductor at most `R`. -/
noncomputable def smallConductorCenteredMass
    (x Q R : ℕ) : ℝ :=
  ∑ p ∈ (positiveFactorPairs Q).filter (fun p ↦
      p.1 ≠ 1 ∧ p.1 ≤ R),
    ((p.1 * p.2).totient : ℝ)⁻¹ *
      ∑ ψ : primitiveCharacters p.1,
        primitiveCenteredEndpointMaximum x p.1 ψ

/-- Centered primitive-character mass with conductor strictly above `R`. -/
noncomputable def largeConductorCenteredMass
    (x Q R : ℕ) : ℝ :=
  ∑ p ∈ (positiveFactorPairs Q).filter (fun p ↦
      p.1 ≠ 1 ∧ R < p.1),
    ((p.1 * p.2).totient : ℝ)⁻¹ *
      ∑ ψ : primitiveCharacters p.1,
        primitiveCenteredEndpointMaximum x p.1 ψ

/-- Reindex the all-modulus inducing-character mass by positive
`(conductor, multiplier)` pairs, retaining the exact product-totient weight. -/
theorem sum_weightedInducingPrimitiveCenteredEndpointMaximum_eq_allFactorPairs
    (x Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q,
      (q.totient : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q,
          inducingPrimitiveCenteredEndpointMaximum x q χ) =
      ∑ p ∈ (positiveFactorPairs Q).filter (fun p ↦ p.1 ≠ 1),
        ((p.1 * p.2).totient : ℝ)⁻¹ *
          ∑ ψ : primitiveCharacters p.1,
            primitiveCenteredEndpointMaximum x p.1 ψ := by
  classical
  have hindex : Finset.Icc 1 Q = Finset.Ioc 0 Q := by
    ext q
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  let F : ∀ {q d : ℕ}, d ∣ q → primitiveCharacters d → ℝ :=
    fun {q d} _ ψ ↦
      (q.totient : ℝ)⁻¹ * primitiveCenteredEndpointMaximum x d ψ
  let G : ℕ × ℕ → ℝ := fun p ↦
    ((p.1 * p.2).totient : ℝ)⁻¹ *
      ∑ ψ : primitiveCharacters p.1,
        primitiveCenteredEndpointMaximum x p.1 ψ
  have hleft :
      (∑ q ∈ Finset.Icc 1 Q,
        (q.totient : ℝ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q,
            inducingPrimitiveCenteredEndpointMaximum x q χ) =
        ∑ q ∈ Finset.Ioc 0 Q,
          ∑ d : q.divisors,
            ∑ ψ : primitiveCharacters d.1,
              F (Nat.dvd_of_mem_divisors d.2) ψ := by
    rw [hindex]
    apply Finset.sum_congr rfl
    intro q hq
    have hqpos : 0 < q := (Finset.mem_Ioc.mp hq).1
    rw [sum_inducingPrimitiveCenteredEndpointMaximum_eq_divisors hqpos]
    rw [Finset.mul_sum]
    apply Fintype.sum_congr
    intro d
    rw [Finset.mul_sum]
  have hreindex :
      (∑ q ∈ Finset.Ioc 0 Q,
        ∑ d : q.divisors,
          ∑ ψ : primitiveCharacters d.1,
            F (Nat.dvd_of_mem_divisors d.2) ψ) =
        ∑ p ∈ positiveFactorPairs Q,
          ∑ ψ : primitiveCharacters p.1,
            F (Nat.dvd_mul_right p.1 p.2) ψ :=
    sum_primitive_conductors_up_to_eq_sum_positiveFactorPairs F
  have hright :
      (∑ p ∈ positiveFactorPairs Q,
        ∑ ψ : primitiveCharacters p.1,
          F (Nat.dvd_mul_right p.1 p.2) ψ) =
        ∑ p ∈ positiveFactorPairs Q, G p := by
    apply Finset.sum_congr rfl
    intro p hp
    change (∑ ψ : primitiveCharacters p.1,
      ((p.1 * p.2).totient : ℝ)⁻¹ *
        primitiveCenteredEndpointMaximum x p.1 ψ) = G p
    unfold G
    rw [Finset.mul_sum]
  have hzero : ∀ p ∈ positiveFactorPairs Q, p.1 = 1 → G p = 0 := by
    intro p hp hp1
    rcases p with ⟨d, k⟩
    simp only at hp1 ⊢
    subst d
    apply mul_eq_zero_of_right
    exact sum_primitiveCenteredEndpointMaximum_one x
  have hfilter :
      (∑ p ∈ (positiveFactorPairs Q).filter (fun p ↦ p.1 ≠ 1), G p) =
        ∑ p ∈ positiveFactorPairs Q, G p := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hnot
    have hp1 : p.1 = 1 := by
      by_contra hpne
      exact hnot (Finset.mem_filter.mpr ⟨hp, hpne⟩)
    exact hzero p hp hp1
  exact hleft.trans (hreindex.trans (hright.trans hfilter.symm))

/-- Split the all-modulus centered character mass exactly at conductor `R`. -/
theorem allModulusCenteredCharacterMass_eq_small_add_large
    (x Q R : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q,
      (q.totient : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q,
          inducingPrimitiveCenteredEndpointMaximum x q χ) =
      smallConductorCenteredMass x Q R +
        largeConductorCenteredMass x Q R := by
  classical
  rw [sum_weightedInducingPrimitiveCenteredEndpointMaximum_eq_allFactorPairs]
  unfold smallConductorCenteredMass largeConductorCenteredMass
  simpa only [Finset.filter_filter, not_le] using
    (Finset.sum_filter_add_sum_filter_not
      ((positiveFactorPairs Q).filter (fun p ↦ p.1 ≠ 1))
      (fun p ↦ p.1 ≤ R)
      (fun p ↦ ((p.1 * p.2).totient : ℝ)⁻¹ *
        ∑ ψ : primitiveCharacters p.1,
          primitiveCenteredEndpointMaximum x p.1 ψ)).symm

private theorem sum_allModuli_log_sq_le
    (x Q : ℕ) (hx : 2 ≤ x) :
    (∑ q ∈ Finset.Icc 1 Q,
      Real.log ((q * x : ℕ) : ℝ) ^ 2) ≤
      (Q : ℝ) * Real.log ((Q * x : ℕ) : ℝ) ^ 2 := by
  have hpoint : ∀ q ∈ Finset.Icc 1 Q,
      Real.log ((q * x : ℕ) : ℝ) ^ 2 ≤
        Real.log ((Q * x : ℕ) : ℝ) ^ 2 := by
    intro q hq
    have hqBounds := Finset.mem_Icc.mp hq
    have hqxPos : 0 < q * x := Nat.mul_pos (by omega) (by omega)
    have hlogNonneg : 0 ≤ Real.log ((q * x : ℕ) : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hqxPos.ne')
    have hlogLe :
        Real.log ((q * x : ℕ) : ℝ) ≤
          Real.log ((Q * x : ℕ) : ℝ) := by
      apply Real.log_le_log
      · exact_mod_cast hqxPos
      · exact_mod_cast Nat.mul_le_mul_right x hqBounds.2
    exact (sq_le_sq₀ hlogNonneg (hlogNonneg.trans hlogLe)).2 hlogLe
  calc
    (∑ q ∈ Finset.Icc 1 Q,
        Real.log ((q * x : ℕ) : ℝ) ^ 2) ≤
        ∑ _q ∈ Finset.Icc 1 Q,
          Real.log ((Q * x : ℕ) : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro q hq
      exact hpoint q hq
    _ = (Q : ℝ) * Real.log ((Q * x : ℕ) : ℝ) ^ 2 := by
      simp [nsmul_eq_mul]

/-- Sum the fixed-modulus global-centered character reduction over every
positive modulus through `Q`. -/
theorem
    sum_allModuli_maxCenteredProgressionDiscrepancyUpTo_le_log_sq_add_inducing
    (x Q : ℕ) (hx : 2 ≤ x) :
    (∑ q ∈ Finset.Icc 1 Q,
      maxCenteredProgressionDiscrepancyUpTo x q) ≤
      (Q : ℝ) * Real.log ((Q * x : ℕ) : ℝ) ^ 2 +
        ∑ q ∈ Finset.Icc 1 Q,
          (q.totient : ℝ)⁻¹ *
            ∑ χ : DirichletCharacter ℂ q,
              inducingPrimitiveCenteredEndpointMaximum x q χ := by
  calc
    (∑ q ∈ Finset.Icc 1 Q,
        maxCenteredProgressionDiscrepancyUpTo x q) ≤
        ∑ q ∈ Finset.Icc 1 Q,
          (Real.log ((q * x : ℕ) : ℝ) ^ 2 +
            (q.totient : ℝ)⁻¹ *
              ∑ χ : DirichletCharacter ℂ q,
                inducingPrimitiveCenteredEndpointMaximum x q χ) := by
      apply Finset.sum_le_sum
      intro q hq
      exact maxCenteredProgressionDiscrepancyUpTo_le_log_sq_add_primitive
        hx (Finset.mem_Icc.mp hq).1
    _ = (∑ q ∈ Finset.Icc 1 Q,
          Real.log ((q * x : ℕ) : ℝ) ^ 2) +
        ∑ q ∈ Finset.Icc 1 Q,
          (q.totient : ℝ)⁻¹ *
            ∑ χ : DirichletCharacter ℂ q,
              inducingPrimitiveCenteredEndpointMaximum x q χ := by
      rw [Finset.sum_add_distrib]
    _ ≤ (Q : ℝ) * Real.log ((Q * x : ℕ) : ℝ) ^ 2 +
        ∑ q ∈ Finset.Icc 1 Q,
          (q.totient : ℝ)⁻¹ *
            ∑ χ : DirichletCharacter ℂ q,
              inducingPrimitiveCenteredEndpointMaximum x q χ := by
      exact add_le_add (sum_allModuli_log_sq_le x Q hx) le_rfl

/-- All-modulus centered discrepancy bound with the small and large primitive
conductor branches exposed but not analytically estimated. -/
theorem
    sum_maxCenteredProgressionDiscrepancyUpTo_le_log_sq_add_small_add_large
    (x Q R : ℕ) (hx : 2 ≤ x) :
    (∑ q ∈ Finset.Icc 1 Q,
      maxCenteredProgressionDiscrepancyUpTo x q) ≤
      (Q : ℝ) * Real.log ((Q * x : ℕ) : ℝ) ^ 2 +
        smallConductorCenteredMass x Q R +
          largeConductorCenteredMass x Q R := by
  calc
    (∑ q ∈ Finset.Icc 1 Q,
        maxCenteredProgressionDiscrepancyUpTo x q) ≤
        (Q : ℝ) * Real.log ((Q * x : ℕ) : ℝ) ^ 2 +
          ∑ q ∈ Finset.Icc 1 Q,
            (q.totient : ℝ)⁻¹ *
              ∑ χ : DirichletCharacter ℂ q,
                inducingPrimitiveCenteredEndpointMaximum x q χ :=
      sum_allModuli_maxCenteredProgressionDiscrepancyUpTo_le_log_sq_add_inducing
        x Q hx
    _ = (Q : ℝ) * Real.log ((Q * x : ℕ) : ℝ) ^ 2 +
        smallConductorCenteredMass x Q R +
          largeConductorCenteredMass x Q R := by
      rw [allModulusCenteredCharacterMass_eq_small_add_large]
      ring

end

end BoundedGaps.Maynard
