import BoundedGaps.BombieriVinogradov.Analytic.CenteredPrimitiveMaxima
import BoundedGaps.BombieriVinogradov.Analytic.PositiveDivisorPairReindex

/-!
# Exact weighted conductor reindex

This file formalizes the exact weighted index change on
Akbary--Hambrook2013v2, Section 7, p. 25. It retains the product roughness
condition and the reciprocal totient of the full modulus. The subsequent
domain enlargement and reciprocal-totient estimate are deliberately separate.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable section

/-- A positive modulus whose least prime factor is above the real cutoff. -/
def roughModulusAbove (Q1 : ℝ) (q : ℕ) : Prop :=
  1 < q ∧ Q1 < (q.minFac : ℝ)

noncomputable local instance roughModulusAboveDecidable (Q1 : ℝ) :
    DecidablePred (roughModulusAbove Q1) :=
  Classical.decPred _

/-- On positive moduli and above cutoff one, the explicit source-domain guard
is equivalent to the bare least-prime-factor comparison. -/
theorem roughModulusAbove_iff_minFac
    {Q1 : ℝ} {q : ℕ} (hQ1 : 1 ≤ Q1) (hq : 0 < q) :
    roughModulusAbove Q1 q ↔ Q1 < (q.minFac : ℝ) := by
  unfold roughModulusAbove
  constructor
  · exact And.right
  · intro hmin
    by_cases hq1 : q = 1
    · subst q
      simp [Nat.minFac_one] at hmin
      linarith
    · exact ⟨Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hq.ne', hq1⟩, hmin⟩

/-- Reindex the exact reciprocal-totient weighted inducing-character sum by
positive `(conductor, multiplier)` pairs. -/
theorem sum_weightedInducingPrimitiveCenteredEndpointMaximum_eq_factorPairs
    (x Q : ℕ) (Q1 : ℝ) :
    (∑ q ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 q,
      (q.totient : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q,
          inducingPrimitiveCenteredEndpointMaximum x q χ) =
      ∑ p ∈ (positiveFactorPairs Q).filter (fun p ↦
          roughModulusAbove Q1 (p.1 * p.2) ∧ p.1 ≠ 1),
        ((p.1 * p.2).totient : ℝ)⁻¹ *
          ∑ ψ : primitiveCharacters p.1,
            primitiveCenteredEndpointMaximum x p.1 ψ := by
  classical
  let F : ∀ {q d : ℕ}, d ∣ q → primitiveCharacters d → ℝ :=
    fun {q d} _ ψ ↦
      (q.totient : ℝ)⁻¹ * primitiveCenteredEndpointMaximum x d ψ
  have hleft :
      (∑ q ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 q,
        (q.totient : ℝ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q,
            inducingPrimitiveCenteredEndpointMaximum x q χ) =
        ∑ q ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 q,
          ∑ d : q.divisors,
            ∑ ψ : primitiveCharacters d.1,
              F (Nat.dvd_of_mem_divisors d.2) ψ := by
    apply Finset.sum_congr rfl
    intro q hqmem
    have hqpos : 0 < q :=
      (Finset.mem_Ioc.mp (Finset.mem_filter.mp hqmem).1).1
    rw [sum_inducingPrimitiveCenteredEndpointMaximum_eq_divisors hqpos]
    rw [Finset.mul_sum]
    apply Fintype.sum_congr
    intro d
    rw [Finset.mul_sum]
  have hreindex :
      (∑ q ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 q,
        ∑ d : q.divisors,
          ∑ ψ : primitiveCharacters d.1,
            F (Nat.dvd_of_mem_divisors d.2) ψ) =
        ∑ p ∈ (positiveFactorPairs Q).filter (fun p ↦
            roughModulusAbove Q1 (p.1 * p.2)),
          ∑ ψ : primitiveCharacters p.1,
            F (Nat.dvd_mul_right p.1 p.2) ψ :=
    sum_primitive_conductors_up_to_filter_eq_sum_positiveFactorPairs
      (Q := Q) (roughModulusAbove Q1) F
  let G : ℕ × ℕ → ℝ := fun p ↦
    ((p.1 * p.2).totient : ℝ)⁻¹ *
      ∑ ψ : primitiveCharacters p.1,
        primitiveCenteredEndpointMaximum x p.1 ψ
  have hright :
      (∑ p ∈ (positiveFactorPairs Q).filter (fun p ↦
          roughModulusAbove Q1 (p.1 * p.2)),
        ∑ ψ : primitiveCharacters p.1,
          F (Nat.dvd_mul_right p.1 p.2) ψ) =
        ∑ p ∈ (positiveFactorPairs Q).filter (fun p ↦
          roughModulusAbove Q1 (p.1 * p.2)), G p := by
    apply Finset.sum_congr rfl
    intro p hp
    change (∑ ψ : primitiveCharacters p.1,
      ((p.1 * p.2).totient : ℝ)⁻¹ *
        primitiveCenteredEndpointMaximum x p.1 ψ) = G p
    unfold G
    rw [Finset.mul_sum]
  have hzero : ∀ p ∈ (positiveFactorPairs Q).filter (fun p ↦
      roughModulusAbove Q1 (p.1 * p.2)), p.1 = 1 → G p = 0 := by
    intro p hp hp1
    rcases p with ⟨d, k⟩
    simp only at hp1 ⊢
    subst d
    apply mul_eq_zero_of_right
    apply Fintype.sum_eq_zero
    intro ψ
    exact primitiveCenteredEndpointMaximum_one x ψ
  have hfilter :
      (∑ p ∈ (positiveFactorPairs Q).filter (fun p ↦
          roughModulusAbove Q1 (p.1 * p.2) ∧ p.1 ≠ 1), G p) =
        ∑ p ∈ (positiveFactorPairs Q).filter (fun p ↦
          roughModulusAbove Q1 (p.1 * p.2)), G p := by
    apply Finset.sum_subset
    · intro p hp
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1,
        (Finset.mem_filter.mp hp).2.1⟩
    · intro p hp hnot
      have hp1 : p.1 = 1 := by
        by_contra hpne
        exact hnot (Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hp).1,
            ⟨(Finset.mem_filter.mp hp).2, hpne⟩⟩)
      exact hzero p hp hp1
  exact hleft.trans (hreindex.trans (hright.trans hfilter.symm))

end

end BoundedGaps.Maynard
