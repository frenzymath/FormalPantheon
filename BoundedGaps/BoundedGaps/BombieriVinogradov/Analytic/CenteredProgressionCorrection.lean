import BoundedGaps.BombieriVinogradov.Analytic.WeightedConductorReindex

/-!
# Global-Chebyshev-centered progression correction

This file names the source-order endpoint/residue discrepancy in
Akbary--Hambrook's equation (1.2), applies SEM-420 at each modulus, and sums
the elementary squared-log correction over rough moduli.

Source: `AkbaryHambrook2013v2`, Section 7, printed p. 24. Semantic review:
`SEM-462`.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable section

/-- Progression discrepancy centered at the global Chebyshev function. This
is distinct from the earlier discrepancy centered at `x / phi(q)`. -/
noncomputable def centeredProgressionDiscrepancy
    (x q a : ℕ) : ℝ :=
  |chebyshevProgressionSum x q a -
    Chebyshev.psi (x : ℝ) / (q.totient : ℝ)|

/-- Reduced-residue maximum of the global-Chebyshev-centered discrepancy. -/
noncomputable def maxCenteredProgressionDiscrepancy
    (x q : ℕ) : ℝ :=
  if hq : 0 < q then
    (coprimeResidues q).sup' (coprimeResidues_nonempty hq)
      (centeredProgressionDiscrepancy x q)
  else 0

/-- Source-order maximum: endpoints outermost and reduced residues innermost. -/
noncomputable def maxCenteredProgressionDiscrepancyUpTo
    (x q : ℕ) : ℝ :=
  if hx : 2 ≤ x then
    (Finset.Icc 2 x).sup' (weightedEndpointRange_nonempty hx)
      (fun y ↦ maxCenteredProgressionDiscrepancy y q)
  else 0

/-- Unfold the totalized maximum on its positive source range. -/
theorem maxCenteredProgressionDiscrepancyUpTo_eq_sup_endpoint_residues
    {x q : ℕ} (hx : 2 ≤ x) (hq : 0 < q) :
    maxCenteredProgressionDiscrepancyUpTo x q =
      (Finset.Icc 2 x).sup' (weightedEndpointRange_nonempty hx) (fun y ↦
        (coprimeResidues q).sup' (coprimeResidues_nonempty hq) (fun a ↦
          |chebyshevProgressionSum y q a -
            Chebyshev.psi (y : ℝ) / (q.totient : ℝ)|)) := by
  rw [maxCenteredProgressionDiscrepancyUpTo, dif_pos hx]
  simp_rw [maxCenteredProgressionDiscrepancy, dif_pos hq,
    centeredProgressionDiscrepancy]

/-- The fixed-modulus source discrepancy is bounded by its elementary
correction plus the inducing-primitive centered character sum. -/
theorem maxCenteredProgressionDiscrepancyUpTo_le_log_sq_add_primitive
    {x q : ℕ} (hx : 2 ≤ x) (hq : 1 ≤ q) :
    maxCenteredProgressionDiscrepancyUpTo x q ≤
      Real.log ((q * x : ℕ) : ℝ) ^ 2 +
        (q.totient : ℝ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q,
            inducingPrimitiveCenteredEndpointMaximum x q χ := by
  rw [maxCenteredProgressionDiscrepancyUpTo_eq_sup_endpoint_residues
    hx (by omega)]
  exact
    centeredProgressionResidueEndpointMaximum_le_log_sq_add_primitive hx hq

noncomputable local instance
    roughModulusAboveDecidableForCenteredProgressionCorrection
    (Q1 : ℝ) : DecidablePred (roughModulusAbove Q1) :=
  Classical.decPred _

private theorem sum_rough_log_sq_le
    (x Q : ℕ) (Q1 : ℝ) (hx : 2 ≤ x) :
    (∑ q ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 q,
      Real.log ((q * x : ℕ) : ℝ) ^ 2) ≤
      (Q : ℝ) * Real.log ((Q * x : ℕ) : ℝ) ^ 2 := by
  let S := (Finset.Ioc 0 Q).filter (roughModulusAbove Q1)
  have hpoint : ∀ q ∈ S,
      Real.log ((q * x : ℕ) : ℝ) ^ 2 ≤
        Real.log ((Q * x : ℕ) : ℝ) ^ 2 := by
    intro q hqS
    have hqBounds := Finset.mem_Ioc.mp (Finset.mem_filter.mp hqS).1
    have hqxPos : 0 < q * x := Nat.mul_pos hqBounds.1 (by omega)
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
  have hcard : S.card ≤ Q := by
    calc
      S.card ≤ (Finset.Ioc 0 Q).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = Q := by simp
  change (∑ q ∈ S, Real.log ((q * x : ℕ) : ℝ) ^ 2) ≤ _
  calc
    (∑ q ∈ S, Real.log ((q * x : ℕ) : ℝ) ^ 2) ≤
        ∑ _q ∈ S, Real.log ((Q * x : ℕ) : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro q hq
      exact hpoint q hq
    _ = (S.card : ℝ) * Real.log ((Q * x : ℕ) : ℝ) ^ 2 := by
      simp [nsmul_eq_mul]
    _ ≤ (Q : ℝ) * Real.log ((Q * x : ℕ) : ℝ) ^ 2 := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hcard
      · positivity

/-- The rough-modulus discrepancy sum splits into the coefficient-one
elementary correction and the unchanged inducing-character sum. -/
theorem sum_maxCenteredProgressionDiscrepancyUpTo_le_log_sq_add_inducing
    (x Q : ℕ) (Q1 : ℝ) (hx : 2 ≤ x) :
    (∑ q ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 q,
      maxCenteredProgressionDiscrepancyUpTo x q) ≤
      (Q : ℝ) * Real.log ((Q * x : ℕ) : ℝ) ^ 2 +
        ∑ q ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 q,
          (q.totient : ℝ)⁻¹ *
            ∑ χ : DirichletCharacter ℂ q,
              inducingPrimitiveCenteredEndpointMaximum x q χ := by
  calc
    (∑ q ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 q,
        maxCenteredProgressionDiscrepancyUpTo x q) ≤
      ∑ q ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 q,
        (Real.log ((q * x : ℕ) : ℝ) ^ 2 +
          (q.totient : ℝ)⁻¹ *
            ∑ χ : DirichletCharacter ℂ q,
              inducingPrimitiveCenteredEndpointMaximum x q χ) := by
      apply Finset.sum_le_sum
      intro q hq
      exact maxCenteredProgressionDiscrepancyUpTo_le_log_sq_add_primitive
        hx (Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1).1
    _ = (∑ q ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 q,
          Real.log ((q * x : ℕ) : ℝ) ^ 2) +
        ∑ q ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 q,
          (q.totient : ℝ)⁻¹ *
            ∑ χ : DirichletCharacter ℂ q,
              inducingPrimitiveCenteredEndpointMaximum x q χ := by
      rw [Finset.sum_add_distrib]
    _ ≤ (Q : ℝ) * Real.log ((Q * x : ℕ) : ℝ) ^ 2 +
        ∑ q ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 q,
          (q.totient : ℝ)⁻¹ *
            ∑ χ : DirichletCharacter ℂ q,
              inducingPrimitiveCenteredEndpointMaximum x q χ := by
      exact add_le_add (sum_rough_log_sq_le x Q Q1 hx) le_rfl

end

end BoundedGaps.Maynard
