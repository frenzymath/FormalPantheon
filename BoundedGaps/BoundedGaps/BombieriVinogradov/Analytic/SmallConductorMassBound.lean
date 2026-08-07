import BoundedGaps.BombieriVinogradov.Analytic.AllModulusConductorSplit
import BoundedGaps.BombieriVinogradov.Analytic.ReciprocalTotientPrefix
import BoundedGaps.BombieriVinogradov.Analytic.SiegelWalfiszEndpointMaximum

/-!
# Small-conductor all-modulus mass bound

This file estimates the small-inducing-conductor branch of SEM-463. It
regroups the exact positive factor-pair support, cancels primitive-character
counting against the conductor totient, and applies SEM-424 and SEM-565.

Sources: `Vaughan1980`, p. 113, and `AkbaryHambrook2013v2`, Section 7,
pp. 24--25. The exact `min R Q` support and constant-four conclusion are
project-derived. Semantic review: `SEM-566`.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable section

/-- Regroup the exact small-conductor mass by its primitive conductor and
positive multiplier. -/
theorem smallConductorCenteredMass_eq_sum_multipliers
    (x Q R : ℕ) :
    smallConductorCenteredMass x Q R =
      ∑ d ∈ Finset.Ioc 1 (min R Q),
        (∑ ψ : primitiveCharacters d,
          primitiveCenteredEndpointMaximum x d ψ) *
          ∑ k ∈ Finset.Ioc 0 (Q / d),
            ((d * k).totient : ℝ)⁻¹ := by
  classical
  unfold smallConductorCenteredMass
  have hreindex :
      (∑ p ∈ (positiveFactorPairs Q).filter (fun p ↦
          p.1 ≠ 1 ∧ p.1 ≤ R),
        ((p.1 * p.2).totient : ℝ)⁻¹ *
          ∑ ψ : primitiveCharacters p.1,
            primitiveCenteredEndpointMaximum x p.1 ψ) =
        ∑ d ∈ Finset.Ioc 0 Q with d ≠ 1 ∧ d ≤ R,
          ∑ k ∈ Finset.Ioc 0 (Q / d),
            ((d * k).totient : ℝ)⁻¹ *
              ∑ ψ : primitiveCharacters d,
                primitiveCenteredEndpointMaximum x d ψ := by
    simpa only using
      (sum_positiveFactorPairs_filter_fst_eq_sum_multipliers
        (Q := Q) (fun d ↦ d ≠ 1 ∧ d ≤ R)
        (fun d k ↦ ((d * k).totient : ℝ)⁻¹ *
          ∑ ψ : primitiveCharacters d,
            primitiveCenteredEndpointMaximum x d ψ))
  have hindex :
      (Finset.Ioc 0 Q).filter (fun d ↦ d ≠ 1 ∧ d ≤ R) =
        Finset.Ioc 1 (min R Q) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    omega
  rw [hreindex, hindex]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [mul_comm]

/-- Aggregate any common nonnegative endpoint envelope over the exact small
primitive-conductor support. -/
theorem smallConductorCenteredMass_le_of_endpointMaximum
    {x Q R : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hendpoint : ∀ d : ℕ, 1 < d → d ≤ min R Q →
      ∀ ψ : primitiveCharacters d,
        primitiveCenteredEndpointMaximum x d ψ ≤ B) :
    smallConductorCenteredMass x Q R ≤
      4 * (((min R Q - 1 : ℕ) : ℝ)) *
        (1 + Real.log (Q : ℝ)) * B := by
  rw [smallConductorCenteredMass_eq_sum_multipliers]
  have hlogQ : 0 ≤ Real.log (Q : ℝ) := Real.log_natCast_nonneg Q
  calc
    (∑ d ∈ Finset.Ioc 1 (min R Q),
        (∑ ψ : primitiveCharacters d,
          primitiveCenteredEndpointMaximum x d ψ) *
          ∑ k ∈ Finset.Ioc 0 (Q / d),
            ((d * k).totient : ℝ)⁻¹) ≤
        ∑ _d ∈ Finset.Ioc 1 (min R Q),
          4 * (1 + Real.log (Q : ℝ)) * B := by
      apply Finset.sum_le_sum
      intro d hdmem
      have hdBounds := Finset.mem_Ioc.mp hdmem
      have hdpos : 0 < d := by omega
      have hdQ : d ≤ Q := hdBounds.2.trans (min_le_right R Q)
      have hQdiv : 0 < Q / d := Nat.div_pos hdQ hdpos
      have hphi : 0 < (d.totient : ℝ) := by
        exact_mod_cast Nat.totient_pos.mpr hdpos
      have hmass :
          (∑ ψ : primitiveCharacters d,
            primitiveCenteredEndpointMaximum x d ψ) ≤
            (d.totient : ℝ) * B := by
        calc
          (∑ ψ : primitiveCharacters d,
              primitiveCenteredEndpointMaximum x d ψ) ≤
              ∑ _ψ : primitiveCharacters d, B := by
            apply Finset.sum_le_sum
            intro ψ _hψ
            exact hendpoint d hdBounds.1 hdBounds.2 ψ
          _ = (Fintype.card (primitiveCharacters d) : ℝ) * B := by
            simp
          _ ≤ (d.totient : ℝ) * B := by
            apply mul_le_mul_of_nonneg_right _ hB
            exact_mod_cast card_primitiveCharacters_le_totient hdpos
      have hprefix :
          (∑ k ∈ Finset.Ioc 0 (Q / d),
            (k.totient : ℝ)⁻¹) ≤
            4 * (1 + Real.log ((Q / d : ℕ) : ℝ)) := by
        simpa [reciprocalTotientPrefix] using
          reciprocalTotientPrefix_le_four_mul_one_add_log hQdiv
      have hlogDiv :
          Real.log ((Q / d : ℕ) : ℝ) ≤ Real.log (Q : ℝ) := by
        apply Real.log_le_log
        · exact_mod_cast hQdiv
        · exact_mod_cast Nat.div_le_self Q d
      have hweight :
          (∑ k ∈ Finset.Ioc 0 (Q / d),
            ((d * k).totient : ℝ)⁻¹) ≤
            (d.totient : ℝ)⁻¹ *
              (4 * (1 + Real.log (Q : ℝ))) := by
        calc
          (∑ k ∈ Finset.Ioc 0 (Q / d),
              ((d * k).totient : ℝ)⁻¹) ≤
              (d.totient : ℝ)⁻¹ *
                ∑ k ∈ Finset.Ioc 0 (Q / d),
                  (k.totient : ℝ)⁻¹ :=
            sum_inv_totient_mul_le_inv_totient_mul_sum Q d hdpos
          _ ≤ (d.totient : ℝ)⁻¹ *
              (4 * (1 + Real.log ((Q / d : ℕ) : ℝ))) := by
            exact mul_le_mul_of_nonneg_left hprefix (by positivity)
          _ ≤ (d.totient : ℝ)⁻¹ *
              (4 * (1 + Real.log (Q : ℝ))) := by
            apply mul_le_mul_of_nonneg_left
            · gcongr
            · positivity
      calc
        (∑ ψ : primitiveCharacters d,
            primitiveCenteredEndpointMaximum x d ψ) *
            ∑ k ∈ Finset.Ioc 0 (Q / d),
              ((d * k).totient : ℝ)⁻¹ ≤
            (∑ ψ : primitiveCharacters d,
              primitiveCenteredEndpointMaximum x d ψ) *
              ((d.totient : ℝ)⁻¹ *
                (4 * (1 + Real.log (Q : ℝ)))) :=
          mul_le_mul_of_nonneg_left hweight
            (sum_primitiveCenteredEndpointMaximum_nonneg x d)
        _ ≤ ((d.totient : ℝ) * B) *
              ((d.totient : ℝ)⁻¹ *
                (4 * (1 + Real.log (Q : ℝ)))) := by
          apply mul_le_mul_of_nonneg_right hmass
          positivity
        _ = 4 * (1 + Real.log (Q : ℝ)) * B := by
          field_simp [ne_of_gt hphi]
    _ = 4 * (((min R Q - 1 : ℕ) : ℝ)) *
        (1 + Real.log (Q : ℝ)) * B := by
      rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ioc]
      ring

/-- Siegel--Walfisz controls the full small-conductor centered mass at the
exact cutoff supported by the original moduli. -/
theorem exists_siegelWalfisz_smallConductorCenteredMass_le :
    ∀ D : ℝ, 0 < D →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∃ X0 : ℕ, 4 ≤ X0 ∧
          ∀ x : ℕ, X0 ≤ x →
            ∀ Q R : ℕ,
              ((min R Q : ℕ) : ℝ) ≤ Real.log (x : ℝ) ^ D →
                smallConductorCenteredMass x Q R ≤
                  4 * (((min R Q - 1 : ℕ) : ℝ)) *
                    (1 + Real.log (Q : ℝ)) *
                      (C * ((x : ℝ) * Real.exp
                        (-c * Real.sqrt (Real.log (x : ℝ))))) := by
  intro D hD
  obtain ⟨C, c, hC, hc, X0, hX0, hSiegelWalfisz⟩ :=
    exists_siegelWalfisz_primitiveCenteredEndpointMaximum_le D hD
  refine ⟨C, c, hC, hc, X0, hX0, ?_⟩
  intro x hx Q R hcutoff
  apply smallConductorCenteredMass_le_of_endpointMaximum
  · positivity
  · intro d hd hdCutoff ψ
    apply hSiegelWalfisz x hx d hd
    exact (by exact_mod_cast hdCutoff :
      (d : ℝ) ≤ ((min R Q : ℕ) : ℝ)).trans hcutoff

end

end BoundedGaps.Maynard
