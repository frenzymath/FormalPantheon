import BoundedGaps.BombieriVinogradov.Analytic.LargeConductorMassBound
import BoundedGaps.BombieriVinogradov.Analytic.SmallConductorMassBound

/-!
# Logarithmic conductor composition

This file chooses the shared primitive-conductor cutoff
`floor ((log x) ^ D)` and composes the exact all-modulus split with the
small-conductor Siegel--Walfisz bound and the large-conductor Vaughan Abel
envelope. No asymptotic term is absorbed here.

Sources: `Vaughan1980`, p. 113; `AkbaryHambrook2013v2`, Section 7,
pp. 24--25; and `DavenportMNTCh22SW1980`, pp. 132--133. The named cutoff and
three-term composition are project-derived. Semantic review: `SEM-567`.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable section

/-- Natural primitive-conductor split at the `D`th real power of `log x`. -/
noncomputable def siegelWalfiszConductorCutoff
    (D : ℝ) (x : ℕ) : ℕ :=
  Nat.floor (Real.log (x : ℝ) ^ D)

/-- The natural floor cutoff never exceeds its defining real scale. -/
theorem natCast_siegelWalfiszConductorCutoff_le
    (D : ℝ) (x : ℕ) :
    ((siegelWalfiszConductorCutoff D x : ℕ) : ℝ) ≤
      Real.log (x : ℝ) ^ D := by
  unfold siegelWalfiszConductorCutoff
  exact Nat.floor_le
    (Real.rpow_nonneg (Real.log_natCast_nonneg x) D)

/-- Above the common endpoint threshold, a positive logarithmic exponent
gives a nontrivial conductor cutoff. -/
theorem one_le_siegelWalfiszConductorCutoff
    {D : ℝ} (hD : 0 < D) {x : ℕ} (hx : 4 ≤ x) :
    1 ≤ siegelWalfiszConductorCutoff D x := by
  unfold siegelWalfiszConductorCutoff
  exact (Nat.one_le_floor_iff _).2
    (Real.one_le_rpow (one_le_log_natCast hx) hD.le)

/-- Exact composition of the all-modulus centered discrepancy split at the
floored logarithmic conductor scale. The correction, small branch, and large
branch remain separate for later scalar optimization. -/
theorem
    exists_siegelWalfisz_sum_maxCenteredProgressionDiscrepancyUpTo_le_abelEnvelope :
    ∀ D : ℝ, 0 < D →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∃ X0 : ℕ, 4 ≤ X0 ∧
          ∀ x : ℕ, X0 ≤ x →
            ∀ Q : ℕ, siegelWalfiszConductorCutoff D x ≤ Q →
              (Q : ℝ) ≤ Real.sqrt (x : ℝ) →
                (∑ q ∈ Finset.Icc 1 Q,
                  maxCenteredProgressionDiscrepancyUpTo x q) ≤
                  (Q : ℝ) * Real.log ((Q * x : ℕ) : ℝ) ^ 2 +
                    4 * (((siegelWalfiszConductorCutoff D x - 1 : ℕ) : ℝ)) *
                      (1 + Real.log (Q : ℝ)) *
                        (C * ((x : ℝ) * Real.exp
                          (-c * Real.sqrt (Real.log (x : ℝ))))) +
                    (5 * vaughanPrimitiveMeanEquationOneOneConstant
                        (Real.log 4 + 4)) *
                      vaughanPrimitiveMeanAbelEnvelope x
                        (siegelWalfiszConductorCutoff D x : ℝ) Q *
                        vaughanPrimitiveMeanEquationOneTwoLogPower x := by
  intro D hD
  obtain ⟨C, c, hC, hc, X0, hX0, hsmall⟩ :=
    exists_siegelWalfisz_smallConductorCenteredMass_le D hD
  refine ⟨C, c, hC, hc, X0, hX0, ?_⟩
  intro x hx Q hcutoffQ hQsqrt
  let R := siegelWalfiszConductorCutoff D x
  have hx4 : 4 ≤ x := hX0.trans hx
  have hR : 1 ≤ R := by
    simpa only [R] using one_le_siegelWalfiszConductorCutoff hD hx4
  have hRQ : R ≤ Q := by
    simpa only [R] using hcutoffQ
  have hmin : min R Q = R := min_eq_left hRQ
  have hcutoff :
      ((min R Q : ℕ) : ℝ) ≤ Real.log (x : ℝ) ^ D := by
    rw [hmin]
    simpa only [R] using natCast_siegelWalfiszConductorCutoff_le D x
  have hsmallBound := hsmall x hx Q R hcutoff
  have hlargeBound := largeConductorCenteredMass_le_abelEnvelope
    x Q R hx4 hQsqrt hR hRQ
  have hsplit :=
    sum_maxCenteredProgressionDiscrepancyUpTo_le_log_sq_add_small_add_large
      x Q R (by omega)
  calc
    (∑ q ∈ Finset.Icc 1 Q,
        maxCenteredProgressionDiscrepancyUpTo x q) ≤
        (Q : ℝ) * Real.log ((Q * x : ℕ) : ℝ) ^ 2 +
          smallConductorCenteredMass x Q R +
            largeConductorCenteredMass x Q R := hsplit
    _ ≤ (Q : ℝ) * Real.log ((Q * x : ℕ) : ℝ) ^ 2 +
          4 * (((min R Q - 1 : ℕ) : ℝ)) *
            (1 + Real.log (Q : ℝ)) *
              (C * ((x : ℝ) * Real.exp
                (-c * Real.sqrt (Real.log (x : ℝ))))) +
          (5 * vaughanPrimitiveMeanEquationOneOneConstant
              (Real.log 4 + 4)) *
            vaughanPrimitiveMeanAbelEnvelope x (R : ℝ) Q *
              vaughanPrimitiveMeanEquationOneTwoLogPower x :=
      add_le_add (add_le_add le_rfl hsmallBound) hlargeBound
    _ = _ := by simp only [hmin, R]

end

end BoundedGaps.Maynard
