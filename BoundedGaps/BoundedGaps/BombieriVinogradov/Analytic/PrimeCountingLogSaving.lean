import BoundedGaps.BombieriVinogradov.Analytic.BelowCutoffLogSaving
import BoundedGaps.BombieriVinogradov.Analytic.CenteredPrimeCountingComposition

/-!
# Prime-counting logarithmic saving

This file absorbs SEM-574's prime-power envelope using pinned Mathlib's
square-root bound for `Chebyshev.psi - Chebyshev.theta`, then composes the
result with SEM-571's centered logarithmic saving. The first theorem retains
all five spare logarithmic powers; the aggregate theorem spends them only at
the inherited endpoint `x >= 4`.

The surrounding route is compared with `AkbaryHambrook2013v2`, printed pp. 4
and 26, and `Maynard2013v3`, equation `eq:LevelOfDistribution`. The exact
contracts are project-derived. Semantic review: `SEM-575`.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

private theorem exists_nonneg_psi_sub_theta_le_mul_sqrt :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ y : ℝ,
        Chebyshev.psi y - Chebyshev.theta y ≤ K * Real.sqrt y := by
  obtain ⟨K, hK⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨max K 0, le_max_right K 0, ?_⟩
  intro y
  exact (hK y).trans
    (mul_le_mul_of_nonneg_right (le_max_left K 0) (Real.sqrt_nonneg y))

/-- One absolute constant bounds the aggregate prime-power envelope throughout
the logarithmically reduced square-root range, without spending its five spare
logarithmic powers. -/
theorem exists_primePowerRemainder_mul_cutoff_le_logSaving :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (A : ℝ) (x Q : ℕ), 2 ≤ x →
        (Q : ℝ) ≤ Real.sqrt (x : ℝ) /
            Real.rpow (Real.log (x : ℝ)) (A + 5) →
          (Q : ℝ) *
              (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ)) ≤
            K * (x : ℝ) /
              Real.rpow (Real.log (x : ℝ)) (A + 5) := by
  obtain ⟨K, hK, hKbound⟩ := exists_nonneg_psi_sub_theta_le_mul_sqrt
  refine ⟨K, hK, ?_⟩
  intro A x Q hx hQ
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := by positivity
  have hxOne : (1 : ℝ) < (x : ℝ) := by
    exact_mod_cast (show 1 < x by omega)
  have hpowPos :
      0 < Real.rpow (Real.log (x : ℝ)) (A + 5) :=
    Real.rpow_pos_of_pos (Real.log_pos hxOne) _
  have hremainder :
      0 ≤ Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ) :=
    sub_nonneg.mpr (Chebyshev.theta_le_psi _)
  calc
    (Q : ℝ) *
          (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ)) ≤
        (Real.sqrt (x : ℝ) /
            Real.rpow (Real.log (x : ℝ)) (A + 5)) *
          (K * Real.sqrt (x : ℝ)) :=
      mul_le_mul hQ (hKbound (x : ℝ)) hremainder
        (div_nonneg (Real.sqrt_nonneg _) hpowPos.le)
    _ = K * (x : ℝ) /
        Real.rpow (Real.log (x : ℝ)) (A + 5) := by
      rw [div_mul_eq_mul_div]
      congr 1
      calc
        Real.sqrt (x : ℝ) * (K * Real.sqrt (x : ℝ)) =
            K * (Real.sqrt (x : ℝ) * Real.sqrt (x : ℝ)) := by ring
        _ = K * (x : ℝ) := by rw [Real.mul_self_sqrt hx0]

/-- The prime-counting logarithmic saving with the absolute prime-power
constant and the inherited centered coefficient both visible. -/
theorem
    exists_sum_maxProgressionDiscrepancy_le_inv_log_two_mul_logSaving_allCutoffs :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ A : ℝ, 0 ≤ A →
        ∃ C : ℝ, 0 < C ∧
          ∃ X0 : ℕ, 4 ≤ X0 ∧
            ∀ x : ℕ, X0 ≤ x →
              ∀ Q : ℕ,
                (Q : ℝ) ≤ Real.sqrt (x : ℝ) /
                    Real.rpow (Real.log (x : ℝ)) (A + 5) →
                  (∑ q ∈ Finset.Icc 1 Q,
                      maxProgressionDiscrepancy x q) ≤
                    (Real.log 2)⁻¹ *
                      ((C + 40 * vaughanPrimitiveMeanEquationOneTwoConstant
                          (Real.log 4 + 4) + K) *
                        (x : ℝ) / Real.rpow (Real.log (x : ℝ)) A) := by
  obtain ⟨K, hK, hKbound⟩ :=
    exists_primePowerRemainder_mul_cutoff_le_logSaving
  refine ⟨K, hK, ?_⟩
  intro A hA
  obtain ⟨C, _, hC, _, X0, hX0, hpsi⟩ :=
    exists_siegelWalfisz_sum_maxCenteredProgressionDiscrepancyUpTo_le_logSaving_allCutoffs
      A hA
  refine ⟨C, hC, X0, hX0, ?_⟩
  intro x hx Q hQ
  have hx4 : 4 ≤ x := hX0.trans hx
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := by positivity
  have hlogOne : 1 ≤ Real.log (x : ℝ) := one_le_log_natCast hx4
  have hpowAPos : 0 < Real.rpow (Real.log (x : ℝ)) A :=
    Real.rpow_pos_of_pos (zero_lt_one.trans_le hlogOne) _
  have hpowLe :
      Real.rpow (Real.log (x : ℝ)) A ≤
        Real.rpow (Real.log (x : ℝ)) (A + 5) :=
    Real.rpow_le_rpow_of_exponent_le hlogOne (by linarith)
  have hprimePower :
      (Q : ℝ) *
          (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ)) ≤
        K * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) A :=
    (hKbound A x Q (by omega) hQ).trans
      (div_le_div_of_nonneg_left (mul_nonneg hK hx0) hpowAPos hpowLe)
  calc
    (∑ q ∈ Finset.Icc 1 Q, maxProgressionDiscrepancy x q) ≤
        (Real.log 2)⁻¹ *
          ((∑ q ∈ Finset.Icc 1 Q,
              maxCenteredProgressionDiscrepancyUpTo x q) +
            (Q : ℝ) *
              (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ))) :=
      sum_maxProgressionDiscrepancy_le_inv_log_two_mul_centeredPsiPrimePowerEnvelope
        (show 2 ≤ x by omega)
    _ ≤ (Real.log 2)⁻¹ *
        ((C + 40 * vaughanPrimitiveMeanEquationOneTwoConstant
            (Real.log 4 + 4)) * (x : ℝ) /
              Real.rpow (Real.log (x : ℝ)) A +
          K * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) A) := by
      apply mul_le_mul_of_nonneg_left _
        ((inv_pos.mpr (Real.log_pos one_lt_two)).le)
      exact add_le_add (hpsi x hx Q hQ) hprimePower
    _ = (Real.log 2)⁻¹ *
        ((C + 40 * vaughanPrimitiveMeanEquationOneTwoConstant
            (Real.log 4 + 4) + K) *
          (x : ℝ) / Real.rpow (Real.log (x : ℝ)) A) := by
      ring

/-- The prime-counting logarithmic saving with one sign-certified coefficient,
in the form needed by the later public-level cutoff adapter. -/
theorem exists_sum_maxProgressionDiscrepancy_le_logSaving_allCutoffs :
    ∀ A : ℝ, 0 ≤ A →
      ∃ C : ℝ, 0 ≤ C ∧
        ∃ X0 : ℕ, 4 ≤ X0 ∧
          ∀ x : ℕ, X0 ≤ x →
            ∀ Q : ℕ,
              (Q : ℝ) ≤ Real.sqrt (x : ℝ) /
                  Real.rpow (Real.log (x : ℝ)) (A + 5) →
                (∑ q ∈ Finset.Icc 1 Q,
                    maxProgressionDiscrepancy x q) ≤
                  C * (x : ℝ) /
                    Real.rpow (Real.log (x : ℝ)) A := by
  obtain ⟨K, hK, hboundAll⟩ :=
    exists_sum_maxProgressionDiscrepancy_le_inv_log_two_mul_logSaving_allCutoffs
  intro A hA
  obtain ⟨C, hC, X0, hX0, hbound⟩ := hboundAll A hA
  let D := (Real.log 2)⁻¹ *
    (C + 40 * vaughanPrimitiveMeanEquationOneTwoConstant
      (Real.log 4 + 4) + K)
  have hC12 :
      0 ≤ vaughanPrimitiveMeanEquationOneTwoConstant (Real.log 4 + 4) := by
    unfold vaughanPrimitiveMeanEquationOneTwoConstant
    have h := vaughanPrimitiveMeanEquationOneOneConstant_nonneg
      (Real.log 4 + 4)
    positivity
  have hD : 0 ≤ D := by
    dsimp only [D]
    positivity [Real.log_pos one_lt_two]
  refine ⟨D, hD, X0, hX0, ?_⟩
  intro x hx Q hQ
  calc
    (∑ q ∈ Finset.Icc 1 Q, maxProgressionDiscrepancy x q) ≤
        (Real.log 2)⁻¹ *
          ((C + 40 * vaughanPrimitiveMeanEquationOneTwoConstant
              (Real.log 4 + 4) + K) *
            (x : ℝ) / Real.rpow (Real.log (x : ℝ)) A) :=
      hbound x hx Q hQ
    _ = D * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) A := by
      dsimp only [D]
      ring

end BoundedGaps.Maynard
