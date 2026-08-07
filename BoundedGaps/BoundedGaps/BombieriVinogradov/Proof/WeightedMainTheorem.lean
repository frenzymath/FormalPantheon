import BoundedGaps.BombieriVinogradov.Analytic.BelowCutoffLogSaving
import BoundedGaps.BombieriVinogradov.Analytic.WeightedCenterBridge
import BoundedGaps.BombieriVinogradov.Analytic.WeightedPntPrefix

/-!
# Unconditional standard weighted Bombieri--Vinogradov

SEM-571 supplies the all-cutoff estimate after centering at `psi(y)/phi(q)`.
The finite bridge recenters in the reverse direction, retaining its modulus-one
term; the SEM-579 prefix estimate bounds that term with one spare logarithm.
The natural exponent is chosen strictly above `A + 5`, so it also satisfies the
public `A + 4` window.
-/

namespace BoundedGaps.BombieriVinogradov

open scoped BigOperators

noncomputable section

private theorem weightedWindow_target_implies_centeredWindow
    {A : ℝ} {B : ℕ} {x Q : ℕ}
    (hx : 4 ≤ x) (hB : A + 5 < (B : ℝ))
    (hQ : (Q : ℝ) ≤ Real.sqrt (x : ℝ) /
      (Real.log (x : ℝ)) ^ B) :
    (Q : ℝ) ≤ Real.sqrt (x : ℝ) /
      Real.rpow (Real.log (x : ℝ)) (A + 5) := by
  have hlogOne : 1 ≤ Real.log (x : ℝ) :=
    BoundedGaps.Maynard.one_le_log_natCast hx
  have hlogPos : 0 < Real.log (x : ℝ) := zero_lt_one.trans_le hlogOne
  have hpowOrder :
      Real.rpow (Real.log (x : ℝ)) (A + 5) ≤
        (Real.log (x : ℝ)) ^ B := by
    calc
      Real.rpow (Real.log (x : ℝ)) (A + 5) ≤
          Real.rpow (Real.log (x : ℝ)) (B : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hlogOne (by exact_mod_cast hB.le)
      _ = (Real.log (x : ℝ)) ^ B := Real.rpow_natCast _ _
  exact hQ.trans (div_le_div_of_nonneg_left
    (Real.sqrt_nonneg _) (Real.rpow_pos_of_pos hlogPos _)
    hpowOrder)

private theorem weighted_standard_sum_le_logSaving
    {A : ℝ} (hA : 0 ≤ A) :
    ∃ B : ℕ, A + 4 < (B : ℝ) ∧
      ∃ C : ℝ, 0 ≤ C ∧
      ∃ X0 : ℕ, 4 ≤ X0 ∧
        ∀ x : ℕ, X0 ≤ x →
          ∀ Q : ℕ, 1 ≤ Q →
            (Q : ℝ) ≤ Real.sqrt (x : ℝ) /
                (Real.log (x : ℝ)) ^ B →
            (∑ q ∈ Finset.Icc 1 Q,
              maxWeightedProgressionDiscrepancyUpTo x q) ≤
              C * (x : ℝ) /
                Real.rpow (Real.log (x : ℝ)) A := by
  obtain ⟨B, hB⟩ := exists_nat_gt (A + 5)
  obtain ⟨Cc, cc, hCc, hcc, Xc, hXc, hcenter⟩ :=
    BoundedGaps.Maynard.exists_siegelWalfisz_sum_maxCenteredProgressionDiscrepancyUpTo_le_logSaving_allCutoffs
      A hA
  obtain ⟨C1, hC1, X1, hX1, hglobal⟩ :=
    exists_maxWeightedProgressionDiscrepancyUpTo_one_le_logSaving (A + 1)
      (by linarith)
  let C : ℝ := Cc + 40 *
      BoundedGaps.Maynard.vaughanPrimitiveMeanEquationOneTwoConstant
        (Real.log 4 + 4) + 5 * C1
  have hV : 0 ≤ BoundedGaps.Maynard.vaughanPrimitiveMeanEquationOneTwoConstant
      (Real.log 4 + 4) := by
    unfold BoundedGaps.Maynard.vaughanPrimitiveMeanEquationOneTwoConstant
    have h := BoundedGaps.Maynard.vaughanPrimitiveMeanEquationOneOneConstant_nonneg
      (Real.log 4 + 4)
    positivity
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  let X0 : ℕ := max 4 (max Xc X1)
  refine ⟨B, by linarith, C, hC, X0, by simp [X0], ?_⟩
  intro x hx Q hQone hQ
  have hx4 : 4 ≤ x := by
    dsimp [X0] at hx
    omega
  have hxC : Xc ≤ x := by
    dsimp [X0] at hx
    omega
  have hx1 : X1 ≤ x := by
    dsimp [X0] at hx
    omega
  have hQcenter := weightedWindow_target_implies_centeredWindow hx4 hB hQ
  have hcenterBound := hcenter x hxC Q hQcenter
  have hglobalBound := hglobal x hx1
  have hglobalBound' :
      maxWeightedProgressionDiscrepancyUpTo x 1 ≤
        C1 * ((x : ℝ) /
          Real.rpow (Real.log (x : ℝ)) (A + 1)) := by
    simpa [div_eq_mul_inv, mul_assoc] using hglobalBound
  have hQsqrt : (Q : ℝ) ≤ Real.sqrt (x : ℝ) := by
    exact hQ.trans (by
      have hlogOne : 1 ≤ Real.log (x : ℝ) :=
        BoundedGaps.Maynard.one_le_log_natCast hx4
      have hpowOneR : 1 ≤ Real.rpow (Real.log (x : ℝ)) (B : ℝ) :=
        Real.one_le_rpow hlogOne (by positivity)
      have hpowOne : 1 ≤ (Real.log (x : ℝ)) ^ B := by
        rw [← Real.rpow_natCast]
        exact hpowOneR
      exact div_le_self (Real.sqrt_nonneg _) hpowOne)
  have hprefix := reciprocalTotientPrefix_lt_five_mul_log_of_le_sqrt
    hx4 (by omega : 0 < Q) hQsqrt
  have hbridge := sum_maxWeightedProgressionDiscrepancyUpTo_le_centered_add_global
    (x := x) (Q := Q) (by omega : 2 ≤ x)
  have hglobalNonneg :
      0 ≤ maxWeightedProgressionDiscrepancyUpTo x 1 :=
    maxWeightedProgressionDiscrepancyUpTo_nonneg x 1
  have hcorr :
      BoundedGaps.Maynard.reciprocalTotientPrefix Q *
          maxWeightedProgressionDiscrepancyUpTo x 1 ≤
        (5 * Real.log (x : ℝ)) *
          (C1 * ((x : ℝ) /
            Real.rpow (Real.log (x : ℝ)) (A + 1))) := by
    exact mul_le_mul hprefix.le hglobalBound' hglobalNonneg (by positivity)
  have hxlogPos : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hcorr' :
      (5 * Real.log (x : ℝ)) *
          (C1 * ((x : ℝ) /
            Real.rpow (Real.log (x : ℝ)) (A + 1))) ≤
        5 * C1 * ((x : ℝ) /
          Real.rpow (Real.log (x : ℝ)) A) := by
    have hpowAdd :
        Real.rpow (Real.log (x : ℝ)) (A + 1) =
          Real.rpow (Real.log (x : ℝ)) A * Real.log (x : ℝ) := by
      change (Real.log (x : ℝ)) ^ (A + 1) =
        (Real.log (x : ℝ)) ^ A * Real.log (x : ℝ)
      rw [Real.rpow_add hxlogPos A 1, Real.rpow_one]
    rw [hpowAdd]
    field_simp
    exact le_rfl
  calc
    (∑ q ∈ Finset.Icc 1 Q,
        maxWeightedProgressionDiscrepancyUpTo x q) ≤
        (∑ q ∈ Finset.Icc 1 Q,
          BoundedGaps.Maynard.maxCenteredProgressionDiscrepancyUpTo x q) +
          BoundedGaps.Maynard.reciprocalTotientPrefix Q *
            maxWeightedProgressionDiscrepancyUpTo x 1 := hbridge
    _ ≤ (Cc + 40 *
          BoundedGaps.Maynard.vaughanPrimitiveMeanEquationOneTwoConstant
            (Real.log 4 + 4)) * (x : ℝ) /
            Real.rpow (Real.log (x : ℝ)) A +
          (5 * Real.log (x : ℝ)) *
            (C1 * ((x : ℝ) /
              Real.rpow (Real.log (x : ℝ)) (A + 1))) := by
      exact add_le_add hcenterBound hcorr
    _ ≤ (Cc + 40 *
          BoundedGaps.Maynard.vaughanPrimitiveMeanEquationOneTwoConstant
            (Real.log 4 + 4)) * (x : ℝ) /
          Real.rpow (Real.log (x : ℝ)) A +
        5 * C1 * ((x : ℝ) /
          Real.rpow (Real.log (x : ℝ)) A) :=
      add_le_add (le_refl _) hcorr'
    _ = C * (x : ℝ) /
        Real.rpow (Real.log (x : ℝ)) A := by
      dsimp [C]
      ring

theorem unconditional_weightedBombieriVinogradov :
    weightedBombieriVinogradov := by
  intro A hA
  exact weighted_standard_sum_le_logSaving hA.le

end

end BoundedGaps.BombieriVinogradov
