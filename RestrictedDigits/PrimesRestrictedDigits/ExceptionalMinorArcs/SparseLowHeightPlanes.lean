import PrimesRestrictedDigits.ExceptionalMinorArcs.LineCauchyAggregation
import PrimesRestrictedDigits.ExceptionalMinorArcs.LineZeroCoefficientCardinality
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Sparse sets restricted to low-height planes

This completes the decimal-scale form of `MAYNARD-PRD-PUBLISHED`, Lemma 15.2, pp. 210--214, by
recombining the zero-term cover and residual estimate.
-/

open Filter

namespace PrimesRestrictedDigits

/-- The pair-level zero/residual cover gives the corresponding real
cardinality sum. -/
theorem card_lowHeightPlanePairs_real_le_zero_add_residual
    {X : Nat} (C : Finset (Fin X)) (V : Real) :
    ((lowHeightPlanePairs C V).card : Real) <=
      (zeroTermLowHeightPlanePairCover C V).card +
        (residualLowHeightPlanePairs C V).card := by
  have hcard : (lowHeightPlanePairs C V).card <=
      (zeroTermLowHeightPlanePairCover C V).card +
        (residualLowHeightPlanePairs C V).card := by
    calc
      (lowHeightPlanePairs C V).card <=
          (zeroTermLowHeightPlanePairCover C V ∪
            residualLowHeightPlanePairs C V).card :=
        Finset.card_le_card
          (lowHeightPlanePairs_subset_zeroTerm_union_residual C V)
      _ <= (zeroTermLowHeightPlanePairCover C V).card +
          (residualLowHeightPlanePairs C V).card :=
        Finset.card_union_le _ _
  exact_mod_cast hcard

private theorem sq_le_sourceFirstTerm_of_one_le_of_le
    (H V : Real) (hH : 1 <= H) (hHV : H <= V) :
    H ^ 2 <= H ^ (5 / 4 : Real) * V ^ 2 := by
  have hV : 0 <= V := (zero_le_one.trans hH).trans hHV
  have hsq : H ^ 2 <= V ^ 2 := by nlinarith
  have hpow : 1 <= H ^ (5 / 4 : Real) :=
    Real.one_le_rpow hH (by norm_num)
  calc
    H ^ 2 <= V ^ 2 := hsq
    _ = 1 * V ^ 2 := by ring
    _ <= H ^ (5 / 4 : Real) * V ^ 2 := by gcongr

/-- Explicit-quantifier decimal-scale form of published Lemma 15.2. -/
theorem exists_card_lowHeightPlanePairs_le_threshold
    (rho : Real) (hrho : 0 < rho) :
    exists length0 : Nat, forall length : Nat, length0 <= length ->
      forall (C : Finset (Fin (10 ^ length))) (V : Real), 1 <= V ->
        let X : Real := ((10 ^ length : Nat) : Real)
        let H : Real := (C.card : Real)
        ((lowHeightPlanePairs C V).card : Real) <=
          X ^ rho *
            (H ^ (5 / 4 : Real) * V ^ 2 +
              H ^ (3 / 2 : Real) * V ^ 3 /
                X ^ (1 / 2 : Real)) := by
  obtain ⟨lengthZero, hzero⟩ :=
    exists_card_zeroTermLowHeightPlanePairCover_le_threshold
      (rho / 2) (by positivity)
  obtain ⟨lengthResidual, hresidual⟩ :=
    exists_card_residualLowHeightPlanePairs_le_cauchyAggregation_threshold
      (rho / 2) (by positivity)
  have hscale :
      Tendsto (fun length : Nat => ((10 ^ length : Nat) : Real))
        atTop atTop := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      (tendsto_pow_atTop_atTop_of_one_lt
        (by norm_num : (1 : Real) < 10))
  have hgrowth :
      Tendsto
        (fun length : Nat =>
          ((10 ^ length : Nat) : Real) ^ (rho / 2))
        atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < rho / 2)).comp hscale
  obtain ⟨lengthFixed, hfixed⟩ :=
    eventually_atTop.mp (hgrowth.eventually_ge_atTop 2)
  refine ⟨max lengthZero (max lengthResidual lengthFixed), ?_⟩
  intro length hlength C V hV
  let X : Real := ((10 ^ length : Nat) : Real)
  let H : Real := (C.card : Real)
  let F : Real := X ^ (rho / 2)
  let S : Real := H ^ (5 / 4 : Real) * V ^ 2 +
    H ^ (3 / 2 : Real) * V ^ 3 / X ^ (1 / 2 : Real)
  change ((lowHeightPlanePairs C V).card : Real) <= X ^ rho * S
  have hlengthZero : lengthZero <= length := by omega
  have hlengthResidual : lengthResidual <= length := by omega
  have hlengthFixed : lengthFixed <= length := by omega
  have hX : 0 < X := by dsimp only [X]; positivity
  have hXOne : 1 <= X := by
    dsimp only [X]
    exact_mod_cast Nat.one_le_pow length 10 (by norm_num)
  have hF : 0 <= F := by dsimp only [F]; positivity
  have hS : 0 <= S := by dsimp only [S, H, X]; positivity
  have hfixedAtLength : (2 : Real) <= F := by
    simpa only [F, X] using hfixed length hlengthFixed
  by_cases hCZero : C.card = 0
  · have hcard : (lowHeightPlanePairs C V).card <= C.card ^ 2 :=
      card_lowHeightPlanePairs_le_sq C V
    have hcardReal : ((lowHeightPlanePairs C V).card : Real) <=
        (C.card : Real) ^ 2 := by
      exact_mod_cast hcard
    calc
      ((lowHeightPlanePairs C V).card : Real) <=
          (C.card : Real) ^ 2 := hcardReal
      _ = 0 := by simp [hCZero]
      _ <= X ^ rho * S := mul_nonneg (Real.rpow_nonneg hX.le rho) hS
  · have hHOne : 1 <= H := by
      dsimp only [H]
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hCZero)
    have hcardAmbient : C.card <= 10 ^ length := by
      calc
        C.card <= Fintype.card (Fin (10 ^ length)) :=
          Finset.card_le_univ C
        _ = 10 ^ length := Fintype.card_fin _
    have hHX : H <= X := by
      dsimp only [H, X]
      exact_mod_cast hcardAmbient
    by_cases hVX : V < X
    · have hzeroBound :
          ((zeroTermLowHeightPlanePairCover C V).card : Real) <=
            F * H * V ^ 2 := by
        simpa only [F, X, H] using
          hzero length hlengthZero C V hV hVX
      have hresidualBound :
          ((residualLowHeightPlanePairs C V).card : Real) <= F * S := by
        simpa only [F, X, H, S] using
          hresidual length hlengthResidual C V hV hVX
      have hHPow : H <= H ^ (5 / 4 : Real) := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hHOne (by norm_num :
            (1 : Real) <= 5 / 4)
      have hzeroTermLe : H * V ^ 2 <= S := by
        calc
          H * V ^ 2 <= H ^ (5 / 4 : Real) * V ^ 2 :=
            mul_le_mul_of_nonneg_right hHPow (sq_nonneg V)
          _ <= S := by
            dsimp only [S]
            exact le_add_of_nonneg_right (by positivity)
      have hzeroSource :
          ((zeroTermLowHeightPlanePairCover C V).card : Real) <= F * S := by
        calc
          ((zeroTermLowHeightPlanePairCover C V).card : Real) <=
              F * H * V ^ 2 := hzeroBound
          _ = F * (H * V ^ 2) := by ring
          _ <= F * S := mul_le_mul_of_nonneg_left hzeroTermLe hF
      have hFF : F * F = X ^ rho := by
        dsimp only [F]
        rw [← Real.rpow_add hX]
        congr 1
        ring
      calc
        ((lowHeightPlanePairs C V).card : Real) <=
            (zeroTermLowHeightPlanePairCover C V).card +
              (residualLowHeightPlanePairs C V).card :=
          card_lowHeightPlanePairs_real_le_zero_add_residual C V
        _ <= F * S + F * S := add_le_add hzeroSource hresidualBound
        _ = 2 * (F * S) := by ring
        _ <= F * (F * S) :=
          mul_le_mul_of_nonneg_right hfixedAtLength (mul_nonneg hF hS)
        _ = X ^ rho * S := by rw [← mul_assoc, hFF]
    · have hXV : X <= V := le_of_not_gt hVX
      have hHV : H <= V := hHX.trans hXV
      have hcard : (lowHeightPlanePairs C V).card <= C.card ^ 2 :=
        card_lowHeightPlanePairs_le_sq C V
      have hcardReal : ((lowHeightPlanePairs C V).card : Real) <=
          H ^ 2 := by
        dsimp only [H]
        exact_mod_cast hcard
      have htrivial : H ^ 2 <= H ^ (5 / 4 : Real) * V ^ 2 :=
        sq_le_sourceFirstTerm_of_one_le_of_le H V hHOne hHV
      have hfirstLe : H ^ (5 / 4 : Real) * V ^ 2 <= S := by
        dsimp only [S]
        exact le_add_of_nonneg_right (by positivity)
      have hXRho : 1 <= X ^ rho :=
        Real.one_le_rpow hXOne hrho.le
      calc
        ((lowHeightPlanePairs C V).card : Real) <= H ^ 2 := hcardReal
        _ <= H ^ (5 / 4 : Real) * V ^ 2 := htrivial
        _ <= S := hfirstLe
        _ = 1 * S := by ring
        _ <= X ^ rho * S := mul_le_mul_of_nonneg_right hXRho hS

end PrimesRestrictedDigits
