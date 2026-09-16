import PrimesRestrictedDigits.BasicEstimates.DecimalDivisorBound
import PrimesRestrictedDigits.ExceptionalMinorArcs.LineCongruenceHeightClassFibers
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Quantitative source congruence height-class cardinality

This proves the coefficient-one eventual form of `#C(A,M) <= X^(o(1)) min(#C,M^2)` from
`MAYNARD-PRD-PUBLISHED`, Lemma 15.2, pp. 211--212, for the repaired sup-height classes.
-/

open Filter

namespace PrimesRestrictedDigits

private theorem lineCongruencePair_target_natAbs_le_two_mul_sq
    {X M : Nat} {c : Prod Int Int}
    (hX : 1 <= X) (hMX : M <= X)
    (hc : c ∈ lineCongruencePairBox M) :
    ((c.1 - c.2 * (X : Int)).natAbs : Real) <=
      2 * ((X : Real) ^ 2) := by
  rw [lineCongruencePairBox, Finset.product_eq_sprod,
    Finset.mem_product] at hc
  simp only [Finset.mem_Icc] at hc
  have hc1Int : abs c.1 <= (M : Int) := abs_le.mpr hc.1
  have hc2Int : abs c.2 <= (M : Int) := abs_le.mpr hc.2
  have hc1 : abs (c.1 : Real) <= (M : Real) := by
    exact_mod_cast hc1Int
  have hc2 : abs (c.2 : Real) <= (M : Real) := by
    exact_mod_cast hc2Int
  have hMXReal : (M : Real) <= X := by exact_mod_cast hMX
  have hXReal : (1 : Real) <= X := by exact_mod_cast hX
  rw [Nat.cast_natAbs, Int.cast_abs]
  push_cast
  calc
    abs ((c.1 : Real) - (c.2 : Real) * X) <=
        abs (c.1 : Real) + abs ((c.2 : Real) * X) := abs_sub _ _
    _ = abs (c.1 : Real) + abs (c.2 : Real) * X := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : Real) <= X)]
    _ <= (M : Real) + (M : Real) * X := by gcongr
    _ <= X + X * X := by gcongr
    _ <= 2 * X ^ 2 := by nlinarith

/-- Uniform coefficient-one form of the source height-class estimate. The
threshold depends only on the requested positive exponent. -/
theorem exists_card_lineCongruenceHeightClass_le_threshold
    (rho : Real) (hrho : 0 < rho) :
    exists length0 : Nat, forall length : Nat, length0 <= length ->
      forall (C : Finset (Fin (10 ^ length)))
        (j : Prod (Fin (length + 1)) (Fin (length + 1))),
        ((lineCongruenceHeightClass length C j).card : Real) <=
          (((10 ^ length : Nat) : Real) ^ rho) *
            min (C.card : Real)
              (((10 ^ j.2.val : Nat) : Real) ^ 2) := by
  obtain ⟨lengthDivisor, hdivisor⟩ :=
    exists_card_int_divisorsAntidiag_le_decimalPower_rpow_threshold
      (rho / 2) 2 2 (by positivity) (by norm_num)
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
    eventually_atTop.mp (hgrowth.eventually_ge_atTop 9)
  refine ⟨max lengthDivisor lengthFixed, ?_⟩
  intro length hlength C j
  let X : Nat := 10 ^ length
  let M : Nat := 10 ^ j.2.val
  let XR : Real := (X : Real)
  let MR : Real := (M : Real)
  have hlengthDivisor : lengthDivisor <= length :=
    (le_max_left _ _).trans hlength
  have hlengthFixed : lengthFixed <= length :=
    (le_max_right _ _).trans hlength
  have hXOne : 1 <= X := by
    dsimp only [X]
    exact one_le_pow₀ (by norm_num)
  have hMX : M <= X := by
    dsimp only [M, X]
    exact Nat.pow_le_pow_right (by norm_num) j.2.is_le
  have hdivisorAtScale : forall c : Prod Int Int,
      c ∈ lineCongruencePairBox M ->
      ((c.1 - c.2 * (X : Int)).divisorsAntidiag.card : Real) <=
        XR ^ (rho / 2) := by
    intro c hc
    apply hdivisor length hlengthDivisor
    simpa only [X, XR] using
      lineCongruencePair_target_natAbs_le_two_mul_sq hXOne hMX hc
  have hfinite :
      ((lineCongruenceHeightClass length C j).card : Real) <=
        ((lineCongruencePairBox M).card : Real) * XR ^ (rho / 2) := by
    simpa only [M, X, XR] using
      lineCongruenceHeightClass_card_real_le_box_mul C j
        (XR ^ (rho / 2)) hdivisorAtScale
  have hMOne : 1 <= M := by
    dsimp only [M]
    exact one_le_pow₀ (by norm_num)
  have hbox :
      ((lineCongruencePairBox M).card : Real) <= 9 * MR ^ 2 := by
    rw [card_lineCongruencePairBox]
    dsimp only [MR]
    push_cast
    have hMReal : (1 : Real) <= M := by exact_mod_cast hMOne
    nlinarith [sq_nonneg (2 * (M : Real) + 1),
      sq_nonneg (3 * (M : Real))]
  have hfixedAtScale : (9 : Real) <= XR ^ (rho / 2) := by
    simpa only [X, XR] using hfixed length hlengthFixed
  have hXPos : 0 < XR := by
    dsimp only [XR, X]
    positivity
  have hHalfNonneg : 0 <= XR ^ (rho / 2) :=
    Real.rpow_nonneg hXPos.le _
  have hclassM :
      ((lineCongruenceHeightClass length C j).card : Real) <=
        XR ^ rho * MR ^ 2 := by
    calc
      ((lineCongruenceHeightClass length C j).card : Real) <=
          ((lineCongruencePairBox M).card : Real) * XR ^ (rho / 2) :=
        hfinite
      _ <= (9 * MR ^ 2) * XR ^ (rho / 2) := by gcongr
      _ <= (XR ^ (rho / 2) * MR ^ 2) * XR ^ (rho / 2) := by
        gcongr
      _ = (XR ^ (rho / 2) * XR ^ (rho / 2)) * MR ^ 2 := by ring
      _ = XR ^ rho * MR ^ 2 := by
        rw [← Real.rpow_add hXPos]
        congr 2
        ring
  have hXrhoOne : (1 : Real) <= XR ^ rho := by
    apply Real.one_le_rpow
    · dsimp only [XR]
      exact_mod_cast hXOne
    · exact hrho.le
  have hclassC :
      ((lineCongruenceHeightClass length C j).card : Real) <=
        XR ^ rho * (C.card : Real) := by
    calc
      ((lineCongruenceHeightClass length C j).card : Real) <=
          (C.card : Real) := by
        exact_mod_cast lineCongruenceHeightClass_card_le_ambient length C j
      _ = 1 * (C.card : Real) := by ring
      _ <= XR ^ rho * (C.card : Real) := by gcongr
  dsimp only [X, M, XR, MR] at hclassM hclassC ⊢
  rw [mul_min_of_nonneg _ _ (Real.rpow_nonneg (by positivity) rho)]
  exact le_min hclassC hclassM

end PrimesRestrictedDigits
