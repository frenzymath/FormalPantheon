import Waring.Analytic.ChenTenArcs
import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
# Reduced approximations on Chen's minor arcs

This is the rational-approximation step in Chen's final minor-arc argument
[CHEN1964-EN, pp. 1567-1568; CHEN1964-ZH, pp. 733-734].
-/

set_option autoImplicit false

namespace Waring.Analytic

open Set

noncomputable section

/-- Every point of Chen's minor arcs has a reduced Dirichlet approximation
whose denominator lies beyond the major-arc cutoff. -/
theorem exists_reducedDirichletApproximation_of_mem_chenTenMinorArcs
    {P : Nat} (hP : 0 < P) {alpha : Real}
    (halpha : alpha ∈ chenTenMinorArcs P) :
    ∃ q a : Nat, ∃ epsilon : Real,
      0 < q ∧ a < q ∧ Nat.Coprime a q ∧
        IsUnit (a : ZMod q) ∧
        (P : Real) ^ (1 / 2 : Real) ≤ q ∧
        (q : Real) ≤ 10 * (P : Real) ^ 4 ∧
        alpha = (a : Real) / q + epsilon ∧
        |epsilon| ≤ 1 / (10 * (q : Real) * (P : Real) ^ 4) := by
  let n : Nat := 10 * P ^ 4
  have hnPos : 0 < n := by
    dsimp [n]
    positivity
  obtain ⟨r, hrApprox, hrDen⟩ :=
    Real.exists_rat_abs_sub_le_and_den_le alpha hnPos
  have htauPos : 0 < chenTenArcScale P := chenTenArcScale_pos hP
  have hdenPos : (0 : Real) < r.den := by
    exact_mod_cast Rat.den_pos r
  have hnCast : (n : Real) = chenTenArcScale P := by
    simp [n, chenTenArcScale]
  have hcoarse :
      1 / (((n : Real) + 1) * (r.den : Real)) ≤
        1 / chenTenArcScale P := by
    apply one_div_le_one_div_of_le htauPos
    rw [← hnCast]
    have hdenOne : (1 : Real) ≤ r.den := by
      exact_mod_cast Rat.den_pos r
    calc
      (n : Real) ≤ (n : Real) + 1 := by linarith
      _ = ((n : Real) + 1) * 1 := by ring
      _ ≤ ((n : Real) + 1) * (r.den : Real) := by
        gcongr
  have hrApproxCoarse :
      |alpha - (r : Real)| ≤ 1 / chenTenArcScale P :=
    hrApprox.trans hcoarse
  have hfund := halpha.1
  have hfundLower : chenTenArcLeftEndpoint P ≤ alpha := hfund.1
  have hfundUpper : alpha < chenTenArcRightEndpoint P := hfund.2
  have halphaBeyondZero : (chenTenArcScale P)⁻¹ < alpha := by
    by_contra hnot
    have halphaUpper : alpha ≤ (chenTenArcScale P)⁻¹ := le_of_not_gt hnot
    have hzeroArc : alpha ∈ chenTenArc P (chenTenZeroArcIndex P hP) := by
      rw [chenTenZeroArc_eq P hP]
      exact ⟨hfundLower, halphaUpper⟩
    exact halpha.2
      (Set.mem_iUnion.2 ⟨chenTenZeroArcIndex P hP, hzeroArc⟩)
  have hrNonneg : (0 : Rat) ≤ r := by
    by_contra hnot
    have hrNeg : (r : Real) < 0 := by
      exact_mod_cast (lt_of_not_ge hnot)
    have hdiffNonneg : 0 ≤ alpha - (r : Real) := by
      have : 0 < alpha := lt_trans (inv_pos.mpr htauPos) halphaBeyondZero
      linarith
    have halphaLe : alpha ≤ |alpha - (r : Real)| := by
      rw [abs_of_nonneg hdiffNonneg]
      linarith
    have : alpha ≤ (chenTenArcScale P)⁻¹ := by
      simpa only [one_div] using halphaLe.trans hrApproxCoarse
    exact (not_le_of_gt halphaBeyondZero) this
  have hrLtOne : r < 1 := by
    by_contra hnot
    have hrOne : (1 : Real) ≤ r := by
      exact_mod_cast (le_of_not_gt hnot)
    have hright :
        alpha < 1 - (chenTenArcScale P)⁻¹ := by
      simpa only [chenTenArcRightEndpoint] using hfundUpper
    have hinvPos : 0 < (chenTenArcScale P)⁻¹ := inv_pos.mpr htauPos
    have hdiffNonpos : alpha - (r : Real) ≤ 0 := by linarith
    have hgap : (chenTenArcScale P)⁻¹ < |alpha - (r : Real)| := by
      rw [abs_of_nonpos hdiffNonpos]
      linarith
    exact (not_lt_of_ge (by simpa only [one_div] using hrApproxCoarse)) hgap
  let s : NNRat := ⟨r, hrNonneg⟩
  let a : Nat := s.num
  let q : Nat := s.den
  have hqPos : 0 < q := by
    exact s.den_pos
  have haLt : a < q := by
    have hnumLt : (s.num : Int) < (s.den : Int) := by
      rw [← NNRat.num_coe, ← NNRat.den_coe]
      exact Rat.num_lt_denom_iff.2 hrLtOne
    exact_mod_cast hnumLt
  have haCoprime : Nat.Coprime a q := by
    exact s.coprime_num_den
  have haUnit : IsUnit (a : ZMod q) := by
    exact (ZMod.isUnit_iff_coprime a q).2 haCoprime
  have hrCast : (r : Real) = (a : Real) / q := by
    change ((s : NNRat) : Real) = (a : Real) / q
    rw [NNRat.cast_def]
  let epsilon : Real := alpha - (a : Real) / q
  have hepsilon :
      |epsilon| ≤ 1 / (10 * (q : Real) * (P : Real) ^ 4) := by
    dsimp [epsilon]
    rw [← hrCast]
    have hdirichlet :
        |alpha - (r : Real)| ≤
          1 / (((n : Real) + 1) * (q : Real)) := by
      simpa [q, s] using hrApprox
    have hdenominator :
        10 * (q : Real) * (P : Real) ^ 4 ≤
          ((n : Real) + 1) * (q : Real) := by
      rw [show 10 * (q : Real) * (P : Real) ^ 4 =
          (n : Real) * q by rw [hnCast]; unfold chenTenArcScale; ring]
      gcongr
      linarith
    exact hdirichlet.trans
      (one_div_le_one_div_of_le (by positivity) hdenominator)
  have hqUpper : (q : Real) ≤ 10 * (P : Real) ^ 4 := by
    have hqNat : q ≤ n := by
      simpa [q, s] using hrDen
    calc
      (q : Real) ≤ n := by exact_mod_cast hqNat
      _ = 10 * (P : Real) ^ 4 := by simp [n]
  have hqSqNot : ¬ q ^ 2 ≤ P := by
    intro hqSq
    have hqLeP : q ≤ P := by
      calc
        q ≤ q ^ 2 := by nlinarith
        _ ≤ P := hqSq
    have haLeP : a ≤ P := (Nat.le_of_lt haLt).trans hqLeP
    let i : ChenTenArcIndex P :=
      ⟨(⟨a, by omega⟩, ⟨q, by omega⟩), hqPos, haLt, haCoprime, hqSq⟩
    have hmemArc : alpha ∈ chenTenArc P i := by
      change alpha ∈ Set.Icc
        ((a : Real) / q - 1 / ((q : Real) * chenTenArcScale P))
        ((a : Real) / q + 1 / ((q : Real) * chenTenArcScale P))
      have habs :
          |epsilon| ≤ 1 / ((q : Real) * chenTenArcScale P) := by
        rw [chenTenArcScale]
        have hmul :
            (q : Real) * (10 * (P : Real) ^ 4) =
              10 * (q : Real) * (P : Real) ^ 4 := by ring
        rw [hmul]
        exact hepsilon
      have hbounds := abs_le.mp habs
      dsimp [epsilon] at hbounds
      exact ⟨by linarith, by linarith⟩
    exact halpha.2 (Set.mem_iUnion.2 ⟨i, hmemArc⟩)
  have hqLower : (P : Real) ^ (1 / 2 : Real) ≤ q := by
    rw [← Real.sqrt_eq_rpow]
    rw [Real.sqrt_le_iff]
    exact ⟨by positivity,
      by exact_mod_cast (Nat.le_of_lt (lt_of_not_ge hqSqNot))⟩
  refine ⟨q, a, epsilon, hqPos, haLt, haCoprime, haUnit,
    hqLower, hqUpper, ?_, hepsilon⟩
  dsimp [epsilon]
  ring

end

end Waring.Analytic
