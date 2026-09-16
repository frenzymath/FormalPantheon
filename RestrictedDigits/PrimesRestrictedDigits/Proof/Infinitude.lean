import PrimesRestrictedDigits.Statement
import PrimesRestrictedDigits.Proof.MainTheorem
import PrimesRestrictedDigits.Foundations.PowerLaw
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
/-! # Infinitude -/

namespace PrimesRestrictedDigits

/- The lower link in Theorem 1.1 makes the prime set unbounded: for a finite
   set, choose a cutoff whose power-law quotient exceeds its largest element.
   The auxiliary growth lemma is elementary and uses the standard fact that
   every positive power eventually dominates the logarithm. -/
private lemma exists_rpow_div_log_gt_inf {a M : Real} (ha : 0 < a) :
    ∃ X : Real, 4 ≤ X ∧ M < X ^ a / Real.log X := by
  let r : Real := a / 2
  have hr : 0 < r := by
    dsimp [r]
    linarith
  have hsmall := (isLittleO_log_rpow_atTop hr).bound
    (show 0 < (1 / 2 : Real) by norm_num)
  obtain ⟨E, hE⟩ := Filter.eventually_atTop.1 hsmall
  have hBEvent :=
    Filter.tendsto_atTop.1 (tendsto_rpow_atTop hr) (max (M / 2 + 1) 1)
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.mp hBEvent
  let X : Real := max 4 (max E B)
  have hXE : E ≤ X := by
    dsimp [X]
    exact (le_max_left E B).trans (le_max_right 4 (max E B))
  have hXB : B ≤ X := by
    dsimp [X]
    exact (le_max_right E B).trans (le_max_right 4 (max E B))
  have hX4 : 4 ≤ X := by
    dsimp [X]
    exact le_max_left _ _
  have hlogBound := hE X hXE
  have hrpowBound := hB X hXB
  have hXone : 1 < X := lt_of_lt_of_le (by norm_num) hX4
  have hXpos : 0 < X := by linarith
  have hlogPos : 0 < Real.log X := Real.log_pos hXone
  have hlogNonneg : 0 ≤ Real.log X := hlogPos.le
  have hpowNonneg : 0 ≤ X ^ r := Real.rpow_nonneg hXpos.le _
  have hlogHalf : Real.log X ≤ (1 / 2 : Real) * X ^ r := by
    simpa only [Real.norm_of_nonneg hlogNonneg, Real.norm_of_nonneg hpowNonneg,
      one_div] using hlogBound
  have hpowLarge : M / 2 < X ^ r := by
    have hthreshold : M / 2 + 1 ≤ X ^ r :=
      (le_max_left (M / 2 + 1) 1).trans hrpowBound
    have hMhalf : M / 2 < M / 2 + 1 := by linarith
    exact lt_of_lt_of_le hMhalf hthreshold
  have hratio : 2 * X ^ r ≤ X ^ a / Real.log X := by
    have hpowA : X ^ a = (X ^ r) * (X ^ r) := by
      dsimp [r]
      rw [← Real.rpow_add hXpos]
      congr 1
      ring
    rw [hpowA]
    apply (le_div_iff₀ hlogPos).2
    have hmul := mul_le_mul_of_nonneg_left hlogHalf
      (by positivity : 0 ≤ 2 * X ^ r)
    calc
      2 * X ^ r * Real.log X ≤
          2 * X ^ r * ((1 / 2 : Real) * X ^ r) := hmul
      _ = X ^ r * X ^ r := by ring
  have hM : M < 2 * X ^ r := by
    nlinarith [hpowLarge]
  exact ⟨X, hX4, hM.trans_le hratio⟩

/- Infinitude follows from the lower bound in Maynard's Theorem 1.1. -/
theorem infinitudeCorollary_of_quantitativeTheorem
    (hquant : quantitativeTheorem) : infinitudeCorollary := by
  classical
  rcases hquant with ⟨c1, c2, c3, c4, hc1, hc2, hc3, hc4, hbound⟩
  intro a
  by_contra hnot
  have hfinite : Set.Finite {p : Nat | p.Prime ∧ omitsDecimalDigit a p} :=
    Set.not_infinite.mp hnot
  rcases hfinite.bddAbove with ⟨B, hB⟩
  let alpha : Real := Real.log (9 : Real) / Real.log (10 : Real)
  have hlog9 : 0 < Real.log (9 : Real) := Real.log_pos (by norm_num)
  have hlog10 : 0 < Real.log (10 : Real) := Real.log_pos (by norm_num)
  have halpha : 0 < alpha := by
    dsimp [alpha]
    positivity
  let M : Real := ((B : Real) + 1) / (c1 * c3)
  have hMpos : 0 < M := by
    dsimp [M]
    positivity
  obtain ⟨X, hX4, hgrowth⟩ :=
    exists_rpow_div_log_gt_inf (a := alpha) (M := M) halpha
  have hlinks := hbound a X hX4
  have hlogPos : 0 < Real.log X := Real.log_pos (by linarith)
  have hprod : c1 * c3 * (X ^ alpha / Real.log X) <
      (restrictedPrimeCount a X : Real) := by
    calc
      c1 * c3 * (X ^ alpha / Real.log X) =
          c1 * (c3 * (X ^ alpha / Real.log X)) := by ring
      _ < c1 * ((restrictedCount a X : Real) / Real.log X) :=
        mul_lt_mul_of_pos_left hlinks.2.2.1 hc1
      _ < (restrictedPrimeCount a X : Real) := hlinks.1
  have hMidentity : (B : Real) + 1 = c1 * c3 * M := by
    dsimp [M]
    field_simp [hc1.ne', hc3.ne']
  have hBplus : (B : Real) + 1 <
      (restrictedPrimeCount a X : Real) := by
    calc
      (B : Real) + 1 = c1 * c3 * M := hMidentity
      _ < c1 * c3 * (X ^ alpha / Real.log X) :=
        mul_lt_mul_of_pos_left hgrowth (mul_pos hc1 hc3)
      _ < (restrictedPrimeCount a X : Real) := hprod
  let P : Finset Nat := (restrictedNumbers a X).filter Nat.Prime
  have hPsub : P ⊆ Finset.range (B + 1) := by
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    have hpNumber := mem_restrictedNumbers.mp hpData.1
    have hpSet : p ∈ {p : Nat | p.Prime ∧ omitsDecimalDigit a p} :=
      ⟨hpData.2, hpNumber.2⟩
    have hpBound := hB hpSet
    rw [Finset.mem_range]
    omega
  have hPcard : P.card ≤ B + 1 := by
    exact (Finset.card_le_card hPsub).trans_eq (Finset.card_range _)
  have hPcardReal : (restrictedPrimeCount a X : Real) ≤ (B : Real) + 1 := by
    change (P.card : Real) ≤ (B : Real) + 1
    exact_mod_cast hPcard
  exact (not_lt_of_ge hPcardReal) hBplus

/-- Infinitely many primes omit each prescribed decimal digit, by the quantitative theorem. -/
theorem infinitude : infinitudeCorollary :=
  infinitudeCorollary_of_quantitativeTheorem mainTheorem

end PrimesRestrictedDigits
