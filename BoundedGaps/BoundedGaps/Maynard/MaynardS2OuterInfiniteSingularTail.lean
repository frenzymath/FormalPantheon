import BoundedGaps.Maynard.MaynardS2OuterSingularApproximation
import Mathlib.Analysis.SpecialFunctions.Log.Summable

noncomputable section

/-!
# Infinite S2 outer singular-series tail

The outer local corrections from Maynard2013v3, source lines 552--560, are
summable.  This file passes from the audited finite tails to their infinite
product and preserves the uniform `8/D` bound.
-/

namespace BoundedGaps.Maynard

open Filter

noncomputable def maynardS2OuterSingularSequenceFactor
    (D n : ℕ) : ℝ :=
  if n.Prime ∧ D < n then maynardS2OuterSingularLocalFactor n else 1

noncomputable def maynardS2OuterInfiniteSingularTail (D : ℕ) : ℝ :=
  ∏' n : ℕ, maynardS2OuterSingularSequenceFactor D n

theorem maynardS2OuterSingularSequenceFactor_multipliable
    {D : ℕ} (hD : 2 ≤ D) :
    Multipliable (maynardS2OuterSingularSequenceFactor D) := by
  let f : ℕ → ℝ := fun n =>
    if n.Prime ∧ D < n then -maynardS2OuterSingularCorrection n else 0
  have hbase : Summable (fun n : ℕ => 4 * ((1 : ℝ) / (n : ℝ) ^ 2)) := by
    exact (Real.summable_one_div_nat_pow.mpr (by omega)).mul_left 4
  have hsum : Summable f := hbase.of_norm_bounded (fun n => by
    by_cases hn : n.Prime ∧ D < n
    · dsimp [f]
      rw [if_pos hn]
      have hn3 : 3 ≤ n := by omega
      have hcorr := (maynardS2OuterSingularCorrection_prime_bounds
        hn.1 hn3).2
      have hprime := one_div_totient_prime_sq_le_four_div_prime_sq hn.1
      rw [abs_neg,
        abs_of_nonneg (maynardS2OuterSingularCorrection_prime_bounds
          hn.1 hn3).1]
      exact hcorr.trans hprime
    · simp [f, hn])
  have hmult := Real.multipliable_one_add_of_summable hsum
  apply hmult.congr
  intro n
  by_cases hn : n.Prime ∧ D < n
  · rw [show f n = -maynardS2OuterSingularCorrection n by simp [f, hn]]
    rw [maynardS2OuterSingularSequenceFactor,
      if_pos hn,
      maynardS2OuterSingularLocalFactor_prime_eq hn.1 (by omega)]
    ring
  · simp [f, maynardS2OuterSingularSequenceFactor, hn]

theorem prod_range_maynardS2OuterSingularSequenceFactor_eq
    (D Q : ℕ) :
    (∏ n ∈ Finset.range Q,
      maynardS2OuterSingularSequenceFactor D n) =
      maynardS2OuterSingularTail D Q := by
  unfold maynardS2OuterSingularSequenceFactor
    maynardS2OuterSingularTail
  rw [← Finset.prod_filter]
  apply Finset.prod_congr
  · ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨hnQ, hnPrime, hDn⟩
      exact ⟨⟨by omega, hnQ⟩, hnPrime⟩
    · rintro ⟨⟨hDn, hnQ⟩, hnPrime⟩
      exact ⟨hnQ, hnPrime, by omega⟩
  · intro n hn
    rfl

theorem tendsto_maynardS2OuterSingularTail
    {D : ℕ} (hD : 2 ≤ D) :
    Tendsto (fun Q => maynardS2OuterSingularTail D Q) atTop
      (nhds (maynardS2OuterInfiniteSingularTail D)) := by
  have hprod :=
    (maynardS2OuterSingularSequenceFactor_multipliable hD).hasProd
      |>.tendsto_prod_nat
  exact hprod.congr' (Eventually.of_forall fun Q =>
    prod_range_maynardS2OuterSingularSequenceFactor_eq D Q)

theorem abs_maynardS2OuterInfiniteSingularTail_sub_one_le
    {D : ℕ} (hD : 2 ≤ D) :
    |maynardS2OuterInfiniteSingularTail D - 1| ≤ 8 / (D : ℝ) := by
  have hlim := (tendsto_maynardS2OuterSingularTail hD).sub_const 1 |>.abs
  exact le_of_tendsto hlim (Eventually.of_forall fun Q =>
    abs_maynardS2OuterSingularTail_sub_one_le hD)

end BoundedGaps.Maynard
