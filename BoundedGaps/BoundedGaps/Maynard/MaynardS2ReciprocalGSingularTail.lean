import BoundedGaps.Maynard.MaynardS2ReciprocalGCorrectionEndpoint
import Mathlib.Analysis.SpecialFunctions.Log.Summable

noncomputable section

/-!
# Finite and infinite reciprocal-g singular tails

The reciprocal-g correction factors are `1 + 1/(p*(p-2))` outside the
pre-sieve. This module proves convergence and a uniform deviation estimate.
See `SEM-358`.
-/

namespace BoundedGaps.Maynard

open Finset Nat Filter
open scoped BigOperators

private noncomputable def maynardS2ReciprocalGSingularCorrection (p : ℕ) : ℝ :=
  (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 2))

noncomputable def maynardS2ReciprocalGSingularTail (D Q : ℕ) : ℝ :=
  ∏ p ∈ (Finset.Ico (D + 1) Q).filter Nat.Prime,
    maynardS2ReciprocalGSingularLocalFactor p

private theorem maynardS2ReciprocalGSingularSequenceFactor_multipliable
    {D : ℕ} (hD : 2 ≤ D) :
    Multipliable (maynardS2ReciprocalGSingularSequenceFactor D) := by
  let f : ℕ → ℝ := fun n =>
    if n.Prime ∧ D < n then
      maynardS2ReciprocalGSingularCorrection n else 0
  have hbase : Summable (fun n : ℕ => 4 / (n : ℝ) ^ 2) := by
    simpa [div_eq_mul_inv] using
      (Real.summable_one_div_nat_pow.mpr (by omega)).mul_left 4
  have hsum : Summable f := hbase.of_norm_bounded (fun n => by
    by_cases hn : n.Prime ∧ D < n
    · dsimp [f]
      rw [if_pos hn]
      have hn3 : 3 ≤ n := by omega
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn.1.pos
      have hn3R : (3 : ℝ) ≤ n := by exact_mod_cast hn3
      have hnm2 : 0 < (n : ℝ) - 2 := by linarith
      have hden : 0 < (n : ℝ) * ((n : ℝ) - 2) :=
        mul_pos hnR hnm2
      unfold maynardS2ReciprocalGSingularCorrection
      rw [abs_of_nonneg (by positivity)]
      rw [div_le_div_iff₀ hden (sq_pos_of_pos hnR)]
      nlinarith [sq_nonneg (n : ℝ)]
    · simp [f, hn]
      positivity)
  have hmult := Real.multipliable_one_add_of_summable hsum
  apply hmult.congr
  intro n
  by_cases hn : n.Prime ∧ D < n
  · rw [show f n = maynardS2ReciprocalGSingularCorrection n by
        simp [f, hn]]
    rw [maynardS2ReciprocalGSingularSequenceFactor,
      if_pos hn]
    unfold maynardS2ReciprocalGSingularLocalFactor
      maynardS2ReciprocalGSingularCorrection
    ring
  · simp [f, maynardS2ReciprocalGSingularSequenceFactor, hn]

theorem prod_range_maynardS2ReciprocalGSingularSequenceFactor_eq
    (D Q : ℕ) :
    (∏ n ∈ Finset.range Q,
      maynardS2ReciprocalGSingularSequenceFactor D n) =
      maynardS2ReciprocalGSingularTail D Q := by
  unfold maynardS2ReciprocalGSingularSequenceFactor
    maynardS2ReciprocalGSingularTail
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

theorem tendsto_maynardS2ReciprocalGSingularTail
    {D : ℕ} (hD : 2 ≤ D) :
    Tendsto (fun Q => maynardS2ReciprocalGSingularTail D Q) atTop
      (nhds (maynardS2ReciprocalGInfiniteSingularTail D)) := by
  have hprod :=
    (maynardS2ReciprocalGSingularSequenceFactor_multipliable hD).hasProd
      |>.tendsto_prod_nat
  exact hprod.congr' (Eventually.of_forall fun Q =>
    prod_range_maynardS2ReciprocalGSingularSequenceFactor_eq D Q)

private theorem maynardS2ReciprocalGSingularCorrection_sum_le
    {D Q : ℕ} (hD : 2 ≤ D) :
    (∑ p ∈ (Finset.Ico (D + 1) Q).filter Nat.Prime,
      maynardS2ReciprocalGSingularCorrection p) ≤
      16 / (D : ℝ) := by
  let P := (Finset.Ico (D + 1) Q).filter Nat.Prime
  have hsum : (∑ p ∈ P,
      maynardS2ReciprocalGSingularCorrection p) ≤
      ∑ p ∈ P, 2 * primeTotientSquareWeight p := by
    apply Finset.sum_le_sum
    intro p hp
    have hpPrime := (Finset.mem_filter.mp hp).2
    have hpLower : D + 1 ≤ p :=
      (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1
    have hp3 : 3 ≤ p := by omega
    have hc := maynardS2ReciprocalGCorrection_square_coeff_le hpPrime hp3
    have hcast : ((p - 2 : ℕ) : ℝ) = (p : ℝ) - 2 := by
      rw [Nat.cast_sub hpPrime.two_le]
      norm_num
    have hc' : maynardS2ReciprocalGSingularCorrection p ≤
        2 * primeTotientSquareWeight p := by
      simpa [maynardS2ReciprocalGSingularCorrection, hcast] using hc.2
    exact hc'
  calc
    (∑ p ∈ (Finset.Ico (D + 1) Q).filter Nat.Prime,
        maynardS2ReciprocalGSingularCorrection p) ≤
        ∑ p ∈ P, 2 * primeTotientSquareWeight p := hsum
    _ = 2 * primeTotientSquareTail D Q := by
      simp [P, primeTotientSquareTail, primeTotientSquareWeight,
        Finset.mul_sum]
    _ ≤ 16 / (D : ℝ) := by
      have htail := primeTotientSquareTail_le (D := D) (Q := Q)
        (by omega : 0 < D)
      calc
        2 * primeTotientSquareTail D Q ≤
            2 * (8 / (D : ℝ)) :=
          mul_le_mul_of_nonneg_left htail (by norm_num)
        _ = 16 / (D : ℝ) := by ring

theorem abs_maynardS2ReciprocalGSingularTail_sub_one_le
    {D Q : ℕ} (hD : 2 ≤ D) :
    |maynardS2ReciprocalGSingularTail D Q - 1| ≤
      Real.exp (16 / (D : ℝ)) - 1 := by
  let P := (Finset.Ico (D + 1) Q).filter Nat.Prime
  let c := maynardS2ReciprocalGSingularCorrection
  have hc0 : ∀ p ∈ P, 0 ≤ c p := by
    intro p hp
    have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2
    have hpLower : D + 1 ≤ p :=
      (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1
    have hp3 : 3 ≤ p := by omega
    have hden : 0 < (p : ℝ) * ((p : ℝ) - 2) := by
      have hpR : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
      have hp3R : (3 : ℝ) ≤ p := by exact_mod_cast hp3
      exact mul_pos hpR (by linarith)
    unfold c maynardS2ReciprocalGSingularCorrection
    exact (one_div_pos.mpr hden).le
  have hfactor : maynardS2ReciprocalGSingularTail D Q =
      ∏ p ∈ P, (1 + c p) := by
    unfold maynardS2ReciprocalGSingularTail
      maynardS2ReciprocalGSingularLocalFactor c
    rfl
  have hdev := Finset.norm_prod_one_add_sub_one_le P c
  have hnorm : (∑ p ∈ P, ‖c p‖) = ∑ p ∈ P, c p := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (hc0 p hp)]
  have hsum : (∑ p ∈ P, ‖c p‖) ≤ 16 / (D : ℝ) := by
    rw [hnorm]
    exact maynardS2ReciprocalGSingularCorrection_sum_le hD
  calc
    |maynardS2ReciprocalGSingularTail D Q - 1| =
        ‖∏ p ∈ P, (1 + c p) - 1‖ := by
      rw [Real.norm_eq_abs, hfactor]
    _ ≤ Real.exp (∑ p ∈ P, ‖c p‖) - 1 := hdev
    _ ≤ Real.exp (16 / (D : ℝ)) - 1 := by
      gcongr

theorem abs_maynardS2ReciprocalGInfiniteSingularTail_sub_one_le
    {D : ℕ} (hD : 2 ≤ D) :
    |maynardS2ReciprocalGInfiniteSingularTail D - 1| ≤
      Real.exp (16 / (D : ℝ)) - 1 := by
  have hlim := (tendsto_maynardS2ReciprocalGSingularTail hD).sub_const 1 |>.abs
  exact le_of_tendsto hlim (Eventually.of_forall fun Q =>
    abs_maynardS2ReciprocalGSingularTail_sub_one_le hD)

end BoundedGaps.Maynard
