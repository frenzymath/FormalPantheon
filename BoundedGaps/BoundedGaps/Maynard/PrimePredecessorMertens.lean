import BoundedGaps.Maynard.PrimeMertens
import Mathlib.Analysis.PSeries

noncomputable section

/-! A bounded-error Mertens estimate with the Euler factor denominator `p - 1`. -/

namespace BoundedGaps.Maynard

open Finset Nat Real

noncomputable def primeLogPredecessorSum (D : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE D, Real.log p / (p - 1 : ℕ)

noncomputable def primeLogPredecessorCorrection (D : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE D,
    Real.log p / ((p : ℝ) * (p - 1 : ℕ))

theorem primeLogPredecessorSum_eq (D : ℕ) :
    primeLogPredecessorSum D =
      primeLogHarmonicSum D + primeLogPredecessorCorrection D := by
  unfold primeLogPredecessorSum primeLogHarmonicSum
    primeLogPredecessorCorrection
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hpPrime := Nat.prime_of_mem_primesLE hp
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
  have hpPredPos : (0 : ℝ) < (p - 1 : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt hpPrime.one_lt
  have hpredCast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub hpPrime.one_le]
    norm_num
  rw [hpredCast] at hpPredPos ⊢
  field_simp [ne_of_gt hpPos, ne_of_gt hpPredPos]
  ring

private theorem prime_correction_term_le {p : ℕ} (hp : p.Prime) :
    Real.log p / ((p : ℝ) * (p - 1 : ℕ)) ≤
      4 / (p : ℝ) ^ (3 / 2 : ℝ) := by
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpPredPos : (0 : ℝ) < (p - 1 : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt hp.one_lt
  have hlog := Real.log_natCast_le_rpow_div p (show (0 : ℝ) < 1 / 2 by norm_num)
  have hpred : (p : ℝ) ≤ 2 * (p - 1 : ℕ) := by
    rw [Nat.cast_sub hp.one_le]
    have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    norm_num only [Nat.cast_one]
    linarith
  rw [div_le_div_iff₀ (mul_pos hpPos hpPredPos)
    (Real.rpow_pos_of_pos hpPos _)]
  calc
    Real.log p * (p : ℝ) ^ (3 / 2 : ℝ) ≤
        (2 * (p : ℝ) ^ (1 / 2 : ℝ)) *
          (p : ℝ) ^ (3 / 2 : ℝ) := by
      gcongr
      simpa [div_eq_mul_inv, mul_comm] using hlog
    _ = 2 * (p : ℝ) ^ (2 : ℝ) := by
      rw [mul_assoc, ← Real.rpow_add hpPos]
      norm_num
    _ = 2 * (p : ℝ) ^ 2 := by rw [Real.rpow_two]
    _ ≤ 4 * ((p : ℝ) * (p - 1 : ℕ)) := by nlinarith

private theorem summable_prime_predecessor_correction :
    Summable fun n : ℕ =>
      if n.Prime then Real.log n / ((n : ℝ) * (n - 1 : ℕ)) else 0 := by
  have hs : Summable fun n : ℕ => 4 / (n : ℝ) ^ (3 / 2 : ℝ) := by
    simpa [div_eq_mul_inv] using
      ((Real.summable_one_div_nat_rpow
        (p := (3 / 2 : ℝ))).mpr (by norm_num)).mul_left 4
  apply hs.of_nonneg_of_le
  · intro n
    split_ifs with hn
    · positivity
    · exact le_rfl
  · intro n
    split_ifs with hn
    · exact prime_correction_term_le hn
    · positivity

theorem exists_uniform_abs_primeLogPredecessorSum_sub_log :
    ∃ C : ℝ, ∀ D : ℕ,
      |primeLogPredecessorSum D - Real.log D| ≤ C := by
  obtain ⟨C, hC⟩ := exists_uniform_abs_primeLogHarmonicSum_sub_log
  let f : ℕ → ℝ := fun n =>
    if n.Prime then Real.log n / ((n : ℝ) * (n - 1 : ℕ)) else 0
  refine ⟨C + ∑' n : ℕ, f n, fun D => ?_⟩
  have hfSummable : Summable f := summable_prime_predecessor_correction
  have hfNonneg (n : ℕ) : 0 ≤ f n := by
    unfold f
    split_ifs <;> positivity
  have hcorrNonneg : 0 ≤ primeLogPredecessorCorrection D := by
    unfold primeLogPredecessorCorrection
    exact Finset.sum_nonneg fun p hp => by positivity
  have hcorrLe : primeLogPredecessorCorrection D ≤ ∑' n : ℕ, f n := by
    unfold primeLogPredecessorCorrection
    calc
      (∑ p ∈ Nat.primesLE D,
          Real.log p / ((p : ℝ) * (p - 1 : ℕ))) =
          ∑ p ∈ Nat.primesLE D, f p := by
        apply Finset.sum_congr rfl
        intro p hp
        simp [f, Nat.prime_of_mem_primesLE hp]
      _ ≤ ∑' n : ℕ, f n :=
        hfSummable.sum_le_tsum (Nat.primesLE D) fun n hn => hfNonneg n
  rw [primeLogPredecessorSum_eq]
  calc
    |primeLogHarmonicSum D + primeLogPredecessorCorrection D - Real.log D| =
        |(primeLogHarmonicSum D - Real.log D) +
          primeLogPredecessorCorrection D| := by ring_nf
    _ ≤ |primeLogHarmonicSum D - Real.log D| +
        |primeLogPredecessorCorrection D| := abs_add_le _ _
    _ ≤ C + ∑' n : ℕ, f n := by
      apply add_le_add (hC D)
      rwa [abs_of_nonneg hcorrNonneg]

end BoundedGaps.Maynard
