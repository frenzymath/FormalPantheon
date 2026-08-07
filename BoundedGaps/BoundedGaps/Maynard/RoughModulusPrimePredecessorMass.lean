import BoundedGaps.Maynard.PrimePredecessorMertens
import BoundedGaps.Maynard.RoughModulusPrimeLogMass

noncomputable section

/-!
# Prime-predecessor mass of a varying squarefree modulus

The `log p / (p - 1)` mass splits into the existing rough-modulus
`log p / p` mass and one uniformly bounded convergent correction.
-/

namespace BoundedGaps.Maynard

open Finset Nat Real

noncomputable def primeLogPredecessorDivisorMass (P : ℕ) : ℝ :=
  ∑ p ∈ P.primeFactors, Real.log p / (p - 1 : ℕ)

noncomputable def primeLogPredecessorDivisorCorrection (P : ℕ) : ℝ :=
  ∑ p ∈ P.primeFactors,
    Real.log p / ((p : ℝ) * (p - 1 : ℕ))

theorem primeLogPredecessorDivisorMass_eq (P : ℕ) :
    primeLogPredecessorDivisorMass P =
      primeLogDivisorMass P +
        primeLogPredecessorDivisorCorrection P := by
  unfold primeLogPredecessorDivisorMass primeLogDivisorMass
    primeLogPredecessorDivisorCorrection
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hpMem
  have hp := Nat.prime_of_mem_primeFactors hpMem
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpPredPos : (0 : ℝ) < (p - 1 : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt hp.one_lt
  have hpPredPos' : (0 : ℝ) < (p : ℝ) - 1 := by
    simpa [Nat.cast_sub hp.one_le] using hpPredPos
  rw [Nat.cast_sub hp.one_le]
  norm_num only [Nat.cast_one]
  field_simp [ne_of_gt hpPos, ne_of_gt hpPredPos']
  ring

theorem primeLogPredecessorDivisorCorrection_nonneg (P : ℕ) :
    0 ≤ primeLogPredecessorDivisorCorrection P := by
  unfold primeLogPredecessorDivisorCorrection
  exact Finset.sum_nonneg fun p hp => by positivity

theorem primeLogPredecessorDivisorCorrection_le
    {P : ℕ} (hP : 0 < P) :
    primeLogPredecessorDivisorCorrection P ≤
      primeLogPredecessorCorrection P := by
  unfold primeLogPredecessorDivisorCorrection
    primeLogPredecessorCorrection
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hpMem
    have hp := Nat.prime_of_mem_primeFactors hpMem
    have hpdvd := Nat.dvd_of_mem_primeFactors hpMem
    exact Nat.mem_primesLE.mpr
      ⟨Nat.le_of_dvd hP hpdvd, hp⟩
  · intro p hpMem hpNot
    positivity

theorem exists_uniform_primeLogPredecessorCorrection_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ D : ℕ,
      primeLogPredecessorCorrection D ≤ C := by
  obtain ⟨C₁, hpred⟩ :=
    exists_uniform_abs_primeLogPredecessorSum_sub_log
  obtain ⟨C₂, hharm⟩ :=
    exists_uniform_abs_primeLogHarmonicSum_sub_log
  refine ⟨|C₁| + |C₂|, add_nonneg (abs_nonneg _) (abs_nonneg _), ?_⟩
  intro D
  have hpred' := hpred D
  have hharm' := hharm D
  have hC₁ : C₁ ≤ |C₁| := le_abs_self C₁
  have hC₂ : C₂ ≤ |C₂| := le_abs_self C₂
  rw [primeLogPredecessorSum_eq] at hpred'
  calc
    primeLogPredecessorCorrection D =
        (primeLogHarmonicSum D + primeLogPredecessorCorrection D -
          Real.log D) - (primeLogHarmonicSum D - Real.log D) := by ring
    _ ≤ |primeLogHarmonicSum D + primeLogPredecessorCorrection D -
          Real.log D| +
        |primeLogHarmonicSum D - Real.log D| := by
      linarith [le_abs_self (primeLogHarmonicSum D +
        primeLogPredecessorCorrection D - Real.log D),
        neg_le_abs (primeLogHarmonicSum D - Real.log D)]
    _ ≤ C₁ + C₂ := add_le_add hpred' hharm'
    _ ≤ |C₁| + |C₂| := add_le_add hC₁ hC₂

theorem exists_uniform_primeLogPredecessorDivisorMass_bound :
    ∃ C : ℝ, ∀ {P T : ℕ}, Squarefree P → 0 < T →
      primeLogPredecessorDivisorMass P ≤
        Real.log T + C + Real.log P / T := by
  obtain ⟨C₁, hmass⟩ := exists_uniform_primeLogDivisorMass_bound
  obtain ⟨C₂, hC₂, hcorr⟩ :=
    exists_uniform_primeLogPredecessorCorrection_bound
  refine ⟨C₁ + C₂, fun {P T} hPsq hT => ?_⟩
  have hP : 0 < P := Nat.pos_of_ne_zero hPsq.ne_zero
  have hbase := hmass (P := P) (T := T) hPsq hT
  have hcorrection :=
    (primeLogPredecessorDivisorCorrection_le hP).trans (hcorr P)
  rw [primeLogPredecessorDivisorMass_eq]
  linarith

end BoundedGaps.Maynard
