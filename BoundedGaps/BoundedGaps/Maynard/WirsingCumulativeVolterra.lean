import BoundedGaps.Maynard.WirsingQuotientBalance
import BoundedGaps.Maynard.AugmentedReciprocalTotientLocalData
import Mathlib.Algebra.BigOperators.Module

noncomputable section

/-!
# Cumulative Volterra balance for the squarefree reciprocal-totient mean

This is the exact finite summation-by-parts form of the logarithmic balance
below GGPY2009, Lemma `L:Wirsing`, source lines 803--842.  It exposes the
all-previous-cutoff recurrence needed by the later cumulative argument; it
does not assert the source's asymptotic normalization.
-/

namespace BoundedGaps.Maynard

open Finset Nat Real
open scoped BigOperators

noncomputable def squarefreeCoprimeInvTotientLogIncrementSum
    (W Q : ℕ) : ℝ :=
  ∑ i ∈ Finset.range Q,
    (Real.log (i + 1) - Real.log i) *
      squarefreeCoprimeInvTotientMean W i

theorem squarefreeCoprimeInvTotientLogMean_eq_log_mul_mean_sub_increment_sum
    (W Q : ℕ) :
    squarefreeCoprimeInvTotientLogMean W Q =
      Real.log Q * squarefreeCoprimeInvTotientMean W Q -
        squarefreeCoprimeInvTotientLogIncrementSum W Q := by
  classical
  let c : ℕ → ℝ := fun n => squarefreeCoprimeInvTotientAF W n
  have hpartial (i : ℕ) :
      (∑ n ∈ Finset.range (i + 1), c n) =
        squarefreeCoprimeInvTotientMean W i := by
    rw [Nat.range_succ_eq_Icc_zero]
    exact sum_squarefreeCoprimeInvTotientAF_eq_mean W i
  have hweighted :
      squarefreeCoprimeInvTotientLogMean W Q =
        ∑ n ∈ Finset.range (Q + 1), Real.log n * c n := by
    rw [Nat.range_succ_eq_Icc_zero,
      Finset.Icc_eq_cons_Ioc (Nat.zero_le Q), Finset.sum_cons]
    simp only [Nat.cast_zero, Real.log_zero, zero_mul, zero_add]
    rw [← Finset.Icc_add_one_left_eq_Ioc]
    unfold squarefreeCoprimeInvTotientLogMean c
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    rw [squarefreeCoprimeInvTotientAF_apply]
    have hnPos : n ≠ 0 := by
      exact (Nat.zero_lt_of_lt (Finset.mem_Icc.mp hn).1).ne'
    rw [if_neg hnPos]
    by_cases h : Squarefree n ∧ Nat.Coprime n W
    · rw [if_pos h, if_pos h]
      ring
    · rw [if_neg h, if_neg h]
      ring
  rw [hweighted]
  have habel := Finset.sum_range_by_parts
    (fun n : ℕ => Real.log n) c (Q + 1)
  simp_rw [hpartial] at habel
  rw [Nat.add_sub_cancel] at habel
  simpa [smul_eq_mul, squarefreeCoprimeInvTotientLogIncrementSum] using habel

theorem exists_uniform_abs_log_mul_mean_sub_two_increment_sum_le :
    ∃ K : ℝ, 0 < K ∧
      ∀ {D P Q : ℕ}, 0 < P → 0 < Q →
        |Real.log Q * squarefreeCoprimeInvTotientMean
              (primorial D * P) Q -
            2 * squarefreeCoprimeInvTotientLogIncrementSum
              (primorial D * P) Q| ≤
          (K + Real.log D + primeLogDivisorMass P) *
            squarefreeCoprimeInvTotientMean (primorial D * P) Q := by
  obtain ⟨K, hK, hbal⟩ :=
    exists_uniform_abs_twoLogMean_sub_log_mul_mean_le
  refine ⟨K, hK, ?_⟩
  intro D P Q hP hQ
  have h := hbal (D := D) (P := P) (Q := Q) hP hQ
  rw [squarefreeCoprimeInvTotientLogMean_eq_log_mul_mean_sub_increment_sum]
    at h
  calc
    |Real.log Q * squarefreeCoprimeInvTotientMean
          (primorial D * P) Q -
        2 * squarefreeCoprimeInvTotientLogIncrementSum
          (primorial D * P) Q| =
      |2 * (Real.log Q * squarefreeCoprimeInvTotientMean
            (primorial D * P) Q -
          squarefreeCoprimeInvTotientLogIncrementSum
            (primorial D * P) Q) -
        Real.log Q * squarefreeCoprimeInvTotientMean
          (primorial D * P) Q| := by
      congr 1
      ring
    _ ≤ _ := h

end BoundedGaps.Maynard
