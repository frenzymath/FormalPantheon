import BoundedGaps.Maynard.ReciprocalTotientCorrection

noncomputable section

namespace BoundedGaps.Maynard

open Finset Nat ArithmeticFunction

/-! The remaining local correction coefficient at a prime square. -/

theorem reciprocalTotientCorrectionAF_apply_prime_sq
    (W : ℕ) {p : ℕ} (hp : p.Prime) :
    reciprocalTotientCorrectionAF W (p ^ 2) =
      if p ∣ W then 0 else -(1 : ℝ) / ((p : ℝ) * (p - 1 : ℕ)) := by
  by_cases hpW : p ∣ W
  · rw [if_pos hpW,
      reciprocalTotientCorrectionAF_apply_prime_sq_of_dvd W hp hpW]
  · rw [if_neg hpW]
    unfold reciprocalTotientCorrectionAF
    rw [ArithmeticFunction.mul_apply,
      sum_divisorsAntidiagonal (fun x y =>
        squarefreeCoprimeInvTotientAF W x * coprimeMobiusInvAF W y)]
    have hdiv : (p ^ 2).divisors = {1, p, p ^ 2} := by
      ext d
      simp only [Nat.mem_divisors]
      simp [Finset.mem_insert, Finset.mem_singleton]
      rw [dvd_prime_pow hp]
      simp [hp.ne_zero]
      constructor
      · rintro ⟨k, hk, rfl⟩
        interval_cases k <;> simp
      · rintro (rfl | rfl | rfl)
        · exact ⟨0, by norm_num, by simp⟩
        · exact ⟨1, by norm_num, by simp⟩
        · exact ⟨2, by norm_num, rfl⟩
    have h1p2 : (1 : ℕ) ∉ ({p, p ^ 2} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      constructor
      · exact hp.ne_one.symm
      · intro h
        have hpOne : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
        have h' : (1 : ℝ) = p ^ 2 := by exact_mod_cast h
        nlinarith
    have hpP2 : p ∉ ({p ^ 2} : Finset ℕ) := by
      simp only [Finset.mem_singleton]
      intro h
      have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      have h' : (p : ℝ) = p ^ 2 := by exact_mod_cast h
      nlinarith
    rw [hdiv, Finset.sum_insert h1p2, Finset.sum_insert hpP2,
      Finset.sum_singleton]
    rw [squarefreeCoprimeInvTotientAF_apply,
      squarefreeCoprimeInvTotientAF_apply,
      squarefreeCoprimeInvTotientAF_apply,
      coprimeMobiusInvAF_apply, coprimeMobiusInvAF_apply,
      coprimeMobiusInvAF_apply]
    have hp2divp : p ^ 2 / p = p := by
      rw [pow_two]
      exact Nat.mul_div_cancel_left _ hp.pos
    have hpc : Nat.Coprime p W := hp.coprime_iff_not_dvd.mpr hpW
    have hpc2 : Nat.Coprime (p ^ 2) W :=
      (Nat.coprime_pow_left_iff (by norm_num : 0 < 2) p W).mpr hpc
    have hs1 : Squarefree 1 ∧ Nat.Coprime 1 W := by
      exact ⟨by norm_num, Nat.coprime_one_left W⟩
    have hsP : Squarefree p ∧ Nat.Coprime p W := ⟨hp.squarefree, hpc⟩
    have hsq2 : ¬Squarefree (p ^ 2) := by
      rw [squarefree_pow_iff hp.ne_one (by norm_num)]
      omega
    have hnpSq2 : ¬(Squarefree (p ^ 2) ∧ Nat.Coprime (p ^ 2) W) :=
      fun h => hsq2 h.1
    simp only [Nat.div_one, hp2divp, Nat.div_self (pow_pos hp.pos 2)]
    simp only [if_neg one_ne_zero, if_pos hs1, if_neg hp.ne_zero,
      if_pos hsP, if_neg hnpSq2, if_pos hpc, if_pos hpc2,
      if_pos (Nat.coprime_one_left W)]
    rw [ArithmeticFunction.moebius_apply_prime hp,
      ArithmeticFunction.moebius_apply_prime_pow hp (by norm_num)]
    rw [if_neg (show (2 : ℕ) ≠ 1 by norm_num)]
    have hpow2 : p ^ 2 ≠ 0 := pow_ne_zero 2 hp.ne_zero
    simp only [if_neg hpow2]
    norm_num [Nat.totient_prime hp]
    rw [Nat.cast_sub hp.one_le]
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hpM : (p : ℝ) - 1 ≠ 0 := by
      have hpOne : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
      nlinarith
    field_simp [hpR, hpM]

end BoundedGaps.Maynard
