import BoundedGaps.Maynard.MaynardS2ReciprocalGCorrection

noncomputable section

/-! Prime-square and higher-prime-power coefficients of the reciprocal-`g` correction. -/

namespace BoundedGaps.Maynard

open Finset Nat ArithmeticFunction

theorem maynardS2ReciprocalGCorrectionAF_apply_prime_sq
    (W : ℕ) {p : ℕ} (hp : p.Prime) :
    maynardS2ReciprocalGCorrectionAF W (p ^ 2) =
      if p ∣ W then 0 else
        -(1 : ℝ) / ((p : ℝ) * ((p - 2 : ℕ) : ℝ)) := by
  unfold maynardS2ReciprocalGCorrectionAF
  rw [ArithmeticFunction.mul_apply,
    sum_divisorsAntidiagonal (fun x y =>
      maynardS2ReciprocalGSquarefreeAF W x * coprimeMobiusInvAF W y)]
  rw [Nat.sum_divisors_prime_pow hp]
  have h0 : (0 : ℕ) ∉ ({1, 2} : Finset ℕ) := by simp
  have h1 : (1 : ℕ) ∉ ({2} : Finset ℕ) := by simp
  have hrange : Finset.range 3 = ({0, 1, 2} : Finset ℕ) := by
    ext j
    simp
    omega
  rw [hrange, Finset.sum_insert h0, Finset.sum_insert h1,
    Finset.sum_singleton]
  rw [show p ^ 0 = 1 by simp, show p ^ 1 = p by simp,
    show p ^ 2 = p ^ 2 by rfl,
    show p ^ 2 / 1 = p ^ 2 by simp,
    show p ^ 2 / p = p by
      rw [pow_two]
      exact Nat.mul_div_cancel_left _ hp.pos,
    show p ^ 2 / p ^ 2 = 1 by
      exact Nat.div_self (pow_pos hp.pos 2)]
  have hweightOne : maynardS2ReciprocalGSquarefreeAF W 1 = 1 :=
    (maynardS2ReciprocalGSquarefreeAF_isMultiplicative W).map_one
  have hweightPrime : maynardS2ReciprocalGSquarefreeAF W p =
      if p ∣ W then 0 else (1 : ℝ) / ((p - 2 : ℕ) : ℝ) :=
    maynardS2ReciprocalGSquarefreeAF_apply_prime W hp
  have hpowNe : p ^ 2 ≠ 0 := pow_ne_zero 2 hp.ne_zero
  have hmu2 : ArithmeticFunction.moebius (p ^ 2) = 0 := by
    rw [ArithmeticFunction.moebius_apply_prime_pow hp (by norm_num)]
    simp
  have hmu2R : (ArithmeticFunction.moebius (p ^ 2) : ℝ) = 0 := by
    exact_mod_cast hmu2
  have hmu2AF :
      (ArithmeticFunction.moebius : ArithmeticFunction ℝ) (p ^ 2) = 0 := by
    change (ArithmeticFunction.moebius (p ^ 2) : ℝ) = 0
    exact_mod_cast hmu2
  have hweightSq : maynardS2ReciprocalGSquarefreeAF W (p ^ 2) = 0 := by
    unfold maynardS2ReciprocalGSquarefreeAF
    rw [ArithmeticFunction.pmul_apply, ArithmeticFunction.pmul_apply,
      hmu2AF]
    norm_num
  rw [hweightOne, hweightPrime, hweightSq]
  rw [coprimeMobiusInvAF_apply, coprimeMobiusInvAF_apply,
    coprimeMobiusInvAF_apply]
  by_cases hpW : p ∣ W
  · have hnot : ¬Nat.Coprime p W := by
      exact fun h => (hp.coprime_iff_not_dvd.mp h) hpW
    have hnot2 : ¬Nat.Coprime (p ^ 2) W := by
      exact fun h => hnot ((Nat.coprime_pow_left_iff (by norm_num : 0 < 2)
        p W).mp h)
    simp [hpW, hp.ne_zero, hnot, hnot2]
  · have hpc : Nat.Coprime p W := hp.coprime_iff_not_dvd.mpr hpW
    have hpc2 : Nat.Coprime (p ^ 2) W :=
      (Nat.coprime_pow_left_iff (by norm_num : 0 < 2) p W).mpr hpc
    simp only [if_neg hpW, if_neg hp.ne_zero, if_neg hpowNe, if_pos hpc,
      if_pos hpc2, ArithmeticFunction.moebius_apply_prime hp]
    rw [hmu2R]
    ring

theorem maynardS2ReciprocalGCorrectionAF_apply_prime_pow_ge_three
    (W : ℕ) {p i : ℕ} (hp : p.Prime) (hi : 3 ≤ i) :
    maynardS2ReciprocalGCorrectionAF W (p ^ i) = 0 := by
  unfold maynardS2ReciprocalGCorrectionAF
  rw [ArithmeticFunction.mul_apply,
    sum_divisorsAntidiagonal (fun x y =>
      maynardS2ReciprocalGSquarefreeAF W x * coprimeMobiusInvAF W y),
    Nat.sum_divisors_prime_pow hp]
  apply Finset.sum_eq_zero
  intro j hj
  simp only [Finset.mem_range] at hj
  rw [show p ^ i / p ^ j = p ^ (i - j) by
    conv_lhs =>
      rw [show i = j + (i - j) by omega, pow_add]
    exact Nat.mul_div_cancel_left _ (pow_pos hp.pos j)]
  by_cases hj0 : j = 0
  · subst j
    simp only [pow_zero, Nat.sub_zero]
    have hpowNe : p ^ i ≠ 0 := pow_ne_zero i hp.ne_zero
    have hweightOne : maynardS2ReciprocalGSquarefreeAF W 1 = 1 :=
      (maynardS2ReciprocalGSquarefreeAF_isMultiplicative W).map_one
    rw [hweightOne, coprimeMobiusInvAF_apply, if_neg hpowNe]
    by_cases hc : Nat.Coprime (p ^ i) W
    · rw [if_pos hc, ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
      simp [show i ≠ 1 by omega]
    · simp [hc]
  · by_cases hj1 : j = 1
    · subst j
      have hpowNe : p ^ (i - 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
      rw [coprimeMobiusInvAF_apply, if_neg hpowNe]
      by_cases hc : Nat.Coprime (p ^ (i - 1)) W
      · rw [if_pos hc, ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
        simp [show i - 1 ≠ 1 by omega]
      · simp [hc]
    · have hjTwo : 2 ≤ j := by omega
      unfold maynardS2ReciprocalGSquarefreeAF
      rw [ArithmeticFunction.pmul_apply, ArithmeticFunction.pmul_apply]
      have hmu : ArithmeticFunction.moebius (p ^ j) = 0 := by
        rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
        simp [show j ≠ 1 by omega]
      have hmuAF :
          (ArithmeticFunction.moebius : ArithmeticFunction ℝ) (p ^ j) = 0 := by
        change (ArithmeticFunction.moebius (p ^ j) : ℝ) = 0
        exact_mod_cast hmu
      rw [hmuAF]
      norm_num

end BoundedGaps.Maynard
