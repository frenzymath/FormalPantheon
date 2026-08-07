import BoundedGaps.Maynard.MaynardPreSievedTotientMean
import BoundedGaps.Maynard.PrimorialCoprimeHarmonic
import Mathlib.NumberTheory.ArithmeticFunction.Misc

noncomputable section

/-! Exact Dirichlet-convolution correction for the squarefree reciprocal-totient mean. -/

namespace BoundedGaps.Maynard

open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius

noncomputable def squarefreeCoprimeInvTotientAF (W : ℕ) :
    ArithmeticFunction ℝ where
  toFun n := if n = 0 then 0 else
    if Squarefree n ∧ Nat.Coprime n W then (1 : ℝ) / Nat.totient n else 0
  map_zero' := if_pos rfl

theorem squarefreeCoprimeInvTotientAF_apply (W n : ℕ) :
    squarefreeCoprimeInvTotientAF W n = if n = 0 then 0 else
      if Squarefree n ∧ Nat.Coprime n W then
        (1 : ℝ) / Nat.totient n else 0 := rfl

private theorem squarefreeCoprimeInvTotientAF_multiplicative (W : ℕ) :
    (squarefreeCoprimeInvTotientAF W).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · simp [squarefreeCoprimeInvTotientAF]
  · intro m n hm hn hmn
    rw [squarefreeCoprimeInvTotientAF_apply,
      squarefreeCoprimeInvTotientAF_apply,
      squarefreeCoprimeInvTotientAF_apply]
    simp only [mul_ne_zero hm hn, hm, hn, ↓reduceIte]
    simp only [Nat.squarefree_mul hmn, Nat.coprime_mul_iff_left]
    by_cases hms : Squarefree m
    · by_cases hns : Squarefree n
      · by_cases hmc : Nat.Coprime m W
        · by_cases hnc : Nat.Coprime n W
          · rw [Nat.totient_mul hmn]
            push_cast
            rw [if_pos ⟨⟨hms, hns⟩, ⟨hmc, hnc⟩⟩,
              if_pos ⟨hms, hmc⟩, if_pos ⟨hns, hnc⟩]
            simp only [one_div, mul_inv_rev]
            ring_nf
          · have hnCond : ¬(Squarefree n ∧ Nat.Coprime n W) :=
              fun h => hnc h.2
            rw [if_neg (fun h => hnc h.2.2), if_neg hnCond]
            ring_nf
        · have hmCond : ¬(Squarefree m ∧ Nat.Coprime m W) :=
            fun h => hmc h.2
          rw [if_neg (fun h => hmc h.2.1), if_neg hmCond]
          ring_nf
      · simp [hms, hns]
    · simp [hms]

private noncomputable def realInvIdAF : ArithmeticFunction ℝ :=
  ArithmeticFunction.pdiv (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
    (ArithmeticFunction.id : ArithmeticFunction ℝ)

private theorem realInvIdAF_apply (n : ℕ) :
    realInvIdAF n = (1 : ℝ) / n := by
  unfold realInvIdAF
  simp only [ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.id_apply]
  by_cases hn : n = 0
  · simp [hn]
  · rw [ArithmeticFunction.zeta_apply_ne hn]
    norm_num

private noncomputable def coprimeIndicatorAF (W : ℕ) :
    ArithmeticFunction ℝ where
  toFun n := if n = 0 then 0 else if Nat.Coprime n W then 1 else 0
  map_zero' := if_pos rfl

private theorem coprimeIndicatorAF_apply (W n : ℕ) :
    coprimeIndicatorAF W n =
      if n = 0 then 0 else if Nat.Coprime n W then 1 else 0 := rfl

private theorem coprimeIndicatorAF_multiplicative (W : ℕ) :
    (coprimeIndicatorAF W).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · simp [coprimeIndicatorAF]
  · intro m n hm hn hmn
    rw [coprimeIndicatorAF_apply, coprimeIndicatorAF_apply,
      coprimeIndicatorAF_apply]
    simp only [mul_ne_zero hm hn, hm, hn, ↓reduceIte]
    simp only [Nat.coprime_mul_iff_left]
    by_cases hmc : Nat.Coprime m W
    · by_cases hnc : Nat.Coprime n W
      · rw [if_pos ⟨hmc, hnc⟩, if_pos hnc, if_pos hmc]
        ring_nf
      · rw [if_neg hnc]
        rw [if_neg (fun h => hnc h.2)]
        ring_nf
    · rw [if_neg hmc]
      rw [if_neg (fun h => hmc h.1)]
      ring_nf

noncomputable def coprimeHarmonicAF (W : ℕ) : ArithmeticFunction ℝ :=
  ArithmeticFunction.pmul realInvIdAF (coprimeIndicatorAF W)

private theorem coprimeHarmonicAF_multiplicative (W : ℕ) :
    (coprimeHarmonicAF W).IsMultiplicative :=
  (ArithmeticFunction.isMultiplicative_zeta.natCast.pdiv
    ArithmeticFunction.isMultiplicative_id.natCast).pmul
      (coprimeIndicatorAF_multiplicative W)

theorem coprimeHarmonicAF_apply (W n : ℕ) :
    coprimeHarmonicAF W n =
      if n = 0 then 0 else if Nat.Coprime n W then (1 : ℝ) / n else 0 := by
  unfold coprimeHarmonicAF coprimeIndicatorAF
  simp only [ArithmeticFunction.pmul_apply, realInvIdAF_apply]
  by_cases hn : n = 0 <;> by_cases hc : Nat.Coprime n W <;> simp [hn, hc]

noncomputable def coprimeMobiusInvAF (W : ℕ) :
    ArithmeticFunction ℝ :=
  ArithmeticFunction.pmul
    (ArithmeticFunction.moebius : ArithmeticFunction ℝ)
    (coprimeHarmonicAF W)

private theorem coprimeMobiusInvAF_multiplicative (W : ℕ) :
    (coprimeMobiusInvAF W).IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_moebius.intCast.pmul
    (coprimeHarmonicAF_multiplicative W)

theorem coprimeMobiusInvAF_apply (W n : ℕ) :
    coprimeMobiusInvAF W n =
      if n = 0 then 0 else if Nat.Coprime n W then
        (ArithmeticFunction.moebius n : ℝ) / n else 0 := by
  unfold coprimeMobiusInvAF
  rw [ArithmeticFunction.pmul_apply, coprimeHarmonicAF_apply]
  by_cases hn : n = 0 <;> by_cases hc : Nat.Coprime n W <;> simp [hn, hc]
  ring_nf

private theorem coprimeMobiusInv_mul_harmonic (W : ℕ) :
    coprimeMobiusInvAF W * coprimeHarmonicAF W = 1 := by
  ext n
  by_cases hn : n = 0
  · simp [hn]
  rw [ArithmeticFunction.mul_apply,
    sum_divisorsAntidiagonal (fun x y =>
      coprimeMobiusInvAF W x * coprimeHarmonicAF W y)]
  by_cases hcop : Nat.Coprime n W
  · have hmu : (∑ d ∈ n.divisors, ArithmeticFunction.moebius d) =
        (1 : ArithmeticFunction ℤ) n := by
      calc
        (∑ d ∈ n.divisors, ArithmeticFunction.moebius d) =
            (ArithmeticFunction.moebius * ArithmeticFunction.zeta) n := by
          rw [ArithmeticFunction.coe_mul_zeta_apply]
        _ = (1 : ArithmeticFunction ℤ) n := by
          rw [ArithmeticFunction.moebius_mul_coe_zeta]
    calc
      (∑ d ∈ n.divisors,
          coprimeMobiusInvAF W d * coprimeHarmonicAF W (n / d)) =
          ∑ d ∈ n.divisors,
            (ArithmeticFunction.moebius d : ℝ) / n := by
        apply Finset.sum_congr rfl
        intro d hd
        have hdvd := Nat.dvd_of_mem_divisors hd
        have hdPos := Nat.pos_of_mem_divisors hd
        have hqPos : 0 < n / d :=
          Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd) hdPos
        have hdc := Nat.Coprime.of_dvd_left hdvd hcop
        have hqc := Nat.Coprime.of_dvd_left (Nat.div_dvd_of_dvd hdvd) hcop
        rw [coprimeMobiusInvAF_apply, coprimeHarmonicAF_apply]
        rw [if_neg hdPos.ne', if_pos hdc, if_neg hqPos.ne', if_pos hqc]
        have hprod : (d : ℝ) * (n / d : ℕ) = n := by
          exact_mod_cast Nat.mul_div_cancel' hdvd
        rw [← hprod]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring_nf
      _ = (((1 : ArithmeticFunction ℤ) n : ℤ) : ℝ) / n := by
        rw [← Finset.sum_div]
        congr 1
        exact_mod_cast hmu
      _ = (1 : ArithmeticFunction ℝ) n := by
        by_cases hnOne : n = 1
        · simp [hnOne]
        · simp [hnOne]
  · have hnOne : n ≠ 1 := by
      intro hnOne
      subst n
      exact hcop (by simp)
    rw [show (1 : ArithmeticFunction ℝ) n = 0 by simp [hnOne]]
    apply Finset.sum_eq_zero
    intro d hd
    have hdvd := Nat.dvd_of_mem_divisors hd
    have hprod := Nat.mul_div_cancel' hdvd
    by_cases hdc : Nat.Coprime d W
    · have hquotNot : ¬Nat.Coprime (n / d) W := by
        intro hqc
        exact hcop (hprod ▸ hdc.mul_left hqc)
      rw [coprimeHarmonicAF_apply]
      simp [hquotNot]
    · rw [coprimeMobiusInvAF_apply]
      simp [hdc]

theorem coprimeMobiusInvAF_mul_coprimeHarmonicAF (W : ℕ) :
    coprimeMobiusInvAF W * coprimeHarmonicAF W = 1 :=
  coprimeMobiusInv_mul_harmonic W

theorem coprimeMobiusInvAF_isMultiplicative (W : ℕ) :
    (coprimeMobiusInvAF W).IsMultiplicative :=
  coprimeMobiusInvAF_multiplicative W

noncomputable def reciprocalTotientCorrectionAF (W : ℕ) :
    ArithmeticFunction ℝ :=
  squarefreeCoprimeInvTotientAF W * coprimeMobiusInvAF W

theorem reciprocalTotientCorrectionAF_multiplicative (W : ℕ) :
    (reciprocalTotientCorrectionAF W).IsMultiplicative :=
  (squarefreeCoprimeInvTotientAF_multiplicative W).mul
    (coprimeMobiusInvAF_multiplicative W)

theorem reciprocalTotientCorrectionAF_apply_prime
    (W : ℕ) {p : ℕ} (hp : p.Prime) :
    reciprocalTotientCorrectionAF W p =
      if p ∣ W then 0 else (1 : ℝ) / ((p : ℝ) * (p - 1 : ℕ)) := by
  unfold reciprocalTotientCorrectionAF
  rw [ArithmeticFunction.mul_apply,
    sum_divisorsAntidiagonal (fun x y =>
      squarefreeCoprimeInvTotientAF W x * coprimeMobiusInvAF W y)]
  have hdiv : p.divisors = {1, p} := by
    ext d
    simp [Nat.mem_divisors, hp.ne_zero, Nat.dvd_prime hp]
  have h1p : (1 : ℕ) ∉ ({p} : Finset ℕ) := by
    simpa using hp.ne_one.symm
  rw [hdiv, Finset.sum_insert h1p, Finset.sum_singleton]
  rw [squarefreeCoprimeInvTotientAF_apply,
    squarefreeCoprimeInvTotientAF_apply,
    coprimeMobiusInvAF_apply, coprimeMobiusInvAF_apply]
  simp only [Nat.div_one, Nat.div_self hp.pos]
  by_cases hpW : p ∣ W
  · have hpc : ¬Nat.Coprime p W := by
      intro h
      exact (hp.coprime_iff_not_dvd.mp h) hpW
    simp [hpc, hpW]
  · have hpc : Nat.Coprime p W := hp.coprime_iff_not_dvd.mpr hpW
    have hs : Squarefree p ∧ Nat.Coprime p W := ⟨hp.squarefree, hpc⟩
    simp only [if_neg hp.ne_zero, if_pos hs]
    simp [hpW, Nat.totient_prime hp,
      ArithmeticFunction.moebius_apply_prime hp]
    rw [if_pos hpc, Nat.cast_sub hp.one_le]
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hpM : (p : ℝ) - 1 ≠ 0 := by
      have hpOne : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
      nlinarith
    field_simp [hpR, hpM]
    ring

theorem reciprocalTotientCorrectionAF_apply_prime_sq_of_dvd
    (W : ℕ) {p : ℕ} (hp : p.Prime) (hpW : p ∣ W) :
    reciprocalTotientCorrectionAF W (p ^ 2) = 0 := by
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
  have hpc : ¬Nat.Coprime p W := by
    intro h
    exact (hp.coprime_iff_not_dvd.mp h) hpW
  have hpc2 : ¬Nat.Coprime (p ^ 2) W := by
    intro h
    exact hpc ((Nat.coprime_pow_left_iff (by norm_num : 0 < 2) p W).mp h)
  simp [Nat.div_one, hp2divp, hp.ne_zero, hpc, hpc2]

theorem reciprocalTotientCorrectionAF_apply_prime_pow_of_dvd
    (W : ℕ) {p i : ℕ} (hp : p.Prime) (hi : 1 ≤ i) (hpW : p ∣ W) :
    reciprocalTotientCorrectionAF W (p ^ i) = 0 := by
  unfold reciprocalTotientCorrectionAF
  rw [ArithmeticFunction.mul_apply,
    sum_divisorsAntidiagonal (fun x y =>
      squarefreeCoprimeInvTotientAF W x * coprimeMobiusInvAF W y),
    Nat.sum_divisors_prime_pow hp]
  apply Finset.sum_eq_zero
  intro j hj
  simp only [Finset.mem_range] at hj
  rw [squarefreeCoprimeInvTotientAF_apply]
  by_cases hj0 : j = 0
  · subst j
    rw [pow_zero, Nat.div_one]
    have hs1 : Squarefree 1 := by norm_num
    rw [if_neg one_ne_zero, if_pos ⟨hs1, Nat.coprime_one_left W⟩]
    norm_num
    rw [coprimeMobiusInvAF_apply]
    have hpc : ¬Nat.Coprime (p ^ i) W := by
      intro h
      exact (hp.coprime_iff_not_dvd.mp
        ((Nat.coprime_pow_left_iff (Nat.pos_of_ne_zero (by omega)) p W).mp h)) hpW
    simp [hpc, show i ≠ 0 by omega]
  · have hjPos : 0 < j := Nat.pos_of_ne_zero hj0
    have hpc : ¬Nat.Coprime (p ^ j) W := by
      intro h
      exact (hp.coprime_iff_not_dvd.mp
        ((Nat.coprime_pow_left_iff hjPos p W).mp h)) hpW
    simp [hpc]

theorem reciprocalTotientCorrectionAF_apply_prime_pow_ge_three
    (W : ℕ) {p i : ℕ} (hp : p.Prime) (hi : 3 ≤ i) :
    reciprocalTotientCorrectionAF W (p ^ i) = 0 := by
  unfold reciprocalTotientCorrectionAF
  rw [ArithmeticFunction.mul_apply,
    sum_divisorsAntidiagonal (fun x y =>
      squarefreeCoprimeInvTotientAF W x * coprimeMobiusInvAF W y),
    Nat.sum_divisors_prime_pow hp]
  apply Finset.sum_eq_zero
  intro j hj
  simp only [Finset.mem_range] at hj
  rw [squarefreeCoprimeInvTotientAF_apply]
  by_cases hj0 : j = 0
  · subst j
    rw [pow_zero, Nat.div_one]
    have hs1 : Squarefree 1 := by norm_num
    rw [if_neg one_ne_zero, if_pos ⟨hs1, Nat.coprime_one_left W⟩]
    norm_num
    rw [coprimeMobiusInvAF_apply]
    have hpowNe : p ^ i ≠ 0 := pow_ne_zero i hp.ne_zero
    rw [if_neg hpowNe]
    by_cases hc : Nat.Coprime (p ^ i) W
    · rw [if_pos hc, ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
      simp [show i ≠ 1 by omega]
    · rw [if_neg hc]
  · by_cases hj1 : j = 1
    · subst j
      have hquot : p ^ i / p ^ 1 = p ^ (i - 1) := by
        conv_lhs =>
          rw [show i = 1 + (i - 1) by omega, pow_add]
        exact Nat.mul_div_cancel_left _ (pow_pos hp.pos 1)
      rw [hquot, coprimeMobiusInvAF_apply]
      have hpowNe : p ^ (i - 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
      rw [if_neg hpowNe]
      by_cases hc : Nat.Coprime (p ^ (i - 1)) W
      · rw [if_pos hc, ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
        simp [show i - 1 ≠ 1 by omega]
      · rw [if_neg hc]
        ring
    · have hjTwo : 2 ≤ j := by omega
      have hpowNe : p ^ j ≠ 0 := pow_ne_zero j hp.ne_zero
      have hsq : ¬Squarefree (p ^ j) := by
        rw [squarefree_pow_iff hp.ne_one (by omega)]
        omega
      rw [if_neg hpowNe, if_neg (fun h => hsq h.1)]
      simp

theorem reciprocalTotientCorrection_mul_coprimeHarmonic (W : ℕ) :
    reciprocalTotientCorrectionAF W * coprimeHarmonicAF W =
      squarefreeCoprimeInvTotientAF W := by
  unfold reciprocalTotientCorrectionAF
  rw [mul_assoc, coprimeMobiusInv_mul_harmonic, mul_one]

theorem squarefreeCoprimeInvTotientMean_eq_correction_coprimeHarmonic
    (W Q : ℕ) :
    squarefreeCoprimeInvTotientMean W Q =
      ∑ d ∈ Finset.Ioc 0 Q,
        reciprocalTotientCorrectionAF W d *
          coprimeHarmonicSum W (Q / d) := by
  have htarget : squarefreeCoprimeInvTotientMean W Q =
      ∑ n ∈ Finset.Ioc 0 Q, squarefreeCoprimeInvTotientAF W n := by
    unfold squarefreeCoprimeInvTotientMean
    have hinterval : Finset.Icc 1 Q = Finset.Ioc 0 Q := by
      ext n
      simp
      omega
    rw [hinterval]
    apply Finset.sum_congr rfl
    intro n hn
    rw [squarefreeCoprimeInvTotientAF_apply]
    have hnNe : n ≠ 0 := (Finset.mem_Ioc.mp hn).1.ne'
    rw [if_neg hnNe]
  rw [htarget, ← reciprocalTotientCorrection_mul_coprimeHarmonic]
  rw [ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  rw [show Finset.Ioc 0 (Q / d) = Finset.Icc 1 (Q / d) by
    ext n
    simp
    omega]
  unfold coprimeHarmonicSum
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  rw [coprimeHarmonicAF_apply]
  have hnNe : n ≠ 0 :=
    (zero_lt_one.trans_le (Finset.mem_Icc.mp hn).1).ne'
  rw [if_neg hnNe]

end BoundedGaps.Maynard
