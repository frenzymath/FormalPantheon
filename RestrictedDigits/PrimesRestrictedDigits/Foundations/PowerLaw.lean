import PrimesRestrictedDigits.Digits.ZeroCount
import PrimesRestrictedDigits.Foundations.CutoffMonotonicity
import PrimesRestrictedDigits.Foundations.DecimalScale

/-!
# Restricted counts and the decimal power law

This proves the count-only comparison with `X ^ (log 9 / log 10)` from the
exact digit counts and real-cutoff bridges. Prime estimates and the common
`log X` denominator in `MAYNARD-PRD-PUBLISHED`, Theorem 1.1, are separate.
-/

namespace PrimesRestrictedDigits

private noncomputable def decimalExponent : ℝ :=
  Real.log (9 : ℝ) / Real.log (10 : ℝ)

private theorem decimalExponent_pos : 0 < decimalExponent := by
  dsimp [decimalExponent]
  exact div_pos (Real.log_pos (by norm_num)) log_ten_pos

private theorem ten_rpow_decimalExponent : (10 : ℝ) ^ decimalExponent = 9 := by
  rw [Real.rpow_def_of_pos (by norm_num)]
  dsimp [decimalExponent]
  have hlog : Real.log (10 : ℝ) ≠ 0 := ne_of_gt log_ten_pos
  rw [mul_div_cancel₀ _ hlog, Real.exp_log (by norm_num)]

private theorem decimalPower_rpow (k : ℕ) :
    ((10 ^ k : ℕ) : ℝ) ^ decimalExponent = (9 : ℝ) ^ k := by
  rw [Nat.cast_pow]
  calc
    ((10 : ℝ) ^ k) ^ decimalExponent =
        ((10 : ℝ) ^ (k : ℝ)) ^ decimalExponent := by
      rw [Real.rpow_natCast]
    _ = (10 : ℝ) ^ ((k : ℝ) * decimalExponent) := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10)]
    _ = ((10 : ℝ) ^ decimalExponent) ^ k := by
      rw [mul_comm, Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 10)]
    _ = (9 : ℝ) ^ k := by rw [ten_rpow_decimalExponent]

private theorem one_omits_zero : omitsDecimalDigit (0 : Fin 10) 1 := by
  rw [omitsDecimalDigit]
  intro d hd
  simp [standardDecimalDigits] at hd
  omega

private theorem restrictedCount_four_pos (a : Fin 10) :
    1 ≤ restrictedCount a 4 := by
  have hmem : ∃ n, n ∈ restrictedNumbers a 4 := by
    by_cases ha : a.val = 0
    · have ha0 : a = (0 : Fin 10) := Fin.ext ha
      subst a
      refine ⟨1, ?_⟩
      rw [mem_restrictedNumbers]
      exact ⟨by norm_num, one_omits_zero⟩
    · refine ⟨0, ?_⟩
      rw [mem_restrictedNumbers]
      exact ⟨by norm_num, (omitsDecimalDigit_zero_iff a).2 ha⟩
  exact Finset.one_le_card.mpr hmem

private theorem restrictedCount_le_ten (a : Fin 10) {X : ℝ} (hX : X ≤ 10) :
    restrictedCount a X ≤ 10 := by
  have hmono := restrictedCount_le_of_le (a := a) hX
  have hten : restrictedCount a 10 ≤ 10 := by
    rw [restrictedCount]
    calc
      (restrictedNumbers a 10).card ≤ (Finset.range 10).card := by
        apply Finset.card_le_card
        intro n hn
        have hn' := (mem_restrictedNumbers.mp hn).1
        have hnlt : n < 10 := by exact_mod_cast hn'
        exact Finset.mem_range.mpr hnlt
      _ = 10 := Finset.card_range 10
  exact hmono.trans hten

private theorem zeroGeometricSum_le (k : ℕ) :
    (∑ i ∈ Finset.range k, 9 ^ (i + 1)) ≤ 2 * 9 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, pow_succ]
      nlinarith [ih, Nat.zero_le (9 ^ k)]

private theorem zeroGeometricSum_top_le (k : ℕ) (hk : 1 ≤ k) :
    9 ^ k ≤ ∑ i ∈ Finset.range k, 9 ^ (i + 1) := by
  have hmem : k - 1 ∈ Finset.range k := by
    rw [Finset.mem_range]
    omega
  have hterm : (9 : ℕ) ^ ((k - 1) + 1) ≤
      ∑ i ∈ Finset.range k, 9 ^ (i + 1) := by
    exact Finset.single_le_sum (f := fun i : ℕ => (9 : ℕ) ^ (i + 1))
      (fun i hi => Nat.zero_le _) hmem
  simpa [Nat.sub_add_cancel hk] using hterm

private theorem restrictedCount_decimalPower_bounds {a : Fin 10} {X : ℝ}
    {k : ℕ} (hk : 1 ≤ k) (hlo : ((10 ^ k : ℕ) : ℝ) ≤ X)
    (hupp : X < ((10 ^ (k + 1) : ℕ) : ℝ)) :
    9 ^ k ≤ restrictedCount a X ∧
      restrictedCount a X ≤ 2 * 9 ^ (k + 1) := by
  by_cases ha : a.val = 0
  · have ha0 : a = (0 : Fin 10) := Fin.ext ha
    subst a
    have hlowpow : 9 ^ k ≤ restrictedCount (0 : Fin 10)
        ((10 ^ k : ℕ) : ℝ) := by
      rw [restrictedCount_zero_power]
      exact zeroGeometricSum_top_le k hk
    have hlow := restrictedCount_le_of_le (a := (0 : Fin 10)) hlo
    have huppow := restrictedCount_le_of_le (a := (0 : Fin 10)) hupp.le
    constructor
    · exact hlowpow.trans hlow
    · rw [restrictedCount_zero_power] at huppow
      exact huppow.trans (by
        have hsum := zeroGeometricSum_le (k + 1)
        simpa [pow_succ] using hsum)
  · have hbounds :=
      restrictedCount_bounds_of_decimalPower_interval_of_ne_zero ha hlo hupp
    constructor
    · exact hbounds.1
    · have hp : 0 ≤ 9 ^ (k + 1) := Nat.zero_le _
      nlinarith [hbounds.2]

theorem restrictedCount_rpow_comparable {a : Fin 10} {X : ℝ} (hX : 4 ≤ X) :
    (1 / 100 : ℝ) * X ^ (Real.log (9 : ℝ) / Real.log (10 : ℝ)) <
        (restrictedCount a X : ℝ) ∧
      (restrictedCount a X : ℝ) <
        100 * X ^ (Real.log (9 : ℝ) / Real.log (10 : ℝ)) := by
  change (1 / 100 : ℝ) * X ^ decimalExponent < (restrictedCount a X : ℝ) ∧
    (restrictedCount a X : ℝ) < 100 * X ^ decimalExponent
  have hbpos := decimalExponent_pos
  by_cases hsmall : X < 10
  · have hlowcount : (1 : ℝ) ≤ (restrictedCount a X : ℝ) := by
      have hmono := restrictedCount_le_of_le (a := a)
        (by linarith : (4 : ℝ) ≤ X)
      have hnat : 1 ≤ restrictedCount a X :=
        le_trans (restrictedCount_four_pos a) hmono
      exact_mod_cast hnat
    have huppcount : (restrictedCount a X : ℝ) ≤ 10 := by
      exact_mod_cast restrictedCount_le_ten a (le_of_lt hsmall)
    have hxpow_lower : (1 : ℝ) < X ^ decimalExponent := by
      rw [← Real.one_rpow decimalExponent]
      exact Real.rpow_lt_rpow zero_le_one (by linarith) hbpos
    have hxpow_upper : X ^ decimalExponent < 9 := by
      calc
        X ^ decimalExponent < (10 : ℝ) ^ decimalExponent :=
          Real.rpow_lt_rpow (by linarith) hsmall hbpos
        _ = 9 := ten_rpow_decimalExponent
    constructor <;> nlinarith
  · have hX10 : 10 ≤ X := le_of_not_gt hsmall
    obtain ⟨k, hlo, hupp⟩ := exists_decimalPower_interval hX
    have hk : 1 ≤ k := by
      by_contra hk0
      have hkz : k = 0 := Nat.eq_zero_of_not_pos hk0
      subst k
      norm_num at hupp
      linarith
    have hcounts := restrictedCount_decimalPower_bounds (a := a) hk hlo hupp
    have hpow_lower : ((9 : ℝ) ^ k) ≤ X ^ decimalExponent := by
      calc
        (9 : ℝ) ^ k = ((10 ^ k : ℕ) : ℝ) ^ decimalExponent :=
          (decimalPower_rpow k).symm
        _ ≤ X ^ decimalExponent :=
          Real.rpow_le_rpow (by positivity) hlo hbpos.le
    have hpow_upper : X ^ decimalExponent < (9 : ℝ) ^ (k + 1) := by
      calc
        X ^ decimalExponent < ((10 ^ (k + 1) : ℕ) : ℝ) ^ decimalExponent :=
          Real.rpow_lt_rpow (by positivity) hupp hbpos
        _ = (9 : ℝ) ^ (k + 1) := decimalPower_rpow (k + 1)
    have hcount_lower : ((9 : ℝ) ^ k) ≤ (restrictedCount a X : ℝ) := by
      exact_mod_cast hcounts.1
    have hcount_upper : (restrictedCount a X : ℝ) ≤
        2 * (9 : ℝ) ^ (k + 1) := by
      exact_mod_cast hcounts.2
    rw [pow_succ] at hpow_upper hcount_upper
    have hkpow : 0 < (9 : ℝ) ^ k := by positivity
    have hxpow : 0 < X ^ decimalExponent := by positivity
    constructor <;> nlinarith

theorem restrictedCount_div_log_rpow_comparable
    {a : Fin 10} {X : ℝ} (hX : 4 ≤ X) :
    (1 / 100 : ℝ) *
          (X ^ (Real.log (9 : ℝ) / Real.log (10 : ℝ)) / Real.log X) <
        (restrictedCount a X : ℝ) / Real.log X ∧
      (restrictedCount a X : ℝ) / Real.log X <
        100 * (X ^ (Real.log (9 : ℝ) / Real.log (10 : ℝ)) / Real.log X) := by
  have hcount := restrictedCount_rpow_comparable (a := a) hX
  have hlog := log_pos_of_four_le hX
  constructor
  · rw [← mul_div_assoc]
    exact (div_lt_div_iff_of_pos_right hlog).2 hcount.1
  · rw [← mul_div_assoc]
    exact (div_lt_div_iff_of_pos_right hlog).2 hcount.2

end PrimesRestrictedDigits
