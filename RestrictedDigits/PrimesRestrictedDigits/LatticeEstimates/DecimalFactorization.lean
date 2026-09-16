import PrimesRestrictedDigits.PrimeNumberTheorem.DecimalSmooth

/-!
# Decimal and coprime parts of a positive natural

This is the exact elementary factorization called "the part not coprime to 10" in
`MAYNARD-PRD-PUBLISHED`, Lemma 14.3, pp. 202--203.
-/

namespace PrimesRestrictedDigits

/-- A positive natural is a decimal-smooth factor times a positive factor
coprime to ten. -/
theorem exists_decimalSmooth_mul_coprime_ten
    (n : Nat) (hn : 0 < n) :
    exists d q : Nat, 0 < d ∧ 0 < q ∧ IsDecimalSmooth d ∧
      q.Coprime 10 ∧ d * q = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases htwo : 2 ∣ n
      · have htwoLe : 2 <= n := Nat.le_of_dvd hn htwo
        have hquotPos : 0 < n / 2 := Nat.div_pos htwoLe (by norm_num)
        obtain ⟨d, q, hd, hq, hdSmooth, hqCoprime, hdq⟩ :=
          ih (n / 2) (Nat.div_lt_self hn (by norm_num)) hquotPos
        refine ⟨2 * d, q, Nat.mul_pos (by norm_num) hd, hq, ?_, hqCoprime, ?_⟩
        · rw [isDecimalSmooth_iff_exists_two_pow_mul_five_pow] at hdSmooth ⊢
          obtain ⟨a, b, rfl⟩ := hdSmooth
          exact ⟨a + 1, b, by rw [pow_add, pow_one]; ring⟩
        · calc
            (2 * d) * q = 2 * (d * q) := by ring
            _ = 2 * (n / 2) := by rw [hdq]
            _ = n := Nat.mul_div_cancel' htwo
      · by_cases hfive : 5 ∣ n
        · have hfiveLe : 5 <= n := Nat.le_of_dvd hn hfive
          have hquotPos : 0 < n / 5 := Nat.div_pos hfiveLe (by norm_num)
          obtain ⟨d, q, hd, hq, hdSmooth, hqCoprime, hdq⟩ :=
            ih (n / 5) (Nat.div_lt_self hn (by norm_num)) hquotPos
          refine ⟨5 * d, q, Nat.mul_pos (by norm_num) hd, hq, ?_, hqCoprime, ?_⟩
          · rw [isDecimalSmooth_iff_exists_two_pow_mul_five_pow] at hdSmooth ⊢
            obtain ⟨a, b, rfl⟩ := hdSmooth
            exact ⟨a, b + 1, by rw [pow_add, pow_one]; ring⟩
          · calc
              (5 * d) * q = 5 * (d * q) := by ring
              _ = 5 * (n / 5) := by rw [hdq]
              _ = n := Nat.mul_div_cancel' hfive
        · refine ⟨1, n, by norm_num, hn, ?_, ?_, by simp⟩
          · exact (isDecimalSmooth_iff_exists_two_pow_mul_five_pow 1).2
              ⟨0, 0, by norm_num⟩
          · rw [show 10 = 2 * 5 by norm_num, Nat.coprime_mul_iff_right]
            exact ⟨(Nat.prime_two.coprime_iff_not_dvd.mpr htwo).symm,
              (Nat.prime_five.coprime_iff_not_dvd.mpr hfive).symm⟩

end PrimesRestrictedDigits
