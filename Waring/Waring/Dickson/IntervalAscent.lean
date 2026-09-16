import Waring.Dickson.NthRootGap

/-!
# Dickson's one-step interval ascent

This file proves the real-endpoint form of Theorem 11 in
[DICKSON1933, p. 710].
-/

namespace Waring

open Statement

/-- Dickson's Theorem 11: if an `n`th-power representation covers an inclusive
natural interval containing every natural strictly below `lower + L`, then one
additional power covers every natural target through
`sigma = (L / n) ^ (n / (n - 1))`.

The hypothesis `lower + L <= baseUpper + 1` is the exact conversion from the
strict real remainder bound to the inclusive natural endpoint `baseUpper`.
-/
theorem dickson_interval_ascent {n slots lower baseUpper : Nat} {L sigma : Real}
    (hn : 1 < n) (hL : 0 < L)
    (hsigma : sigma =
      (L / (n : Real)) ^ ((n : Real) / ((n - 1 : Nat) : Real)))
    (hlowerSigma : (lower : Real) <= sigma)
    (hbaseUpper : (lower : Real) + L <= ((baseUpper + 1 : Nat) : Real))
    (hbase : RepresentsOn n slots lower baseUpper) :
    forall target : Nat, lower <= target -> (target : Real) <= sigma ->
      HasPowerSumRepresentation n (slots + 1) target := by
  have hnNatPos : 0 < n := Nat.zero_lt_of_lt hn
  have hnRealPos : 0 < (n : Real) := by exact_mod_cast hnNatPos
  have hnSubNatPos : 0 < n - 1 := Nat.sub_pos_of_lt hn
  have hnSubRealPos : 0 < ((n - 1 : Nat) : Real) := by
    exact_mod_cast hnSubNatPos
  have hbasePos : 0 < L / (n : Real) := div_pos hL hnRealPos
  have hsigmaNonneg : 0 <= sigma :=
    (Nat.cast_nonneg lower).trans hlowerSigma
  have hexponentPos :
      0 < (((n - 1 : Nat) : Real) / (n : Real)) :=
    div_pos hnSubRealPos hnRealPos
  have hscale :
      (n : Real) *
          sigma ^ (((n - 1 : Nat) : Real) / (n : Real)) = L := by
    rw [hsigma, ← Real.rpow_mul hbasePos.le]
    have hexponents :
        ((n : Real) / ((n - 1 : Nat) : Real)) *
            (((n - 1 : Nat) : Real) / (n : Real)) = 1 := by
      field_simp
    rw [hexponents, Real.rpow_one]
    field_simp
  have hlowerBase : lower <= baseUpper := by
    rw [← Nat.lt_add_one_iff]
    exact_mod_cast
      (lt_of_lt_of_le (lt_add_of_pos_right (lower : Real) hL) hbaseUpper)
  intro target htargetLower htargetSigma
  apply (representsOn_succ_of_remainders hbase ?_)
    target htargetLower le_rfl
  intro m hmLower hmTarget
  have hmSigma : (m : Real) <= sigma := by
    exact (Nat.cast_le.mpr hmTarget).trans htargetSigma
  by_cases hmEq : m = lower
  · subst m
    refine ⟨0, ?_, ?_, ?_⟩
    · simp [Nat.ne_of_gt hnNatPos]
    · simp [Nat.ne_of_gt hnNatPos]
    · simpa [Nat.ne_of_gt hnNatPos] using hlowerBase
  · have hlowerM : lower < m := lt_of_le_of_ne hmLower (Ne.symm hmEq)
    obtain ⟨a, -, haPow, hremLower, hremLt⟩ :=
      exists_pos_power_remainder_lt hnNatPos hlowerM
    refine ⟨a, haPow, hremLower, ?_⟩
    have hpowerMono :
        (m : Real) ^ (((n - 1 : Nat) : Real) / (n : Real)) <=
          sigma ^ (((n - 1 : Nat) : Real) / (n : Real)) :=
      (Real.rpow_le_rpow_iff (Nat.cast_nonneg m) hsigmaNonneg hexponentPos).mpr
        hmSigma
    have hremReal :
        ((m - a ^ n : Nat) : Real) < (lower : Real) + L := by
      calc
        ((m - a ^ n : Nat) : Real) <
            (lower : Real) + (n : Real) *
              (m : Real) ^ (((n - 1 : Nat) : Real) / (n : Real)) := hremLt
        _ <= (lower : Real) + (n : Real) *
              sigma ^ (((n - 1 : Nat) : Real) / (n : Real)) := by
          exact add_le_add le_rfl
            (mul_le_mul_of_nonneg_left hpowerMono hnRealPos.le)
        _ = (lower : Real) + L := by rw [hscale]
    have hremSucc : m - a ^ n < baseUpper + 1 := by
      exact_mod_cast hremReal.trans_le hbaseUpper
    exact Nat.lt_add_one_iff.mp hremSucc

end Waring
