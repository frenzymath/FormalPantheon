import PrimesRestrictedDigits.TypeI.LargeScaleThreshold
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.NormNum

/-!
# Logarithmic counts for Type I decimal scales

This makes explicit the two logarithmic losses suppressed after equation (8.1): one from the
real-capped scale family and one from the harmonic sum.
-/

namespace PrimesRestrictedDigits

private theorem typeIDecimalLength_cast_le_log (length : Nat) :
    (length : Real) ≤ Real.log (((10 ^ length : Nat) : Real)) := by
  have hlogTen : (1 : Real) ≤ Real.log 10 := by
    apply (Real.le_log_iff_exp_le (by norm_num)).2
    exact Real.exp_one_lt_three.le.trans (by norm_num)
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  rw [Real.log_pow]
  calc
    (length : Real) = (length : Real) * 1 := by ring
    _ ≤ (length : Real) * Real.log 10 :=
      mul_le_mul_of_nonneg_left hlogTen (by positivity)

/-- A positive decimal length has natural logarithmic scale at least one. -/
theorem one_le_log_typeIDecimalScale
    {length : Nat} (hlength : 1 ≤ length) :
    (1 : Real) ≤ Real.log (((10 ^ length : Nat) : Real)) := by
  have hlengthReal : (1 : Real) ≤ length := by exact_mod_cast hlength
  exact hlengthReal.trans (typeIDecimalLength_cast_le_log length)

private theorem typeIHarmonic_mono_cast {m n : Nat} (hmn : m ≤ n) :
    (harmonic m : Real) ≤ (harmonic n : Real) := by
  simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    rw [Finset.mem_Icc] at hk ⊢
    exact ⟨hk.1, hk.2.trans hmn⟩
  · intro k hk hnot
    positivity

private theorem typeICeil_le_decimalScale
    {length : Nat} {Q : Real}
    (hQ : Q ≤ ((10 ^ length : Nat) : Real)) :
    Nat.ceil Q ≤ 10 ^ length := by
  have hceil := Nat.ceil_mono hQ
  simpa only [Nat.ceil_natCast] using hceil

/--
The weak ambient level bounds the active scale count by the decimal length plus the two
conservative candidates.
-/
theorem card_typeIDecadeScalesBelow_le_length_add_two
    {length : Nat} {Q : Real}
    (hQ : Q ≤ ((10 ^ length : Nat) : Real)) :
    (typeIDecadeScalesBelow Q).card ≤ length + 2 := by
  have hceil := typeICeil_le_decimalScale hQ
  have hclog := Nat.clog_mono_right 10 hceil
  rw [Nat.clog_pow 10 length (by norm_num)] at hclog
  exact (card_typeIDecadeScalesBelow_le Q).trans
    (Nat.add_le_add_right hclog 2)

/-- At positive decimal length, the active scale count costs at most three
natural logarithms. -/
theorem card_typeIDecadeScalesBelow_cast_le_three_log
    {length : Nat} {Q : Real} (hlength : 1 ≤ length)
    (hQ : Q ≤ ((10 ^ length : Nat) : Real)) :
    ((typeIDecadeScalesBelow Q).card : Real) ≤
      3 * Real.log (((10 ^ length : Nat) : Real)) := by
  have hcardNat := card_typeIDecadeScalesBelow_le_length_add_two hQ
  have hcardReal : ((typeIDecadeScalesBelow Q).card : Real) ≤
      ((length + 2 : Nat) : Real) := by
    exact_mod_cast hcardNat
  have hlengthThreeNat : length + 2 ≤ 3 * length := by omega
  have hlengthThreeReal : ((length + 2 : Nat) : Real) ≤
      3 * (length : Real) := by
    exact_mod_cast hlengthThreeNat
  have hlengthLog := typeIDecimalLength_cast_le_log length
  calc
    ((typeIDecadeScalesBelow Q).card : Real) ≤
        ((length + 2 : Nat) : Real) := hcardReal
    _ ≤ 3 * (length : Real) := hlengthThreeReal
    _ ≤ 3 * Real.log (((10 ^ length : Nat) : Real)) := by linarith

/--
The harmonic factor costs at most two logarithms under the same weak ambient level.
-/
theorem harmonic_ceil_sub_one_le_two_log_decimalScale
    {length : Nat} {Q : Real} (hlength : 1 ≤ length)
    (hQ : Q ≤ ((10 ^ length : Nat) : Real)) :
    (harmonic (Nat.ceil Q - 1) : Real) ≤
      2 * Real.log (((10 ^ length : Nat) : Real)) := by
  have hceil := typeICeil_le_decimalScale hQ
  have hindex : Nat.ceil Q - 1 ≤ 10 ^ length :=
    (Nat.sub_le (Nat.ceil Q) 1).trans hceil
  have honeLog := one_le_log_typeIDecimalScale hlength
  calc
    (harmonic (Nat.ceil Q - 1) : Real) ≤
        (harmonic (10 ^ length) : Real) := typeIHarmonic_mono_cast hindex
    _ ≤ 1 + Real.log (((10 ^ length : Nat) : Real)) :=
      harmonic_le_one_add_log (10 ^ length)
    _ ≤ 2 * Real.log (((10 ^ length : Nat) : Real)) := by linarith

end PrimesRestrictedDigits
