import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The sharp reciprocal-sine aggregate

This file proves the finite reciprocal-sine estimate used in DavenportMNTCh23PV1980,
printed p. 136. Sine symmetry and Jordan's inequality reduce the estimate to
sharp elementary bounds for harmonic numbers.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

open Finset

private theorem harmonic_cast_le_log_two_mul_add_one (n : ℕ) :
    (harmonic n : ℝ) ≤ Real.log (2 * (n : ℝ) + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [harmonic_succ]
      simp only [Rat.cast_add, Rat.cast_inv, Rat.cast_natCast, Nat.cast_succ]
      have hden : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
      have hlog := Real.le_log_one_add_of_nonneg
        (show (0 : ℝ) ≤ 2 / (2 * (n : ℝ) + 1) by positivity)
      have hincrement :
          ((n : ℝ) + 1)⁻¹ ≤
            Real.log (2 * ((n : ℝ) + 1) + 1) -
              Real.log (2 * (n : ℝ) + 1) := by
        rw [← Real.log_div (by positivity) hden.ne']
        convert hlog using 1 <;> field_simp <;> ring_nf
      linarith

private theorem harmonic_cast_lt_log_two_mul_add_one {n : ℕ} (hn : 0 < n) :
    (harmonic n : ℝ) < Real.log (2 * (n : ℝ) + 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [harmonic_succ]
  simp only [Rat.cast_add, Rat.cast_inv, Rat.cast_natCast, Nat.cast_succ]
  have hbase := harmonic_cast_le_log_two_mul_add_one n
  have hden : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  have hlog := Real.lt_log_one_add_of_pos
    (show (0 : ℝ) < 2 / (2 * (n : ℝ) + 1) by positivity)
  have hincrement :
      ((n : ℝ) + 1)⁻¹ <
        Real.log (2 * ((n : ℝ) + 1) + 1) -
          Real.log (2 * (n : ℝ) + 1) := by
    rw [← Real.log_div (by positivity) hden.ne']
    convert hlog using 1 <;> field_simp <;> ring_nf
  linarith

private theorem harmonic_cast_pred_add_inv_two_mul_lt_log_two_mul
    {m : ℕ} (hm : 0 < m) :
    (harmonic (m - 1) : ℝ) + (((2 * m : ℕ) : ℝ))⁻¹ <
      Real.log (((2 * m : ℕ) : ℝ)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  simp only [Nat.succ_sub_one, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_succ]
  have hbase := harmonic_cast_le_log_two_mul_add_one m
  have hden : (0 : ℝ) < 2 * (m : ℝ) + 1 := by positivity
  have hx : (0 : ℝ) < (2 * (m : ℝ) + 1)⁻¹ := by positivity
  have hlog := Real.lt_log_one_add_of_pos hx
  have hincrement :
      (2 * ((m : ℝ) + 1))⁻¹ <
        Real.log (2 * ((m : ℝ) + 1)) -
          Real.log (2 * (m : ℝ) + 1) := by
    rw [← Real.log_div (by positivity) hden.ne']
    calc
      (2 * ((m : ℝ) + 1))⁻¹ <
          2 * (2 * (m : ℝ) + 1)⁻¹ /
            ((2 * (m : ℝ) + 1)⁻¹ + 2) := by
        field_simp
        linarith
      _ < Real.log (1 + (2 * (m : ℝ) + 1)⁻¹) := hlog
      _ = Real.log (2 * ((m : ℝ) + 1) / (2 * (m : ℝ) + 1)) := by
        congr 1
        field_simp
        ring
  linarith

private noncomputable def reciprocalSineTerm (q a : ℕ) : ℝ :=
  (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹

private theorem reciprocalSineTerm_le_div {q a : ℕ} (hq : 0 < q)
    (ha : 0 < a) (haq : 2 * a ≤ q) :
    reciprocalSineTerm q a ≤ (q : ℝ) / (2 * (a : ℝ)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hangle0 : 0 ≤ Real.pi * (a : ℝ) / (q : ℝ) := by positivity
  have hanglehalf : Real.pi * (a : ℝ) / (q : ℝ) ≤ Real.pi / 2 := by
    rw [div_le_div_iff₀ hqR zero_lt_two]
    have haqR : (2 : ℝ) * (a : ℝ) ≤ q := by exact_mod_cast haq
    nlinarith [Real.pi_pos]
  have hjordan := Real.mul_le_sin hangle0 hanglehalf
  have hbase : 0 < 2 / Real.pi *
      (Real.pi * (a : ℝ) / (q : ℝ)) := by positivity
  have hinv := inv_anti₀ hbase hjordan
  calc
    reciprocalSineTerm q a =
        (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ := rfl
    _ ≤ (2 / Real.pi * (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ := hinv
    _ = (q : ℝ) / (2 * (a : ℝ)) := by field_simp

private theorem reciprocalSineTerm_sub {q a : ℕ} (hq : 0 < q) (ha : a ≤ q) :
    reciprocalSineTerm q (q - a) = reciprocalSineTerm q a := by
  rw [reciprocalSineTerm, reciprocalSineTerm, Nat.cast_sub ha]
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  rw [show Real.pi * ((q : ℝ) - (a : ℝ)) / (q : ℝ) =
      Real.pi - Real.pi * (a : ℝ) / (q : ℝ) by field_simp,
    Real.sin_pi_sub]

private theorem reciprocalSineTerm_two_mul_self {m : ℕ} (hm : 0 < m) :
    reciprocalSineTerm (2 * m) m = 1 := by
  rw [reciprocalSineTerm]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  rw [show Real.pi * (m : ℝ) / ((2 * m : ℕ) : ℝ) = Real.pi / 2 by
      push_cast
      field_simp,
    Real.sin_pi_div_two, inv_one]

private theorem sum_Ico_inv_eq_harmonic (n : ℕ) :
    (∑ a ∈ Finset.Ico 1 (n + 1), ((a : ℝ))⁻¹) = (harmonic n : ℝ) := by
  rw [Finset.Ico_add_one_right_eq_Icc]
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

private theorem sum_reciprocalSine_Ico_le_half_mul_harmonic
    {q m : ℕ} (hq : 0 < q) (hmq : 2 * m ≤ q) :
    (∑ a ∈ Finset.Ico 1 (m + 1), reciprocalSineTerm q a) ≤
      (q : ℝ) / 2 * (harmonic m : ℝ) := by
  calc
    (∑ a ∈ Finset.Ico 1 (m + 1), reciprocalSineTerm q a) ≤
        ∑ a ∈ Finset.Ico 1 (m + 1), (q : ℝ) / (2 * (a : ℝ)) := by
      apply Finset.sum_le_sum
      intro a ha
      exact reciprocalSineTerm_le_div hq (Finset.mem_Ico.mp ha).1
        ((Nat.mul_le_mul_left 2
          (Nat.le_of_lt_succ (Finset.mem_Ico.mp ha).2)).trans hmq)
    _ = (q : ℝ) / 2 *
        ∑ a ∈ Finset.Ico 1 (m + 1), ((a : ℝ))⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      field_simp
    _ = (q : ℝ) / 2 * (harmonic m : ℝ) := by
      rw [sum_Ico_inv_eq_harmonic]

private theorem sum_reciprocalSine_odd_eq_two_mul (m : ℕ) :
    (∑ a ∈ Finset.Ico 1 (2 * m + 1), reciprocalSineTerm (2 * m + 1) a) =
      2 * ∑ a ∈ Finset.Ico 1 (m + 1), reciprocalSineTerm (2 * m + 1) a := by
  have hq : 0 < 2 * m + 1 := by omega
  have hreflect := Finset.sum_Ico_reflect
    (reciprocalSineTerm (2 * m + 1)) 1
    (m := m + 1) (n := 2 * m + 1) (by omega)
  have hb1 : 2 * m + 1 + 1 - (m + 1) = m + 1 := by omega
  have hb2 : 2 * m + 1 + 1 - 1 = 2 * m + 1 := by omega
  rw [hb1, hb2] at hreflect
  have hupper :
      (∑ a ∈ Finset.Ico (m + 1) (2 * m + 1),
        reciprocalSineTerm (2 * m + 1) a) =
        ∑ a ∈ Finset.Ico 1 (m + 1), reciprocalSineTerm (2 * m + 1) a := by
    rw [← hreflect]
    apply Finset.sum_congr rfl
    intro a ha
    apply reciprocalSineTerm_sub hq
    exact (Nat.le_of_lt_succ (Finset.mem_Ico.mp ha).2).trans (by omega)
  calc
    (∑ a ∈ Finset.Ico 1 (2 * m + 1), reciprocalSineTerm (2 * m + 1) a) =
        (∑ a ∈ Finset.Ico 1 (m + 1), reciprocalSineTerm (2 * m + 1) a) +
          ∑ a ∈ Finset.Ico (m + 1) (2 * m + 1),
            reciprocalSineTerm (2 * m + 1) a := by
      rw [Finset.sum_Ico_consecutive (reciprocalSineTerm (2 * m + 1))
        (by omega) (by omega)]
    _ = 2 * ∑ a ∈ Finset.Ico 1 (m + 1),
        reciprocalSineTerm (2 * m + 1) a := by rw [hupper]; ring

private theorem sum_reciprocalSine_even_eq_two_mul_add_one
    {m : ℕ} (hm : 0 < m) :
    (∑ a ∈ Finset.Ico 1 (2 * m), reciprocalSineTerm (2 * m) a) =
      2 * (∑ a ∈ Finset.Ico 1 m, reciprocalSineTerm (2 * m) a) + 1 := by
  have hq : 0 < 2 * m := Nat.mul_pos two_pos hm
  have hreflect := Finset.sum_Ico_reflect
    (reciprocalSineTerm (2 * m)) 1
    (m := m) (n := 2 * m) (by omega)
  have hb1 : 2 * m + 1 - m = m + 1 := by omega
  have hb2 : 2 * m + 1 - 1 = 2 * m := by omega
  rw [hb1, hb2] at hreflect
  have hupper :
      (∑ a ∈ Finset.Ico (m + 1) (2 * m), reciprocalSineTerm (2 * m) a) =
        ∑ a ∈ Finset.Ico 1 m, reciprocalSineTerm (2 * m) a := by
    rw [← hreflect]
    apply Finset.sum_congr rfl
    intro a ha
    apply reciprocalSineTerm_sub hq
    exact (Nat.le_of_lt (Finset.mem_Ico.mp ha).2).trans (by omega)
  have hrest :
      (∑ a ∈ Finset.Ico m (2 * m), reciprocalSineTerm (2 * m) a) =
        reciprocalSineTerm (2 * m) m +
          ∑ a ∈ Finset.Ico (m + 1) (2 * m), reciprocalSineTerm (2 * m) a := by
    calc
      _ = (∑ a ∈ Finset.Ico m (m + 1), reciprocalSineTerm (2 * m) a) +
          ∑ a ∈ Finset.Ico (m + 1) (2 * m), reciprocalSineTerm (2 * m) a := by
        rw [Finset.sum_Ico_consecutive (reciprocalSineTerm (2 * m))
          (by omega) (by omega)]
      _ = _ := by simp
  calc
    (∑ a ∈ Finset.Ico 1 (2 * m), reciprocalSineTerm (2 * m) a) =
        (∑ a ∈ Finset.Ico 1 m, reciprocalSineTerm (2 * m) a) +
          ∑ a ∈ Finset.Ico m (2 * m), reciprocalSineTerm (2 * m) a := by
      rw [Finset.sum_Ico_consecutive (reciprocalSineTerm (2 * m))
        (by omega) (by omega)]
    _ = 2 * (∑ a ∈ Finset.Ico 1 m, reciprocalSineTerm (2 * m) a) + 1 := by
      rw [hrest, hupper, reciprocalSineTerm_two_mul_self hm]
      ring

/-- Davenport's sharp sum of reciprocal sines over the nonzero natural
representatives modulo `q`; see DavenportMNTCh23PV1980, printed p. 136. -/
theorem sum_reciprocalSine_Ico_lt_mul_log {q : ℕ} (hq : 1 < q) :
    (∑ a ∈ Finset.Ico 1 q,
      (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹) <
      (q : ℝ) * Real.log (q : ℝ) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' q
  · have hm : 0 < m := by omega
    change (∑ a ∈ Finset.Ico 1 (2 * m), reciprocalSineTerm (2 * m) a) < _
    rw [sum_reciprocalSine_even_eq_two_mul_add_one hm]
    have hhalf := sum_reciprocalSine_Ico_le_half_mul_harmonic
      (q := 2 * m) (m := m - 1) (by omega) (by omega)
    have htop : m - 1 + 1 = m := Nat.sub_add_cancel hm
    rw [htop] at hhalf
    have hlog := harmonic_cast_pred_add_inv_two_mul_lt_log_two_mul hm
    calc
      2 * (∑ a ∈ Finset.Ico 1 m, reciprocalSineTerm (2 * m) a) + 1 ≤
          2 * (((2 * m : ℕ) : ℝ) / 2 * (harmonic (m - 1) : ℝ)) + 1 :=
        by
          simpa only [add_comm] using add_le_add_right
            (mul_le_mul_of_nonneg_left hhalf (show (0 : ℝ) ≤ 2 by norm_num)) 1
      _ = ((2 * m : ℕ) : ℝ) *
          ((harmonic (m - 1) : ℝ) + (((2 * m : ℕ) : ℝ))⁻¹) := by
        have htwoM : (((2 * m : ℕ) : ℝ)) ≠ 0 := by positivity
        field_simp
      _ < ((2 * m : ℕ) : ℝ) * Real.log (((2 * m : ℕ) : ℝ)) :=
        mul_lt_mul_of_pos_left hlog (by positivity)
  · have hm : 0 < m := by omega
    change (∑ a ∈ Finset.Ico 1 (2 * m + 1),
      reciprocalSineTerm (2 * m + 1) a) < _
    rw [sum_reciprocalSine_odd_eq_two_mul]
    have hhalf := sum_reciprocalSine_Ico_le_half_mul_harmonic
      (q := 2 * m + 1) (m := m) (by omega) (by omega)
    have hlog := harmonic_cast_lt_log_two_mul_add_one hm
    calc
      2 * (∑ a ∈ Finset.Ico 1 (m + 1), reciprocalSineTerm (2 * m + 1) a) ≤
          2 * (((2 * m + 1 : ℕ) : ℝ) / 2 * (harmonic m : ℝ)) :=
        mul_le_mul_of_nonneg_left hhalf (by norm_num)
      _ = ((2 * m + 1 : ℕ) : ℝ) * (harmonic m : ℝ) := by ring
      _ < ((2 * m + 1 : ℕ) : ℝ) * Real.log (((2 * m + 1 : ℕ) : ℝ)) := by
        apply mul_lt_mul_of_pos_left _ (by positivity)
        simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hlog

end BoundedGaps.Maynard
