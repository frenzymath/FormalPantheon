import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Standard additive characters on translated integer intervals

This file proves the geometric-series and reciprocal-sine steps in
DavenportMNTCh23PV1980, printed p. 136. The sharp sum over all nonzero
frequencies remains a separate theorem.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

open AddChar Finset

private theorem sum_Ioc_int_eq_sum_range_add_succ
    {A : Type*} [AddCommMonoid A] (f : ℤ → A) (M : ℤ) (N : ℕ) :
    (∑ m ∈ Finset.Ioc M (M + (N : ℤ)), f m) =
      ∑ n ∈ Finset.range N, f (M + (n + 1 : ℕ)) := by
  rw [Int.Ioc_eq_finset_map, Finset.sum_map]
  simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply,
    addLeftEmbedding_apply]
  congr 1
  · simp
  · funext n
    congr 1
    push_cast
    ring

private theorem stdAddChar_mul_int_add_succ {q : ℕ} [NeZero q]
    (a : ZMod q) (M : ℤ) (n : ℕ) :
    ZMod.stdAddChar (a * ((M + ((n + 1 : ℕ) : ℤ) : ℤ) : ZMod q)) =
      ZMod.stdAddChar (a * ((M + 1 : ℤ) : ZMod q)) *
        ZMod.stdAddChar a ^ n := by
  rw [← AddChar.map_nsmul_eq_pow, ← AddChar.map_add_eq_mul]
  congr 1
  push_cast
  simp only [nsmul_eq_mul]
  ring

private theorem stdAddChar_ne_one_of_ne_zero
    {q : ℕ} [NeZero q] {a : ZMod q} (ha : a ≠ 0) :
    ZMod.stdAddChar a ≠ 1 := by
  intro h
  apply ha
  apply ZMod.injective_stdAddChar
  simpa only [AddChar.map_zero_eq_one] using h

private theorem norm_stdAddChar_sub_one_eq_two_mul_abs_sin
    {q : ℕ} [NeZero q] (a : ZMod q) :
    ‖ZMod.stdAddChar a - 1‖ =
      2 * |Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ))| := by
  rw [← ZMod.natCast_zmod_val a]
  rw [show (a.val : ZMod q) = ((a.val : ℤ) : ZMod q) by simp,
    ZMod.stdAddChar_coe]
  simp only [Int.cast_natCast]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (a.val : ℂ) / (q : ℂ) =
      Complex.I * ((2 * Real.pi * (a.val : ℝ) / (q : ℝ) : ℝ) : ℂ) by
        push_cast
        ring]
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  simp only [show (2 * Real.pi * (a.val : ℝ) / (q : ℝ)) / 2 =
    Real.pi * (a.val : ℝ) / (q : ℝ) by ring]
  rw [Real.norm_eq_abs, abs_mul]
  norm_num

/-- The standard additive character on `M < n ≤ M + N` is a translated
finite geometric progression. -/
theorem sum_stdAddChar_Ioc_eq_geometric
    {q : ℕ} [NeZero q] {a : ZMod q} (ha : a ≠ 0)
    (M : ℤ) (N : ℕ) :
    (∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
      ZMod.stdAddChar (a * (n : ZMod q))) =
      ZMod.stdAddChar (a * ((M + 1 : ℤ) : ZMod q)) *
        ((1 - ZMod.stdAddChar (a * (N : ZMod q))) /
          (1 - ZMod.stdAddChar a)) := by
  rw [sum_Ioc_int_eq_sum_range_add_succ]
  simp_rw [stdAddChar_mul_int_add_succ]
  rw [← Finset.mul_sum, geom_sum_eq (stdAddChar_ne_one_of_ne_zero ha)]
  have hpow : ZMod.stdAddChar (a * (N : ZMod q)) =
      ZMod.stdAddChar a ^ N := by
    rw [show a * (N : ZMod q) = N • a by ring,
      AddChar.map_nsmul_eq_pow]
  rw [hpow]
  congr 1
  rw [div_eq_mul_inv, div_eq_mul_inv,
    show ZMod.stdAddChar a - 1 = -(1 - ZMod.stdAddChar a) by ring,
    inv_neg]
  ring

/-- A nonzero standard additive frequency has the reciprocal-sine interval
bound used in the proof of Pólya--Vinogradov. -/
theorem norm_sum_stdAddChar_Ioc_le_inv_sin
    {q : ℕ} [NeZero q] {a : ZMod q} (ha : a ≠ 0)
    (M : ℤ) (N : ℕ) :
    ‖∑ n ∈ Finset.Ioc M (M + (N : ℤ)),
      ZMod.stdAddChar (a * (n : ZMod q))‖ ≤
      (Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ)))⁻¹ := by
  have hqpos : (0 : ℝ) < q := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have havalpos : (0 : ℝ) < a.val := by
    exact_mod_cast Nat.pos_of_ne_zero ((ZMod.val_ne_zero a).mpr ha)
  have hanglepos : 0 < Real.pi * (a.val : ℝ) / (q : ℝ) :=
    div_pos (mul_pos Real.pi_pos havalpos) hqpos
  have hanglelt : Real.pi * (a.val : ℝ) / (q : ℝ) < Real.pi := by
    rw [div_lt_iff₀ hqpos]
    have havallt : (a.val : ℝ) < q := by exact_mod_cast a.val_lt
    nlinarith [Real.pi_pos]
  have hsin : 0 < Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ)) :=
    Real.sin_pos_of_pos_of_lt_pi hanglepos hanglelt
  have hnum : ‖1 - ZMod.stdAddChar (a * (N : ZMod q))‖ ≤ 2 := by
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖ZMod.stdAddChar (a * (N : ZMod q))‖ :=
        norm_sub_le _ _
      _ = 2 := by rw [AddChar.norm_apply]; norm_num
  have hdenom : ‖1 - ZMod.stdAddChar a‖ =
      2 * Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ)) := by
    rw [show (1 : ℂ) - ZMod.stdAddChar a =
      -(ZMod.stdAddChar a - 1) by ring, norm_neg,
      norm_stdAddChar_sub_one_eq_two_mul_abs_sin,
      abs_of_pos hsin]
  rw [sum_stdAddChar_Ioc_eq_geometric ha, norm_mul,
    AddChar.norm_apply, one_mul, norm_div, hdenom]
  calc
    ‖1 - ZMod.stdAddChar (a * (N : ZMod q))‖ /
        (2 * Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ))) ≤
        2 / (2 * Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ))) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = (Real.sin (Real.pi * (a.val : ℝ) / (q : ℝ)))⁻¹ := by
      field_simp

end BoundedGaps.Maynard
