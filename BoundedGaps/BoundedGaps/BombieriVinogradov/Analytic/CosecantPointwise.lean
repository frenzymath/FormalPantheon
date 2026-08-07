import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The pointwise Montgomery--Vaughan cosecant majorant

This file proves the finite-valued content of Lemma 1 of
MontgomeryVaughanHilbert1974, Section 2, p. 76.
The argument uses a fresh calculus proof of the required quartic cosine
bound and keeps the formal finite-valued non-pole restriction explicit. See SEM-445.
-/

namespace BoundedGaps.Maynard

/-- The real cosecant of `pi * x`, used with a real frequency lift. -/
noncomputable def cosecantPi (x : ℝ) : ℝ :=
  (Real.sin (Real.pi * x))⁻¹

private theorem cos_le_quartic {t : ℝ} (ht : 0 ≤ t) :
    Real.cos t ≤ 1 - t ^ 2 / 2 + t ^ 4 / 24 := by
  let f : ℝ → ℝ := fun y => 1 - y ^ 2 / 2 + y ^ 4 / 24 - Real.cos y
  have hderiv (y : ℝ) :
      deriv f y = Real.sin y - (y - y ^ 3 / 6) := by
    simp (disch := fun_prop) [f]
    ring
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro y hy
    rw [hderiv]
    exact sub_nonneg.mpr (Real.sin_ge_sub_cube (interior_subset hy))
  have h := hmono (by simp) ht ht
  norm_num [f] at h
  linarith

private theorem trig_core {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ Real.pi / 2) :
    t ^ 2 * (1 + 2 * |Real.cos t|) ≤ 3 * Real.sin t ^ 2 := by
  have hcos0 : 0 ≤ Real.cos t :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      (by linarith [Real.pi_pos]) ht
  rw [abs_of_nonneg hcos0]
  have hcos := cos_le_quartic ht0
  have hsin := Real.sin_ge_sub_cube ht0
  have hsin0 : 0 ≤ Real.sin t :=
    Real.sin_nonneg_of_nonneg_of_le_pi ht0
      (ht.trans (by linarith [Real.pi_pos]))
  have ht_two : t ≤ 2 := by linarith [Real.pi_lt_four]
  have hpoly0 : 0 ≤ t - t ^ 3 / 6 := by
    nlinarith [sq_nonneg t, mul_self_le_mul_self ht0 ht_two]
  have hsq : (t - t ^ 3 / 6) ^ 2 ≤ Real.sin t ^ 2 := by
    nlinarith
  nlinarith [sq_nonneg t]

private theorem abs_sin_pi_eq_sin_pi_norm (x : ℝ) :
    |Real.sin (Real.pi * x)| =
      Real.sin (Real.pi * ‖(x : UnitAddCircle)‖) := by
  let z : ℝ := x - (round x : ℝ)
  have hzabs : |z| = ‖(x : UnitAddCircle)‖ := by
    simp only [z, UnitAddCircle.norm_eq]
  have hzle : |Real.pi * z| ≤ Real.pi := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    have := abs_sub_round x
    nlinarith [Real.pi_pos]
  have hlocal : |Real.sin (Real.pi * z)| = Real.sin (Real.pi * |z|) := by
    rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi hzle]
    rw [abs_mul, abs_of_pos Real.pi_pos]
  have hshift := Real.sin_sub_int_mul_pi (Real.pi * x) (round x)
  have habs := congrArg abs hshift
  rw [show Real.pi * x - (round x : ℝ) * Real.pi = Real.pi * z by
    simp [z]
    ring] at habs
  have hsign : |((-1 : ℝ) ^ (round x))| = 1 := by
    rw [abs_zpow]
    simp
  rw [abs_mul, hsign, one_mul] at habs
  rw [← habs, hlocal, hzabs]

private theorem abs_cos_pi_eq_cos_pi_norm (x : ℝ) :
    |Real.cos (Real.pi * x)| =
      Real.cos (Real.pi * ‖(x : UnitAddCircle)‖) := by
  let z : ℝ := x - (round x : ℝ)
  have hzabs : |z| = ‖(x : UnitAddCircle)‖ := by
    simp only [z, UnitAddCircle.norm_eq]
  have htheta : Real.pi * |z| ≤ Real.pi / 2 := by
    have := abs_sub_round x
    dsimp [z]
    nlinarith [Real.pi_pos]
  have hcos0 : 0 ≤ Real.cos (Real.pi * |z|) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      (by
        have : 0 ≤ Real.pi * |z| := by positivity
        linarith [Real.pi_pos]) htheta
  have hlocal : |Real.cos (Real.pi * z)| = Real.cos (Real.pi * |z|) := by
    rw [← Real.cos_abs]
    rw [abs_mul, abs_of_pos Real.pi_pos, abs_of_nonneg hcos0]
  have hshift := Real.cos_sub_int_mul_pi (Real.pi * x) (round x)
  have habs := congrArg abs hshift
  rw [show Real.pi * x - (round x : ℝ) * Real.pi = Real.pi * z by
    simp [z]
    ring] at habs
  have hsign : |((-1 : ℝ) ^ (round x))| = 1 := by
    rw [abs_zpow]
    simp
  rw [abs_mul, hsign, one_mul] at habs
  rw [← habs, hlocal, hzabs]

private theorem cosecantPi_sq_mul_one_add_two_abs_cos_le
    (x : ℝ) (hx : (x : UnitAddCircle) ≠ 0) :
    cosecantPi x ^ 2 * (1 + 2 * |Real.cos (Real.pi * x)|) ≤
      3 / (Real.pi ^ 2 * ‖(x : UnitAddCircle)‖ ^ 2) := by
  let d : ℝ := ‖(x : UnitAddCircle)‖
  let t : ℝ := Real.pi * d
  have hd0 : 0 < d := norm_pos_iff.mpr hx
  have hdhalf : d ≤ 1 / 2 := by
    simpa [d] using
      (AddCircle.norm_le_half_period (1 : ℝ) one_ne_zero
        (x := (x : UnitAddCircle)))
  have ht0 : 0 ≤ t := by positivity
  have ht : t ≤ Real.pi / 2 := by
    dsimp [t]
    nlinarith [Real.pi_pos]
  have hsinpos : 0 < Real.sin t := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · linarith [Real.pi_pos]
  have htrig := trig_core ht0 ht
  have hcost0 : 0 ≤ Real.cos t :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      (by linarith [Real.pi_pos]) ht
  rw [abs_of_nonneg hcost0] at htrig
  have hsinequal : |Real.sin (Real.pi * x)| = Real.sin t := by
    simpa [t, d] using abs_sin_pi_eq_sin_pi_norm x
  have hcosequal : |Real.cos (Real.pi * x)| = Real.cos t := by
    simpa [t, d] using abs_cos_pi_eq_cos_pi_norm x
  have hpi : 0 < Real.pi := Real.pi_pos
  change cosecantPi x ^ 2 * (1 + 2 * |Real.cos (Real.pi * x)|) ≤
    3 / (Real.pi ^ 2 * d ^ 2)
  rw [hcosequal]
  simp only [cosecantPi]
  rw [← sq_abs (Real.sin (Real.pi * x))⁻¹, abs_inv, hsinequal]
  rw [inv_pow, inv_mul_eq_div]
  rw [div_le_div_iff₀ (sq_pos_of_pos hsinpos)
    (mul_pos (sq_pos_of_pos hpi) (sq_pos_of_pos hd0))]
  dsimp [t] at htrig
  nlinarith

/-- Montgomery--Vaughan's exact pointwise csc/cot majorant. The quotient
nonzero hypothesis is the formal finite-valued restriction excluding poles. -/
theorem cosecant_cotangent_majorant
    (x : ℝ) (hx : (x : UnitAddCircle) ≠ 0) :
    cosecantPi x ^ 2 +
        2 * |Real.cot (Real.pi * x) * cosecantPi x| ≤
      3 / (Real.pi ^ 2 * ‖(x : UnitAddCircle)‖ ^ 2) := by
  have hfactor := cosecantPi_sq_mul_one_add_two_abs_cos_le x hx
  convert hfactor using 1
  rw [Real.cot_eq_cos_div_sin, div_eq_mul_inv]
  simp only [cosecantPi]
  rw [abs_mul, abs_mul]
  have habs :
      |(Real.sin (Real.pi * x))⁻¹| * |(Real.sin (Real.pi * x))⁻¹| =
        (Real.sin (Real.pi * x))⁻¹ ^ 2 := by
    rw [← sq, sq_abs]
  rw [mul_assoc, habs]
  ring

end BoundedGaps.Maynard
