import Waring.Analytic.ChenSevenResidue
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Affine integral normalization for Chen's Lemma 7

This file records the change of variables from the perturbation integral on
`[0, P]` to the unit-spaced parameter along one residue class modulo `q`.
-/

namespace Waring.Analytic

open scoped ComplexConjugate Interval

/-- The fifth-power perturbation phase after writing a real variable as
`q * s + r`. -/
noncomputable def residueAffinePhase
    (q : Nat) (z : Real) (r : Nat) (s : Real) : Real :=
  2 * Real.pi * z * ((q : Real) * s + r) ^ 5

/-- Negating the real frequency negates the affine residue phase. -/
@[simp]
theorem residueAffinePhase_neg
    (q : Nat) (z : Real) (r : Nat) (s : Real) :
    residueAffinePhase q (-z) r s = -residueAffinePhase q z r s := by
  simp [residueAffinePhase]

/-- Complex conjugation reverses the sign of a real residue phase. -/
theorem conj_exp_residueAffinePhase
    (q : Nat) (z : Real) (r : Nat) (s : Real) :
    conj (Complex.exp
      (Complex.I * (residueAffinePhase q z r s : Complex))) =
      Complex.exp
        (Complex.I * (residueAffinePhase q (-z) r s : Complex)) := by
  rw [← Complex.exp_conj]
  congr 1
  simp

/-- Conjugating an affine residue integral reverses the sign of its real
phase. -/
theorem conj_integral_exp_residueAffinePhase
    (q : Nat) (z : Real) (r : Nat) (a b : Real) :
    conj (∫ s in a..b,
        Complex.exp
          (Complex.I * (residueAffinePhase q z r s : Complex))) =
      ∫ s in a..b,
        Complex.exp
          (Complex.I * (residueAffinePhase q (-z) r s : Complex)) := by
  rw [← intervalIntegral.intervalIntegral_conj]
  apply intervalIntegral.integral_congr
  intro s _
  exact conj_exp_residueAffinePhase q z r s

/-- Conjugating the original perturbation integral reverses its real phase. -/
theorem conj_fifthPerturbationIntegral (z : Real) (P : Nat) :
    conj (fifthPerturbationIntegral z P) =
      fifthPerturbationIntegral (-z) P := by
  unfold fifthPerturbationIntegral
  rw [← intervalIntegral.intervalIntegral_conj]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [← Complex.exp_conj]
  congr 1
  apply Complex.ext <;> simp

/-- An integral of the affine residue phase is bounded by the length of its
interval, since its integrand lies on the unit circle. -/
theorem norm_integral_exp_residueAffinePhase_le
    (q : Nat) (z : Real) (r : Nat) (a b : Real) :
    ‖∫ s in a..b,
        Complex.exp
          (Complex.I * (residueAffinePhase q z r s : Complex))‖ ≤
      |b - a| := by
  calc
    ‖∫ s in a..b,
        Complex.exp
          (Complex.I * (residueAffinePhase q z r s : Complex))‖ ≤
        1 * |b - a| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro s _
      rw [Complex.norm_exp_I_mul_ofReal]
    _ = |b - a| := one_mul _

/-- The first positive residue sample and the fractional integral immediately
to its left differ by at most one.  This is the sharpened endpoint estimate
needed to retain Chen's total error `6`. -/
theorem norm_exp_residueAffinePhase_zero_sub_initialIntegral_le_one
    (q : Nat) [NeZero q] (z : Real) (P r : Nat)
    (hz0 : 0 ≤ z) (hP : 0 < P) (hrq : r ≤ q) (hrP : r ≤ P)
    (hz : z ≤ 1 / (10 * (q : Real) * (P : Real) ^ 4)) :
    ‖Complex.exp
          (Complex.I * (residueAffinePhase q z r 0 : Complex)) -
        ∫ s in -((r : Real) / q)..0,
          Complex.exp
            (Complex.I * (residueAffinePhase q z r s : Complex))‖ ≤ 1 := by
  let A : Real := -((r : Real) / q)
  let L : Real := (r : Real) / q
  let theta : Real → Real := residueAffinePhase q z r
  let u : Complex := Complex.exp (Complex.I * (theta 0 : Complex))
  let f : Real → Complex := fun s =>
    Complex.exp (Complex.I * (theta s : Complex))
  have hqNat : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq : (0 : Real) < q := by exact_mod_cast hqNat
  have hPReal : (0 : Real) < P := by exact_mod_cast hP
  have hrqReal : (r : Real) ≤ q := by exact_mod_cast hrq
  have hrPReal : (r : Real) ≤ P := by exact_mod_cast hrP
  have hL0 : 0 ≤ L := by simp [L]; positivity
  have hL1 : L ≤ 1 := by
    dsimp [L]
    exact (div_le_one hq).2 hrqReal
  have hrpow :
      (r : Real) ^ 5 ≤ (q : Real) * (P : Real) ^ 4 := by
    calc
      (r : Real) ^ 5 = (r : Real) * (r : Real) ^ 4 := by ring
      _ ≤ (q : Real) * (P : Real) ^ 4 := by
        exact mul_le_mul hrqReal
          (pow_le_pow_left₀ (by positivity) hrPReal 4)
          (by positivity) (by positivity)
  have hden : 0 < 10 * (q : Real) * (P : Real) ^ 4 := by positivity
  have hzden : z * (10 * (q : Real) * (P : Real) ^ 4) ≤ 1 := by
    exact (le_div_iff₀ hden).mp (by simpa only [one_div] using hz)
  have hzpow : 10 * z * (r : Real) ^ 5 ≤ 1 := by
    calc
      10 * z * (r : Real) ^ 5 ≤
          10 * z * ((q : Real) * (P : Real) ^ 4) := by
        gcongr
      _ = z * (10 * (q : Real) * (P : Real) ^ 4) := by ring
      _ ≤ 1 := hzden
  have htheta0 : theta 0 ≤ 1 := by
    have hpi : Real.pi / 5 < 1 := by nlinarith [Real.pi_lt_four]
    calc
      theta 0 = (Real.pi / 5) * (10 * z * (r : Real) ^ 5) := by
        simp [theta, residueAffinePhase]
        ring
      _ ≤ (Real.pi / 5) * 1 := by gcongr
      _ ≤ 1 := by simpa using hpi.le
  have hpoint : ∀ s ∈ Set.uIcc A 0, ‖u - f s‖ ≤ 1 := by
    intro s hs
    have hA0 : A ≤ 0 := by simp [A]; positivity
    rw [Set.uIcc_of_le hA0] at hs
    have hx0 : 0 ≤ (q : Real) * s + r := by
      have hsA := hs.1
      dsimp [A] at hsA
      have hmul := mul_le_mul_of_nonneg_left hsA hq.le
      field_simp [hq.ne'] at hmul
      linarith
    have hxr : (q : Real) * s + r ≤ r := by
      have hmul := mul_nonpos_of_nonneg_of_nonpos hq.le hs.2
      linarith
    have hpowr :
        ((q : Real) * s + r) ^ 5 ≤ (r : Real) ^ 5 :=
      pow_le_pow_left₀ hx0 hxr 5
    have htheta0s : 0 ≤ theta 0 - theta s := by
      rw [show theta 0 - theta s =
          2 * Real.pi * z *
            ((r : Real) ^ 5 - ((q : Real) * s + r) ^ 5) by
        simp [theta, residueAffinePhase]
        ring]
      exact mul_nonneg (mul_nonneg (by positivity) hz0)
        (sub_nonneg.mpr hpowr)
    have hthetaLe : theta 0 - theta s ≤ theta 0 := by
      have hthetas0 : 0 ≤ theta s := by
        dsimp [theta, residueAffinePhase]
        positivity
      linarith
    calc
      ‖u - f s‖ ≤ |theta 0 - theta s| :=
        norm_exp_I_mul_sub_exp_I_mul_le _ _
      _ = theta 0 - theta s := abs_of_nonneg htheta0s
      _ ≤ theta 0 := hthetaLe
      _ ≤ 1 := htheta0
  have hu : ‖u‖ = 1 := by
    simp [u, Complex.norm_exp_I_mul_ofReal]
  have hfirst : ‖u - (L : Complex) * u‖ = 1 - L := by
    rw [show u - (L : Complex) * u =
        ((1 - L : Real) : Complex) * u by
      push_cast
      ring]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hu, mul_one,
      abs_of_nonneg (sub_nonneg.mpr hL1)]
  have hfcont : Continuous f := by
    dsimp [f, theta, residueAffinePhase]
    fun_prop
  have hintegralDiff :
      ‖(L : Complex) * u - ∫ s in A..0, f s‖ ≤ L := by
    have hconst : (L : Complex) * u = ∫ _s in A..0, u := by
      simp [A, L]
    have huInt :
        IntervalIntegrable (fun _s : Real => u) MeasureTheory.volume A 0 :=
      continuous_const.intervalIntegrable A 0
    have hfInt : IntervalIntegrable f MeasureTheory.volume A 0 :=
      hfcont.intervalIntegrable A 0
    rw [hconst, ← intervalIntegral.integral_sub huInt hfInt]
    calc
      ‖∫ s in A..0, u - f s‖ ≤ 1 * |0 - A| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro s hs
        exact hpoint s (Set.uIoc_subset_uIcc hs)
      _ = L := by simp [A, L, abs_of_nonneg hL0]
  change ‖u - ∫ s in A..0, f s‖ ≤ 1
  calc
    ‖u - ∫ s in A..0, f s‖ ≤
        ‖u - (L : Complex) * u‖ +
          ‖(L : Complex) * u - ∫ s in A..0, f s‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (1 - L) + L := add_le_add hfirst.le hintegralDiff
    _ = 1 := by ring

/-- The factor `1 / q` in Chen's residue-class main term is the Jacobian of
the affine parametrization `t = q * s + r`. -/
theorem inv_mul_fifthPerturbationIntegral_eq_residueAffineIntegral
    (q : Nat) [NeZero q] (z : Real) (P r : Nat) :
    (q : Complex)⁻¹ * fifthPerturbationIntegral z P =
      ∫ s in -((r : Real) / q)..(((P : Real) - r) / q),
        Complex.exp
          (Complex.I * (residueAffinePhase q z r s : Complex)) := by
  let f : Real → Complex := fun t =>
    Complex.exp
      (Complex.I * ((2 * Real.pi * z * t ^ 5 : Real) : Complex))
  have hqNat : q ≠ 0 := NeZero.ne q
  have hqReal : (q : Real) ≠ 0 := by exact_mod_cast hqNat
  have hchange := intervalIntegral.integral_comp_mul_add
    (a := -((r : Real) / q)) (b := ((P : Real) - r) / q)
    (c := (q : Real)) f hqReal (r : Real)
  have hleft : (q : Real) * (-((r : Real) / q)) + r = 0 := by
    field_simp
    ring
  have hright :
      (q : Real) * (((P : Real) - r) / q) + r = P := by
    field_simp
    ring
  rw [hleft, hright] at hchange
  calc
    (q : Complex)⁻¹ * fifthPerturbationIntegral z P =
        (q : Real)⁻¹ • (∫ t in (0 : Real)..P, f t) := by
      unfold fifthPerturbationIntegral
      dsimp [f]
      simp
    _ = ∫ s in -((r : Real) / q)..(((P : Real) - r) / q),
        f ((q : Real) * s + r) := hchange.symm
    _ = ∫ s in -((r : Real) / q)..(((P : Real) - r) / q),
        Complex.exp
          (Complex.I * (residueAffinePhase q z r s : Complex)) := by
      rfl

end Waring.Analytic
