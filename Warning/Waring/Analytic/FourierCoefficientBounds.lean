import Waring.Analytic.IncompletePowerSums
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Bounds for interval Fourier coefficients

This file develops the finite harmonic estimates used after pairing the
frequencies in Chen's Lemma 6 [CHEN1964-EN, p. 1551, equation (8)].
-/

namespace Waring.Analytic

/-- The harmonic sum from a paired odd residue interval fits inside the
logarithm of the full interval length. -/
theorem harmonic_le_log_two_mul_add_one (n : Nat) :
    (harmonic n : Real) ≤ Real.log (2 * n + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hDen : (0 : Real) < 2 * n + 1 := by positivity
      have hx : (0 : Real) ≤ 2 / (2 * n + 1) := by positivity
      have hstep : ((n + 1 : Nat) : Real)⁻¹ ≤
          Real.log (1 + 2 / (2 * n + 1)) := by
        calc
          ((n + 1 : Nat) : Real)⁻¹ =
              2 * (2 / (2 * n + 1)) / (2 / (2 * n + 1) + 2) := by
                field_simp
                push_cast
                ring
          _ ≤ Real.log (1 + 2 / (2 * n + 1)) :=
            Real.le_log_one_add_of_nonneg hx
      simp only [harmonic_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast]
      calc
        (harmonic n : Real) + ((n + 1 : Nat) : Real)⁻¹ ≤
            Real.log (2 * n + 1) +
              Real.log (1 + 2 / (2 * n + 1)) := add_le_add ih hstep
        _ = Real.log ((2 * n + 1) * (1 + 2 / (2 * n + 1))) := by
          rw [Real.log_mul (ne_of_gt hDen) (by positivity)]
        _ = Real.log (2 * (((n + 1 : Nat) : Real)) + 1) := by
          congr 1
          field_simp
          push_cast
          ring

/-- For an even residue interval, the harmonic pairs plus the self-paired
midpoint fit inside the logarithm of the full interval length. -/
theorem harmonic_add_even_midpoint_le_log (n : Nat) :
    (harmonic n : Real) + ((2 * (n + 1) : Nat) : Real)⁻¹ ≤
      Real.log ((2 * (n + 1) : Nat) : Real) := by
  have hOdd : (harmonic n : Real) ≤ Real.log (2 * n + 1) :=
    harmonic_le_log_two_mul_add_one n
  have hDen : (0 : Real) < 2 * n + 1 := by positivity
  have hTop : (0 : Real) < 2 * (n + 1) := by positivity
  have hRatio : (0 : Real) < (2 * (n + 1)) / (2 * n + 1) := by positivity
  have hstep : ((2 * (n + 1) : Nat) : Real)⁻¹ ≤
      Real.log ((2 * (n + 1)) / (2 * n + 1)) := by
    calc
      ((2 * (n + 1) : Nat) : Real)⁻¹ =
          1 - ((2 * (n + 1) : Real) / (2 * n + 1))⁻¹ := by
            field_simp
            push_cast
            ring
      _ ≤ Real.log ((2 * (n + 1)) / (2 * n + 1)) :=
        Real.one_sub_inv_le_log_of_pos hRatio
  calc
    (harmonic n : Real) + ((2 * (n + 1) : Nat) : Real)⁻¹ ≤
        Real.log (2 * n + 1) +
          Real.log ((2 * (n + 1)) / (2 * n + 1)) := add_le_add hOdd hstep
    _ = Real.log ((2 * n + 1) *
        ((2 * (n + 1)) / (2 * n + 1))) := by
      rw [Real.log_mul (ne_of_gt hDen) (ne_of_gt hRatio)]
    _ = Real.log ((2 * (n + 1) : Nat) : Real) := by
      congr 1
      field_simp
      push_cast
      ring

/-- Extending the interval by one integer appends its final Fourier term. -/
theorem intervalFourierCoefficient_succ {q : Nat} [NeZero q]
    (M : Int) (m : Nat) (h : ZMod q) :
    intervalFourierCoefficient M (m + 1) h =
      intervalFourierCoefficient M m h +
        ZMod.stdAddChar (-(h * ((M + (m + 1 : Nat) : Int) : ZMod q))) := by
  have hM : M ≤ M + (m : Int) := by omega
  have hEnd : M + ((m + 1 : Nat) : Int) = (M + (m : Int)) + 1 := by
    push_cast
    ring
  unfold intervalFourierCoefficient
  rw [hEnd, ← Finset.insert_Ioc_right_eq_Ioc_add_one hM]
  rw [Finset.sum_insert]
  · ac_rfl
  · simp

/-- Exact finite geometric telescoping identity for an interval Fourier
coefficient. -/
theorem intervalFourierCoefficient_mul_sub_one {q : Nat} [NeZero q]
    (M : Int) (m : Nat) (h : ZMod q) :
    intervalFourierCoefficient M m h * (ZMod.stdAddChar (-h) - 1) =
      ZMod.stdAddChar
          (-(h * ((M + (m : Int) + 1 : Int) : ZMod q))) -
        ZMod.stdAddChar (-(h * ((M + 1 : Int) : ZMod q))) := by
  induction m with
  | zero => simp [intervalFourierCoefficient]
  | succ m ih =>
      rw [intervalFourierCoefficient_succ]
      have hshift :
          ZMod.stdAddChar
                (-(h * ((M + ((m + 1 : Nat) : Int) : Int) : ZMod q))) *
              ZMod.stdAddChar (-h) =
            ZMod.stdAddChar
              (-(h * ((M + ((m + 1 : Nat) : Int) + 1 : Int) : ZMod q))) := by
        rw [← ZMod.stdAddChar.map_add_eq_mul]
        congr 1
        push_cast
        ring
      calc
        (intervalFourierCoefficient M m h +
              ZMod.stdAddChar
                (-(h * ((M + ((m + 1 : Nat) : Int) : Int) : ZMod q)))) *
            (ZMod.stdAddChar (-h) - 1) =
            intervalFourierCoefficient M m h * (ZMod.stdAddChar (-h) - 1) +
              ZMod.stdAddChar
                  (-(h * ((M + ((m + 1 : Nat) : Int) : Int) : ZMod q))) *
                (ZMod.stdAddChar (-h) - 1) := by ring
        _ = (ZMod.stdAddChar
                (-(h * ((M + (m : Int) + 1 : Int) : ZMod q))) -
              ZMod.stdAddChar (-(h * ((M + 1 : Int) : ZMod q)))) +
            ZMod.stdAddChar
                (-(h * ((M + ((m + 1 : Nat) : Int) : Int) : ZMod q))) *
              (ZMod.stdAddChar (-h) - 1) := by rw [ih]
        _ = ZMod.stdAddChar
                (-(h * ((M + ((m + 1 : Nat) : Int) + 1 : Int) : ZMod q))) -
              ZMod.stdAddChar (-(h * ((M + 1 : Int) : ZMod q))) := by
          rw [mul_sub, mul_one, hshift]
          push_cast
          ring_nf

/-- Taking norms in the telescoping identity bounds its two endpoint terms. -/
theorem norm_intervalFourierCoefficient_mul_norm_sub_one_le_two
    {q : Nat} [NeZero q] (M : Int) (m : Nat) (h : ZMod q) :
    ‖intervalFourierCoefficient M m h‖ * ‖ZMod.stdAddChar (-h) - 1‖ ≤ 2 := by
  have htelescope := congrArg norm
    (intervalFourierCoefficient_mul_sub_one M m h)
  rw [norm_mul] at htelescope
  rw [htelescope]
  calc
    ‖ZMod.stdAddChar
          (-(h * ((M + (m : Int) + 1 : Int) : ZMod q))) -
        ZMod.stdAddChar (-(h * ((M + 1 : Int) : ZMod q)))‖ ≤
        ‖ZMod.stdAddChar
          (-(h * ((M + (m : Int) + 1 : Int) : ZMod q)))‖ +
          ‖ZMod.stdAddChar (-(h * ((M + 1 : Int) : ZMod q)))‖ := norm_sub_le _ _
    _ = 2 := by norm_num

/-- Away from the zero frequency, division by the nontrivial character
increment gives the usual geometric-series bound. -/
theorem norm_intervalFourierCoefficient_le_two_div {q : Nat} [NeZero q]
    (M : Int) (m : Nat) {h : ZMod q} (hh : h ≠ 0) :
    ‖intervalFourierCoefficient M m h‖ ≤
      2 / ‖ZMod.stdAddChar (-h) - 1‖ := by
  have hchar : ZMod.stdAddChar (-h) ≠ 1 := by
    intro heq
    have heqZero : ZMod.stdAddChar (-h) =
        ZMod.stdAddChar (0 : ZMod q) := by simpa using heq
    have hneg : -h = 0 := ZMod.injective_stdAddChar heqZero
    exact hh (neg_eq_zero.mp hneg)
  have hnorm : 0 < ‖ZMod.stdAddChar (-h) - 1‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hchar)
  apply (le_div_iff₀ hnorm).2
  exact norm_intervalFourierCoefficient_mul_norm_sub_one_le_two M m h

/-- The trivial interval-length bound for a Fourier coefficient. -/
theorem norm_intervalFourierCoefficient_le_length {q : Nat} [NeZero q]
    (M : Int) (m : Nat) (h : ZMod q) :
    ‖intervalFourierCoefficient M m h‖ ≤ m := by
  unfold intervalFourierCoefficient
  calc
    ‖∑ x ∈ Finset.Ioc M (M + m), ZMod.stdAddChar (-(h * (x : ZMod q)))‖ ≤
        ∑ x ∈ Finset.Ioc M (M + m),
          ‖ZMod.stdAddChar (-(h * (x : ZMod q)))‖ := norm_sum_le _ _
    _ = m := by simp

/-- The denominator in the geometric bound is the corresponding sine chord. -/
theorem norm_stdAddChar_neg_sub_one {q : Nat} [NeZero q] (h : ZMod q) :
    ‖ZMod.stdAddChar (-h) - 1‖ =
      ‖(2 : Real) * Real.sin (Real.pi * h.val / q)‖ := by
  have hchar : ZMod.stdAddChar (-h) =
      Complex.exp (2 * Real.pi * Complex.I * (-(h.val : Int)) / q) := by
    calc
      ZMod.stdAddChar (-h) =
          ZMod.stdAddChar (-(h.val : Int) : ZMod q) := by congr 1; simp
      _ = Complex.exp (2 * Real.pi * Complex.I * (-(h.val : Int)) / q) := by
        simpa only [Int.cast_neg, Int.cast_natCast] using
          ZMod.stdAddChar_coe (N := q) (-(h.val : Int))
  rw [hchar]
  rw [show (2 * (Real.pi : Complex) * Complex.I * (-(h.val : Int)) / q) =
      Complex.I * (-(2 * Real.pi * h.val / q) : Real) by push_cast; ring]
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show (-(2 * Real.pi * h.val / q) : Real) / 2 =
      -(Real.pi * h.val / q) by ring]
  rw [Real.sin_neg]
  rw [show (2 : Real) * -Real.sin (Real.pi * h.val / q) =
      -(2 * Real.sin (Real.pi * h.val / q)) by ring, norm_neg]

/-- Sine-chord denominator expressed through the least absolute residue. -/
theorem norm_stdAddChar_neg_sub_one_valMinAbs {q : Nat} [NeZero q]
    (h : ZMod q) :
    ‖ZMod.stdAddChar (-h) - 1‖ =
      2 * |Real.sin (Real.pi * (h.valMinAbs : Real) / q)| := by
  have hchar : ZMod.stdAddChar (-h) =
      Complex.exp (2 * Real.pi * Complex.I * (-h.valMinAbs) / q) := by
    calc
      ZMod.stdAddChar (-h) =
          ZMod.stdAddChar ((-h.valMinAbs : Int) : ZMod q) := by
            congr 1
            rw [Int.cast_neg, ZMod.coe_valMinAbs]
      _ = Complex.exp (2 * Real.pi * Complex.I * (-h.valMinAbs) / q) :=
        by
          simpa only [Int.cast_neg] using
            ZMod.stdAddChar_coe (N := q) (-h.valMinAbs)
  rw [hchar]
  rw [show (2 * (Real.pi : Complex) * Complex.I * (-h.valMinAbs) / q) =
      Complex.I * (-(2 * Real.pi * (h.valMinAbs : Real) / q) : Real) by
        push_cast
        ring]
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show (-(2 * Real.pi * (h.valMinAbs : Real) / q) : Real) / 2 =
      -(Real.pi * (h.valMinAbs : Real) / q) by ring]
  rw [Real.sin_neg, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num :
    (0 : Real) ≤ 2), abs_neg]

/-- A nonzero frequency in the lower half of the residue interval has the
standard reciprocal-distance bound. -/
theorem norm_intervalFourierCoefficient_le_of_two_val_le {q : Nat} [NeZero q]
    (M : Int) (m : Nat) {h : ZMod q} (hh : h ≠ 0)
    (hhalf : 2 * h.val ≤ q) :
    ‖intervalFourierCoefficient M m h‖ ≤
      (q : Real) / (2 * h.val) := by
  have hqNat : 0 < q := NeZero.pos q
  have hvalNat : 0 < h.val := ZMod.val_pos.mpr hh
  have hq : (0 : Real) < q := by exact_mod_cast hqNat
  have hval : (0 : Real) < h.val := by exact_mod_cast hvalNat
  let x : Real := Real.pi * h.val / q
  have hxNonneg : 0 ≤ x := by dsimp [x]; positivity
  have hxHalf : x ≤ Real.pi / 2 := by
    dsimp [x]
    apply (div_le_iff₀ hq).2
    have hhalfReal : (2 : Real) * h.val ≤ q := by exact_mod_cast hhalf
    nlinarith [Real.pi_pos]
  have hsin := Real.mul_abs_le_abs_sin (show |x| ≤ Real.pi / 2 by
    rw [abs_of_nonneg hxNonneg]
    exact hxHalf)
  have hdenom : (4 : Real) * h.val / q ≤
      ‖ZMod.stdAddChar (-h) - 1‖ := by
    rw [norm_stdAddChar_neg_sub_one h, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by norm_num : (0 : Real) ≤ 2)]
    calc
      (4 : Real) * h.val / q = 2 * ((2 / Real.pi) * |x|) := by
        rw [abs_of_nonneg hxNonneg]
        dsimp [x]
        field_simp [Real.pi_ne_zero, ne_of_gt hq]
        ring
      _ ≤ 2 * |Real.sin x| := by gcongr
  have hsmallDenom : 0 < (4 : Real) * h.val / q := by positivity
  calc
    ‖intervalFourierCoefficient M m h‖ ≤
        2 / ‖ZMod.stdAddChar (-h) - 1‖ :=
      norm_intervalFourierCoefficient_le_two_div M m hh
    _ ≤ 2 / ((4 : Real) * h.val / q) :=
      div_le_div_of_nonneg_left (by norm_num) hsmallDenom hdenom
    _ = (q : Real) / (2 * h.val) := by field_simp; ring

/-- The sharp geometric bound in terms of the least absolute residue. -/
theorem norm_intervalFourierCoefficient_le_leastResidue {q : Nat} [NeZero q]
    (M : Int) (m : Nat) {h : ZMod q} (hh : h ≠ 0) :
    ‖intervalFourierCoefficient M m h‖ ≤
      (q : Real) / (2 * (h.valMinAbs.natAbs : Real)) := by
  have hqNat : 0 < q := NeZero.pos q
  have hq : (0 : Real) < q := by exact_mod_cast hqNat
  have hj : h.valMinAbs ≠ 0 := by
    intro hjZero
    exact hh ((ZMod.valMinAbs_eq_zero h).mp hjZero)
  have hdNat : 0 < h.valMinAbs.natAbs := Int.natAbs_pos.mpr hj
  have hd : (0 : Real) < h.valMinAbs.natAbs := by exact_mod_cast hdNat
  have hdHalfNat : 2 * h.valMinAbs.natAbs ≤ q := by
    have := ZMod.natAbs_valMinAbs_le h
    omega
  have hdHalf : (2 : Real) * h.valMinAbs.natAbs ≤ q := by
    exact_mod_cast hdHalfNat
  let x : Real := Real.pi * (h.valMinAbs : Real) / q
  have hxAbs : |x| = Real.pi * h.valMinAbs.natAbs / q := by
    dsimp [x]
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hq,
      ← Int.cast_abs, Int.abs_eq_natAbs]
    norm_num
  have hxHalf : |x| ≤ Real.pi / 2 := by
    rw [hxAbs]
    apply (div_le_iff₀ hq).2
    nlinarith [Real.pi_pos]
  have hsin := Real.mul_abs_le_abs_sin hxHalf
  have hdenom : (4 : Real) * h.valMinAbs.natAbs / q ≤
      ‖ZMod.stdAddChar (-h) - 1‖ := by
    rw [norm_stdAddChar_neg_sub_one_valMinAbs h]
    calc
      (4 : Real) * h.valMinAbs.natAbs / q =
          2 * ((2 / Real.pi) * |x|) := by
        rw [hxAbs]
        field_simp [Real.pi_ne_zero, ne_of_gt hq]
        ring
      _ ≤ 2 * |Real.sin x| := by gcongr
  have hsmallDenom : 0 < (4 : Real) * h.valMinAbs.natAbs / q := by
    positivity
  calc
    ‖intervalFourierCoefficient M m h‖ ≤
        2 / ‖ZMod.stdAddChar (-h) - 1‖ :=
      norm_intervalFourierCoefficient_le_two_div M m hh
    _ ≤ 2 / ((4 : Real) * h.valMinAbs.natAbs / q) :=
      div_le_div_of_nonneg_left (by norm_num) hsmallDenom hdenom
    _ = (q : Real) / (2 * (h.valMinAbs.natAbs : Real)) := by
      field_simp
      ring

/-- Combining the trivial and geometric estimates gives the standard minimum
bound for an interval coefficient. -/
theorem norm_intervalFourierCoefficient_le_min_length_leastResidue
    {q : Nat} [NeZero q] (M : Int) (m : Nat) {h : ZMod q} (hh : h ≠ 0) :
    ‖intervalFourierCoefficient M m h‖ ≤
      min (m : Real) ((q : Real) / (2 * (h.valMinAbs.natAbs : Real))) := by
  exact le_min (norm_intervalFourierCoefficient_le_length M m h)
    (norm_intervalFourierCoefficient_le_leastResidue M m hh)

end Waring.Analytic
