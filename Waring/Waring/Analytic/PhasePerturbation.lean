import Mathlib.Analysis.Real.Pi.Bounds
import Waring.Analytic.AbelVariation
import Waring.Analytic.WeylFifthPhaseCorrelation

/-!
# Phase perturbation in Chen's Lemma 9

This file compares the real fifth-power exponential on `1, ..., P` with the
rational additive-character phase used by the three-step Weyl estimate
[CHEN1964-EN, pp. 1555-1560; CHEN1964-ZH, pp. 720-725].
-/

namespace Waring.Analytic

open scoped BigOperators

/-- The real angle of the fifth-power exponential on the positive interval;
the zero-based index `x` represents the integer `x + 1`. -/
noncomputable def realFifthPowerPhase (alpha : Real) (x : Nat) : Real :=
  2 * Real.pi * alpha * (((x + 1 : Nat) : Real) ^ 5)

/-- The unit-circle exponential with real frequency `alpha`, sampled on the
positive integers. -/
noncomputable def realFifthPowerExponential
    (alpha : Real) (x : Nat) : Complex :=
  Complex.exp (Complex.I * (realFifthPowerPhase alpha x : Complex))

/-- At the rational frequency `a / q`, the real exponential is exactly the
standard additive character used by `fifthPowerChar`. -/
theorem realFifthPowerExponential_rational_eq_fifthPowerChar
    (q : Nat) [NeZero q] (a x : Nat) :
    realFifthPowerExponential ((a : Real) / q) x =
      fifthPowerChar ((a : Nat) : ZMod q) x := by
  unfold realFifthPowerExponential realFifthPowerPhase fifthPowerChar
    shiftedStdAddCharPhase
  symm
  convert ZMod.stdAddChar_coe
    (N := q) (((a * (x + 1) ^ 5 : Nat) : Int)) using 1 <;>
    push_cast <;> ring_nf

/-- Changing a real frequency by `epsilon` changes one sampled exponential by
at most `2*pi*|epsilon|*(x+1)^5`. -/
theorem norm_realFifthPowerExponential_sub_le
    (alpha epsilon : Real) (x : Nat) :
    ‖realFifthPowerExponential (alpha + epsilon) x -
        realFifthPowerExponential alpha x‖ ≤
      2 * Real.pi * |epsilon| * (((x + 1 : Nat) : Real) ^ 5) := by
  unfold realFifthPowerExponential
  calc
    ‖Complex.exp
          (Complex.I * (realFifthPowerPhase (alpha + epsilon) x : Complex)) -
        Complex.exp
          (Complex.I * (realFifthPowerPhase alpha x : Complex))‖ ≤
        |realFifthPowerPhase (alpha + epsilon) x -
          realFifthPowerPhase alpha x| :=
      norm_exp_I_mul_sub_exp_I_mul_le _ _
    _ = 2 * Real.pi * |epsilon| *
        (((x + 1 : Nat) : Real) ^ 5) := by
      unfold realFifthPowerPhase
      rw [show
        2 * Real.pi * (alpha + epsilon) * (((x + 1 : Nat) : Real) ^ 5) -
            2 * Real.pi * alpha * (((x + 1 : Nat) : Real) ^ 5) =
          (2 * Real.pi) * epsilon * (((x + 1 : Nat) : Real) ^ 5) by ring]
      have hpowAbs :
          |(((x + 1 : Nat) : Real) ^ 5)| =
            (((x + 1 : Nat) : Real) ^ 5) := abs_of_nonneg (by positivity)
      rw [abs_mul, abs_mul,
        abs_of_pos (mul_pos (by norm_num) Real.pi_pos), hpowAbs]

/-- General finite perturbation estimate on the positive interval
`1, ..., P`. -/
theorem norm_sum_realFifthPowerExponential_sub_le
    (alpha epsilon : Real) (P : Nat) :
    ‖(∑ x ∈ Finset.range P,
          realFifthPowerExponential (alpha + epsilon) x) -
        ∑ x ∈ Finset.range P, realFifthPowerExponential alpha x‖ ≤
      2 * Real.pi * |epsilon| * (P : Real) ^ 6 := by
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ x ∈ Finset.range P,
        (realFifthPowerExponential (alpha + epsilon) x -
          realFifthPowerExponential alpha x)‖ ≤
        ∑ x ∈ Finset.range P,
          ‖realFifthPowerExponential (alpha + epsilon) x -
            realFifthPowerExponential alpha x‖ := norm_sum_le _ _
    _ ≤ ∑ _x ∈ Finset.range P,
        2 * Real.pi * |epsilon| * (P : Real) ^ 5 := by
      apply Finset.sum_le_sum
      intro x hx
      have hxP : x + 1 ≤ P := by
        have hxlt : x < P := Finset.mem_range.mp hx
        omega
      calc
        ‖realFifthPowerExponential (alpha + epsilon) x -
            realFifthPowerExponential alpha x‖ ≤
            2 * Real.pi * |epsilon| *
              (((x + 1 : Nat) : Real) ^ 5) :=
          norm_realFifthPowerExponential_sub_le alpha epsilon x
        _ ≤ 2 * Real.pi * |epsilon| * (P : Real) ^ 5 := by
          apply mul_le_mul_of_nonneg_left
          · exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hxP) 5
          · positivity
    _ = 2 * Real.pi * |epsilon| * (P : Real) ^ 6 := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

/-- The perturbation estimate with its rational center written as the
existing fifth-power additive character. -/
theorem norm_sum_realFifthPowerExponential_sub_fifthPowerChar_le
    (q : Nat) [NeZero q] (a P : Nat) (epsilon : Real) :
    ‖(∑ x ∈ Finset.range P,
          realFifthPowerExponential ((a : Real) / q + epsilon) x) -
        ∑ x ∈ Finset.range P,
          fifthPowerChar ((a : Nat) : ZMod q) x‖ ≤
      2 * Real.pi * |epsilon| * (P : Real) ^ 6 := by
  have hcenter :
      (∑ x ∈ Finset.range P,
          realFifthPowerExponential ((a : Real) / q) x) =
        ∑ x ∈ Finset.range P,
          fifthPowerChar ((a : Nat) : ZMod q) x := by
    apply Finset.sum_congr rfl
    intro x _
    exact realFifthPowerExponential_rational_eq_fifthPowerChar q a x
  simpa only [hcenter] using
    norm_sum_realFifthPowerExponential_sub_le
      ((a : Real) / q) epsilon P

/-- In Chen's large-denominator range, replacing the real phase by its
rational character costs at most `P^(24/25)`. -/
theorem norm_sum_realFifthPowerExponential_le_rational_add_error
    (q : Nat) [NeZero q] (a P : Nat) (epsilon : Real)
    (hPThreshold : (10 : Real) ^ 150 ≤ P)
    (hqLower : (P : Real) ^ (26 / 25 : Real) ≤ q)
    (hepsilon : |epsilon| ≤
      1 / (10 * (q : Real) * (P : Real) ^ 4)) :
    ‖∑ x ∈ Finset.range P,
        realFifthPowerExponential ((a : Real) / q + epsilon) x‖ ≤
      ‖∑ x ∈ Finset.range P,
        fifthPowerChar ((a : Nat) : ZMod q) x‖ +
          (P : Real) ^ (24 / 25 : Real) := by
  have hPPos : (0 : Real) < P :=
    (by positivity : (0 : Real) < 10 ^ 150).trans_le hPThreshold
  have hqPos : (0 : Real) < q := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have herror :=
    norm_sum_realFifthPowerExponential_sub_fifthPowerChar_le
      q a P epsilon
  have hperturbation :
      2 * Real.pi * |epsilon| * (P : Real) ^ 6 ≤
        (P : Real) ^ (24 / 25 : Real) := by
    calc
      2 * Real.pi * |epsilon| * (P : Real) ^ 6 ≤
          2 * Real.pi *
              (1 / (10 * (q : Real) * (P : Real) ^ 4)) *
                (P : Real) ^ 6 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hepsilon (by positivity)) (by positivity)
      _ = (Real.pi / 5) * ((P : Real) ^ 2 / q) := by
        field_simp
        ring
      _ ≤ (Real.pi / 5) * (P : Real) ^ (24 / 25 : Real) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply (div_le_iff₀ hqPos).2
        calc
          (P : Real) ^ 2 ≤
              (P : Real) ^ (24 / 25 : Real) *
                (P : Real) ^ (26 / 25 : Real) := by
            rw [← Real.rpow_natCast (P : Real) 2,
              ← Real.rpow_add hPPos]
            norm_num
          _ ≤ (P : Real) ^ (24 / 25 : Real) * q :=
            mul_le_mul_of_nonneg_left hqLower (by positivity)
      _ ≤ (P : Real) ^ (24 / 25 : Real) := by
        have hpi : Real.pi / 5 ≤ 1 := by
          linarith [Real.pi_lt_four]
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hpi (Real.rpow_nonneg hPPos.le _)
  exact (norm_le_norm_add_norm_sub'
    (∑ x ∈ Finset.range P,
      realFifthPowerExponential ((a : Real) / q + epsilon) x)
    (∑ x ∈ Finset.range P,
      fifthPowerChar ((a : Nat) : ZMod q) x)).trans
        (add_le_add (le_refl _) (herror.trans hperturbation))

/-- Source-facing form of the perturbation estimate when the real frequency
is supplied separately with its rational-approximation identity. -/
theorem norm_sum_realFifthPowerExponential_le_rational_add_error_of_eq
    (q : Nat) [NeZero q] (a P : Nat) (alpha epsilon : Real)
    (halpha : alpha = (a : Real) / q + epsilon)
    (hPThreshold : (10 : Real) ^ 150 ≤ P)
    (hqLower : (P : Real) ^ (26 / 25 : Real) ≤ q)
    (hepsilon : |epsilon| ≤
      1 / (10 * (q : Real) * (P : Real) ^ 4)) :
    ‖∑ x ∈ Finset.range P, realFifthPowerExponential alpha x‖ ≤
      ‖∑ x ∈ Finset.range P,
        fifthPowerChar ((a : Nat) : ZMod q) x‖ +
          (P : Real) ^ (24 / 25 : Real) := by
  rw [halpha]
  exact norm_sum_realFifthPowerExponential_le_rational_add_error
    q a P epsilon hPThreshold hqLower hepsilon

end Waring.Analytic
