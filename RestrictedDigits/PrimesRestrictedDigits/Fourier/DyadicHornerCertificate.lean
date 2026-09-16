import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Dyadic Horner ceilings

This module gives an exact, root-free bridge from a squared rational upper
bound to a rational upper value for a real power.  A most-significant-bit-first
Boolean list is evaluated by nested square roots; natural square-root ceilings
make every step kernel-checkable.  The construction is numerical
infrastructure only and does not assert any endpoint or matrix certificate.
-/

namespace PrimesRestrictedDigits

def boolReal : Bool → ℝ
  | false => 0
  | true => 1

def boolBase (c : ℝ) : Bool → ℝ
  | false => 1
  | true => c

noncomputable def dyadicExponent : List Bool → ℝ
  | [] => 0
  | bit :: bits => (boolReal bit + dyadicExponent bits) / 2

noncomputable def dyadicRootValue (c : ℝ) : List Bool → ℝ
  | [] => 1
  | bit :: bits => Real.sqrt (boolBase c bit * dyadicRootValue c bits)

theorem dyadicRootValue_eq_rpow {c : ℝ} (hc : 0 < c) (bits : List Bool) :
    dyadicRootValue c bits = c ^ dyadicExponent bits := by
  induction bits with
  | nil => simp [dyadicRootValue, dyadicExponent]
  | cons bit bits ih =>
      rw [dyadicRootValue, dyadicExponent, ih, Real.sqrt_eq_rpow]
      cases bit
      · rw [boolBase, boolReal]
        rw [one_mul, ← Real.rpow_mul hc.le]
        congr 1
        ring
      · rw [boolBase, boolReal]
        calc
          (c * c ^ dyadicExponent bits) ^ (1 / 2 : ℝ) =
              (c ^ (1 + dyadicExponent bits)) ^ (1 / 2 : ℝ) := by
                rw [Real.rpow_add hc, Real.rpow_one]
          _ = c ^ ((1 + dyadicExponent bits) / 2) := by
                rw [← Real.rpow_mul hc.le]
                congr 1
                ring

theorem dyadicExponent_nonneg (bits : List Bool) : 0 ≤ dyadicExponent bits := by
  induction bits with
  | nil => simp [dyadicExponent]
  | cons bit bits ih =>
      simp only [dyadicExponent]
      cases bit <;> simp only [boolReal] <;> positivity

def hornerNum (D c : ℕ) : List Bool → ℕ
  | [] => D
  | bit :: bits =>
      let tail := hornerNum D c bits
      Nat.sqrt (if bit then c * tail else D * tail) + 1

noncomputable def hornerValue (D c : ℕ) (bits : List Bool) : ℝ :=
  (hornerNum D c bits : ℝ) / (D : ℝ)

theorem hornerValue_nonneg (D c : ℕ) (hD : 0 < D) (bits : List Bool) :
    0 ≤ hornerValue D c bits := by
  unfold hornerValue
  positivity

theorem hornerValue_step_sq_upper (D c : ℕ) (hD : 0 < D)
    (bit : Bool) (bits : List Bool) :
    boolBase ((c : ℝ) / D) bit * hornerValue D c bits ≤
      hornerValue D c (bit :: bits) ^ 2 := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  cases bit
  · simp only [boolBase, hornerValue, hornerNum, Bool.false_eq_true, if_false,
      one_mul]
    field_simp
    have hs := Nat.lt_succ_sqrt' (D * hornerNum D c bits)
    have hs' : (D * hornerNum D c bits : ℝ) <
        (Nat.sqrt (D * hornerNum D c bits) + 1 : ℕ) ^ 2 := by
      exact_mod_cast hs
    nlinarith
  · simp only [boolBase, hornerValue, hornerNum, if_true]
    field_simp
    have hs := Nat.lt_succ_sqrt' (c * hornerNum D c bits)
    have hs' : (c * hornerNum D c bits : ℝ) <
        (Nat.sqrt (c * hornerNum D c bits) + 1 : ℕ) ^ 2 := by
      exact_mod_cast hs
    nlinarith

theorem dyadicRootValue_le_hornerValue (D c : ℕ) (hD : 0 < D)
    (hc : 0 < c) (bits : List Bool) :
    dyadicRootValue ((c : ℝ) / D) bits ≤ hornerValue D c bits := by
  induction bits with
  | nil =>
      simp only [dyadicRootValue, hornerValue, hornerNum]
      have hDne : (D : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
      rw [div_self hDne]
  | cons bit bits ih =>
      apply Real.sqrt_le_iff.mpr
      constructor
      · exact hornerValue_nonneg D c hD (bit :: bits)
      calc
        boolBase ((c : ℝ) / D) bit *
              dyadicRootValue ((c : ℝ) / D) bits ≤
            boolBase ((c : ℝ) / D) bit * hornerValue D c bits := by
              apply mul_le_mul_of_nonneg_left ih
              cases bit
              · simp [boolBase]
              · simp [boolBase]
                positivity
        _ ≤ hornerValue D c (bit :: bits) ^ 2 :=
          hornerValue_step_sq_upper D c hD bit bits

theorem rpow_le_hornerValue_of_sq_le (D c : ℕ) (hD : 0 < D)
    (hc : 0 < c) (m t : ℝ) (bits : List Bool)
    (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hmsq : m ^ 2 ≤ (c : ℝ) / D)
    (hexp : 2 * dyadicExponent bits ≤ t) :
    m ^ t ≤ hornerValue D c bits := by
  have he : 0 ≤ dyadicExponent bits := dyadicExponent_nonneg bits
  have hmt : m ^ t ≤ m ^ (2 * dyadicExponent bits) := by
    apply Real.rpow_le_rpow_of_exponent_ge' hm0 hm1
      (by positivity)
    exact hexp
  have hbase : (m ^ 2) ^ dyadicExponent bits ≤
      ((c : ℝ) / D) ^ dyadicExponent bits := by
    apply Real.rpow_le_rpow (sq_nonneg m) hmsq he
  have hpowid : m ^ (2 * dyadicExponent bits) =
      (m ^ 2) ^ dyadicExponent bits := by
    rw [show 2 * dyadicExponent bits = dyadicExponent bits * 2 by ring,
      Real.rpow_mul hm0]
    simpa only [Real.rpow_two] using
      (Real.rpow_pow_comm hm0 (dyadicExponent bits) 2)
  calc
    m ^ t ≤ m ^ (2 * dyadicExponent bits) := hmt
    _ = (m ^ 2) ^ dyadicExponent bits := hpowid
    _ ≤ ((c : ℝ) / D) ^ dyadicExponent bits := hbase
    _ = dyadicRootValue ((c : ℝ) / D) bits := by
      rw [dyadicRootValue_eq_rpow (by positivity)]
    _ ≤ hornerValue D c bits := dyadicRootValue_le_hornerValue D c hD hc bits

end PrimesRestrictedDigits
