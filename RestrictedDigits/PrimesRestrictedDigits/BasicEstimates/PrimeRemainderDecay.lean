import PrimesRestrictedDigits.BasicEstimates.LogarithmicIntegral
import Mathlib.Analysis.Complex.Exponential

/-!
# From exponential PNT decay to a log-square remainder

This proves the fixed exponent-two consequence of Montgomery--Vaughan,
Chapter 6, Theorem 6.9, used after Eq. (7.45). It does not assert the
exponential prime number theorem.
-/

namespace PrimesRestrictedDigits

/-- The degree-four exponential scale used to absorb two logarithmic powers.
This generic form is also used by the optimized zeta Perron height. -/
theorem log_sq_le_exp_sqrt_log_scale
    {c x : Real} (hc : 0 < c) (hx : 1 ≤ x) :
    Real.log x ^ 2 ≤
      24 / c ^ 4 * Real.exp (c * Real.sqrt (Real.log x)) := by
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hz : 0 ≤ c * Real.sqrt (Real.log x) :=
    mul_nonneg hc.le (Real.sqrt_nonneg _)
  have hexp := Real.pow_div_factorial_le_exp
    (c * Real.sqrt (Real.log x)) hz 4
  norm_num [Nat.factorial] at hexp
  have hc4 : 0 < c ^ 4 := pow_pos hc 4
  calc
    Real.log x ^ 2 =
        24 / c ^ 4 * ((c * Real.sqrt (Real.log x)) ^ 4 / 24) := by
      field_simp
      nlinarith [Real.sq_sqrt hlog]
    _ ≤ 24 / c ^ 4 * Real.exp (c * Real.sqrt (Real.log x)) := by
      gcongr

private theorem abs_primeRemainder_le_log_sq_of_exp
    {c C : Real} (hc : 0 < c) (hC : 0 ≤ C)
    (hExp : ∀ x : Real, 2 ≤ x →
      |primeRemainder x| ≤
        C * x / Real.exp (c * Real.sqrt (Real.log x))) :
    ∀ x : Real, 2 ≤ x →
      |primeRemainder x| ≤
        (24 * C / c ^ 4) * x / Real.log x ^ 2 := by
  intro x hx
  apply (hExp x hx).trans
  have hxOne : 1 < x := lt_of_lt_of_le one_lt_two hx
  have hlog : 0 < Real.log x := Real.log_pos hxOne
  have hscale := log_sq_le_exp_sqrt_log_scale hc hxOne.le
  have hrecip :
      1 / Real.exp (c * Real.sqrt (Real.log x)) ≤
        (24 / c ^ 4) / Real.log x ^ 2 := by
    rw [div_le_div_iff₀ (Real.exp_pos _) (sq_pos_of_pos hlog)]
    simpa using hscale
  calc
    C * x / Real.exp (c * Real.sqrt (Real.log x)) =
        (C * x) * (1 / Real.exp (c * Real.sqrt (Real.log x))) := by ring
    _ ≤ (C * x) * ((24 / c ^ 4) / Real.log x ^ 2) := by
      gcongr
    _ = (24 * C / c ^ 4) * x / Real.log x ^ 2 := by ring

/-- A global exponential prime-counting remainder gives the fixed log-square
remainder used in the Buchstab induction. -/
theorem exists_primeRemainder_log_sq_bound_of_exp_bound
    (hExp : ∃ c C : Real, 0 < c ∧ 0 < C ∧
      ∀ x : Real, 2 ≤ x →
        |primeRemainder x| ≤
          C * x / Real.exp (c * Real.sqrt (Real.log x))) :
    ∃ C2 : Real, 0 < C2 ∧
      ∀ x : Real, 2 ≤ x →
        |primeRemainder x| ≤ C2 * x / Real.log x ^ 2 := by
  obtain ⟨c, C, hc, hC, hExp⟩ := hExp
  refine ⟨24 * C / c ^ 4, by positivity, ?_⟩
  exact abs_primeRemainder_le_log_sq_of_exp hc hC.le hExp

end PrimesRestrictedDigits
