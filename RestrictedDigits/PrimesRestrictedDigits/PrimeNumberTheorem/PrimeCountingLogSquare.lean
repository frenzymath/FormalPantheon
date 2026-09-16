import PrimesRestrictedDigits.PrimeNumberTheorem.PsiExponentialLarge
import PrimesRestrictedDigits.BasicEstimates.PsiPrimeRemainder
import PrimesRestrictedDigits.BasicEstimates.PrimeRemainderGlobal

/-!
# The global fixed log-square prime-counting remainder

The optimized Perron estimate is first converted to an eventual `x / (log x)^2` bound for
`Chebyshev.psi`. The arithmetic transfer and bounded-range globalizer then provide the exact
Chapter 7 input.
-/

open Asymptotics Filter

namespace PrimesRestrictedDigits

/-- The fixed exponent-two quantitative prime-counting remainder used in the
source's Buchstab induction. -/
theorem primeCounting_log_sq_error :
    ∃ C : Real, 0 < C ∧
      ∀ x : Real, 2 ≤ x →
        |realPrimeCounting x - logarithmicIntegral x| <=
          C * x / Real.log x ^ 2 := by
  obtain ⟨c, K, L0, hc, hK, hL0, hLarge⟩ :=
    exists_abs_psi_sub_self_le_exp_large
  let d : Real := Real.sqrt (c / 8) / 2
  let A : Real := 24576 * K / c ^ 2
  have hd : 0 < d := by
    dsimp [d]
    exact zetaPerronDecay_pos hc.1
  have hA : 0 < A := by
    dsimp [A]
    exact div_pos (mul_pos (by norm_num) hK) (sq_pos_of_pos hc.1)
  have hpsi :
      (fun x : Real => Chebyshev.psi x - x) =O[atTop]
        (fun x : Real => x / Real.log x ^ 2) := by
    rw [isBigO_iff']
    refine ⟨A * (24 / d ^ 4), by positivity, ?_⟩
    filter_upwards [eventually_ge_atTop (Real.exp L0)] with x hx
    have hxFour : 4 ≤ x := by
      calc
        (4 : Real) = Real.exp (Real.log 4) :=
          (Real.exp_log (by norm_num)).symm
        _ ≤ Real.exp L0 :=
          Real.exp_le_exp.mpr hL0
        _ ≤ x := hx
    have hxOne : 1 ≤ x := by linarith
    have hxPos : 0 < x := by linarith
    have hLogPos : 0 < Real.log x :=
      Real.log_pos (by linarith)
    have hScale := log_sq_le_exp_sqrt_log_scale hd hxOne
    have hRecip :
        1 / Real.exp (d * Real.sqrt (Real.log x)) <=
          (24 / d ^ 4) / Real.log x ^ 2 := by
      rw [div_le_div_iff₀ (Real.exp_pos _) (sq_pos_of_pos hLogPos)]
      simpa using hScale
    have hLargeX := hLarge x hx
    have hLargeX' :
        |Chebyshev.psi x - x| <=
          A * x / Real.exp (d * Real.sqrt (Real.log x)) := by
      simpa [A, d] using hLargeX
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hxPos.le (sq_nonneg _))]
    calc
      |Chebyshev.psi x - x| <=
          A * x / Real.exp (d * Real.sqrt (Real.log x)) := hLargeX'
      _ = (A * x) *
          (1 / Real.exp (d * Real.sqrt (Real.log x))) := by ring
      _ <= (A * x) * ((24 / d ^ 4) / Real.log x ^ 2) := by
        exact mul_le_mul_of_nonneg_left hRecip (by positivity)
      _ = (A * (24 / d ^ 4)) *
          (x / Real.log x ^ 2) := by ring
  have hRemainderO :=
    primeRemainder_isBigO_log_sq_of_psi_sub_id hpsi
  obtain ⟨C, hC, hGlobal⟩ :=
    exists_primeRemainder_log_sq_bound_of_isBigO hRemainderO
  refine ⟨C, hC, ?_⟩
  intro x hx
  simpa [primeRemainder] using hGlobal x hx

end PrimesRestrictedDigits
