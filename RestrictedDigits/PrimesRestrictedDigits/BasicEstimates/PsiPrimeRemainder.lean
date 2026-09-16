import PrimesRestrictedDigits.BasicEstimates.LogarithmicIntegral
import Mathlib.NumberTheory.Chebyshev

/-!
# Transfer from Chebyshev psi to the prime-counting remainder

This is the fixed log-square partial-summation bridge in the proof of
Montgomery--Vaughan, Chapter 6, Theorem 6.9. The quantitative estimate for
`Chebyshev.psi` remains an explicit premise.
-/

open Asymptotics Filter MeasureTheory Set

namespace PrimesRestrictedDigits

private theorem sqrt_isLittleO_pntLogSqScale :
    Real.sqrt =o[atTop] (fun x : Real => x / Real.log x ^ 2) := by
  apply isLittleO_mul_iff_isLittleO_div _ |>.mp
  · conv => arg 2; ext; rw [mul_comm]
    apply isLittleO_mul_iff_isLittleO_div _ |>.mpr
    · simp_rw [Real.div_sqrt, Real.sqrt_eq_rpow, ← Real.rpow_two]
      exact isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0 : Real) < 1 / 2)
    filter_upwards [eventually_gt_atTop 0] with x hx using
      Real.sqrt_ne_zero'.mpr hx
  filter_upwards [eventually_gt_atTop 1] with x hx
  exact pow_ne_zero _ (Real.log_ne_zero.mpr ⟨by linarith, by linarith, by linarith⟩)

theorem logarithmicIntegral_eq_div_add_integral {x : Real} (hx : 2 ≤ x) :
    logarithmicIntegral x =
      x / Real.log x - 2 / Real.log 2 +
        ∫ t in 2..x, 1 / Real.log t ^ 2 := by
  let F : Real → Real := fun t => t / Real.log t
  let f : Real → Real := fun t => 1 / Real.log t - 1 / Real.log t ^ 2
  have hcont : ContinuousOn F (Set.Icc 2 x) := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog0 : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1]) (by linarith [ht.1])
    exact ((hasDerivAt_id t).div (Real.hasDerivAt_log ht0) hlog0).continuousAt.continuousWithinAt
  have hderiv : ∀ t ∈ Set.Ioo 2 x, HasDerivAt F (f t) t := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog0 : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1]) (by linarith [ht.1])
    have h := (hasDerivAt_id t).div (Real.hasDerivAt_log ht0) hlog0
    apply h.congr_deriv
    dsimp [f]
    field_simp [hlog0, ht0]
  have hli : IntervalIntegrable (fun t : Real => 1 / Real.log t) volume 2 x := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog0 : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1]) (by linarith [ht.1])
    fun_prop
  have hsq : IntervalIntegrable (fun t : Real => 1 / Real.log t ^ 2) volume 2 x :=
    Chebyshev.intervalIntegrable_one_div_log_sq (by norm_num) (by linarith)
  have hf : IntervalIntegrable f volume 2 x := by
    simpa [f] using hli.sub hsq
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := F) (f' := f) hx hcont hderiv hf
  rw [show (∫ t in 2..x, f t) =
      (∫ t in 2..x, 1 / Real.log t) -
        ∫ t in 2..x, 1 / Real.log t ^ 2 by
      simpa [f] using intervalIntegral.integral_sub hli hsq] at hftc
  change (∫ t in 2..x, 1 / Real.log t) = _
  dsimp [F] at hftc
  linarith

private theorem one_isLittleO_pntLogSqScale :
    (fun _ : Real => (1 : Real)) =o[atTop]
      (fun x : Real => x / Real.log x ^ 2) := by
  have hlogNe : ∀ᶠ x : Real in atTop, Real.log x ^ 2 ≠ 0 := by
    filter_upwards [eventually_gt_atTop 1] with x hx
    exact pow_ne_zero _ (Real.log_ne_zero.mpr ⟨by linarith, by linarith, by linarith⟩)
  apply (isLittleO_mul_iff_isLittleO_div
    (f := fun x : Real => Real.log x ^ 2)
    (g := fun _ : Real => (1 : Real)) (h := id) hlogNe).mp
  simpa using (Real.isLittleO_pow_log_id_atTop (n := 2))

private theorem div_sub_logarithmicIntegral_isBigO :
    (fun x : Real => x / Real.log x - logarithmicIntegral x) =O[atTop]
      (fun x : Real => x / Real.log x ^ 2) := by
  have hconst :
      (fun _ : Real => (2 : Real) / Real.log 2) =O[atTop]
        (fun x : Real => x / Real.log x ^ 2) :=
    (isBigO_const_const ((2 : Real) / Real.log 2)
      (by norm_num : (1 : Real) ≠ 0) atTop).trans
        one_isLittleO_pntLogSqScale.isBigO
  have hbound := hconst.sub Chebyshev.integral_one_div_log_sq_isBigO
  have heq :
      (fun x : Real => x / Real.log x - logarithmicIntegral x) =ᶠ[atTop]
        fun x => 2 / Real.log 2 - ∫ t in 2..x, 1 / Real.log t ^ 2 := by
    filter_upwards [eventually_ge_atTop 2] with x hx
    rw [logarithmicIntegral_eq_div_add_integral hx]
    ring
  exact heq.trans_isBigO hbound

/-- An eventual log-square error for `Chebyshev.psi` transfers to the same
eventual scale for the source-normalized prime-counting remainder. -/
theorem primeRemainder_isBigO_log_sq_of_psi_sub_id
    (hpsi : (fun x : Real => Chebyshev.psi x - x) =O[atTop]
      fun x : Real => x / Real.log x ^ 2) :
    (fun x : Real => primeRemainder x) =O[atTop]
      fun x : Real => x / Real.log x ^ 2 := by
  have hpsiTheta :
      (fun x : Real => Chebyshev.psi x - Chebyshev.theta x) =O[atTop]
        (fun x : Real => x / Real.log x ^ 2) := by
    exact (Chebyshev.isBigO_psi_sub_theta_sqrt.trans
      sqrt_isLittleO_pntLogSqScale.isBigO).congr_left fun x => rfl
  have htheta :
      (fun x : Real => Chebyshev.theta x - x) =O[atTop]
        (fun x : Real => x / Real.log x ^ 2) := by
    exact (hpsi.sub hpsiTheta).congr_left fun x => by ring
  have hinvLog :
      (fun x : Real => 1 / Real.log x) =O[atTop]
        (fun _ : Real => (1 : Real)) := by
    exact Real.tendsto_log_atTop.inv_tendsto_atTop.isBigO_one Real |>.congr_left
      fun x => by simp [one_div]
  have hthetaDiv :
      (fun x : Real => (Chebyshev.theta x - x) / Real.log x) =O[atTop]
        (fun x : Real => x / Real.log x ^ 2) := by
    simpa [div_eq_mul_inv] using htheta.mul hinvLog
  have hsum :=
    (Chebyshev.primeCounting_sub_theta_div_log_isBigO.add hthetaDiv).add
      div_sub_logarithmicIntegral_isBigO
  exact hsum.congr_left fun x => by
    unfold primeRemainder realPrimeCounting
    ring

end PrimesRestrictedDigits
