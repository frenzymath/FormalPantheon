import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Real.Sign
import Mathlib.MeasureTheory.Integral.Prod

/-!
# A sharp finite Dirichlet sine remainder

This file proves the coefficient-one finite remainder used in the
Bombieri--Vinogradov product cutoff.  The analytic proof is a direct
Laplace/Fubini argument; all integrals in the public statements are finite.

Source: `AkbaryHambrook2013v2`, Section 6, p. 17, specialized to zero phase.
Semantic review: `SEM-450`.
-/

open MeasureTheory Set
open scoped Interval

namespace BoundedGaps.Maynard

noncomputable section

private def laplaceSineIntegrand (u t : ℝ) : ℝ :=
  Real.exp (-u * t) * Real.sin u

private def dirichletSineRemainderIntegrand (X t : ℝ) : ℝ :=
  Real.exp (-X * t) * (Real.cos X + t * Real.sin X) / (1 + t ^ 2)

private lemma abs_cos_add_mul_sin_le_sqrt (X t : ℝ) :
    |Real.cos X + t * Real.sin X| ≤ Real.sqrt (1 + t ^ 2) := by
  apply Real.abs_le_sqrt
  nlinarith [sq_nonneg (t * Real.cos X - Real.sin X), Real.cos_sq_add_sin_sq X]

private lemma norm_dirichletSineRemainderIntegrand_le_exp (X t : ℝ) :
    ‖dirichletSineRemainderIntegrand X t‖ ≤ Real.exp (-X * t) := by
  have hden : 0 < 1 + t ^ 2 := by positivity
  have hsqrt : Real.sqrt (1 + t ^ 2) ≤ 1 + t ^ 2 := by
    rw [Real.sqrt_le_left hden.le]
    nlinarith [sq_nonneg t]
  rw [dirichletSineRemainderIntegrand, Real.norm_eq_abs, abs_div, abs_mul,
    abs_of_pos (Real.exp_pos _), abs_of_pos hden]
  calc
    Real.exp (-X * t) * |Real.cos X + t * Real.sin X| / (1 + t ^ 2)
        ≤ Real.exp (-X * t) * Real.sqrt (1 + t ^ 2) / (1 + t ^ 2) := by
          gcongr
          exact abs_cos_add_mul_sin_le_sqrt X t
    _ ≤ Real.exp (-X * t) * (1 + t ^ 2) / (1 + t ^ 2) := by gcongr
    _ = Real.exp (-X * t) := by field_simp

private lemma integrableOn_dirichletSineRemainderIntegrand_Ioi {X : ℝ} (hX : 0 < X) :
    IntegrableOn (dirichletSineRemainderIntegrand X) (Ioi 0) := by
  refine (integrableOn_exp_mul_Ioi (a := -X) (by linarith) 0).mono' ?_ ?_
  · unfold dirichletSineRemainderIntegrand
    exact ((by fun_prop : Continuous fun t : ℝ ↦
        Real.exp (-X * t) * (Real.cos X + t * Real.sin X)).div
      (by fun_prop : Continuous fun t : ℝ ↦ 1 + t ^ 2)
      (fun t ↦ by positivity)).aestronglyMeasurable
  filter_upwards with t
  exact norm_dirichletSineRemainderIntegrand_le_exp X t

private lemma integral_laplaceSineIntegrand {u : ℝ} (hu : 0 < u) :
    ∫ t in Ioi 0, laplaceSineIntegrand u t = Real.sinc u := by
  unfold laplaceSineIntegrand
  rw [integral_mul_const, integral_exp_mul_Ioi (a := -u) (by linarith)]
  rw [Real.sinc_of_ne_zero hu.ne']
  simp
  field_simp

private lemma integral_norm_laplaceSineIntegrand_le_one {u : ℝ} (hu : 0 < u) :
    ∫ t in Ioi 0, ‖laplaceSineIntegrand u t‖ ≤ 1 := by
  calc
    ∫ t in Ioi 0, ‖laplaceSineIntegrand u t‖ =
        (∫ t in Ioi 0, Real.exp (-u * t)) * |Real.sin u| := by
          unfold laplaceSineIntegrand
          simp_rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
          rw [integral_mul_const]
    _ = |Real.sin u| / u := by
      rw [integral_exp_mul_Ioi (a := -u) (by linarith)]
      simp
      field_simp
    _ ≤ 1 := by
      rw [div_le_one hu]
      simpa [abs_of_pos hu] using (Real.abs_sin_le_abs : |Real.sin u| ≤ |u|)

private lemma integrable_laplaceSineIntegrand_prod (X : ℝ) :
    Integrable (Function.uncurry laplaceSineIntegrand)
      ((volume.restrict (Ioc 0 X)).prod (volume.restrict (Ioi 0))) := by
  have hmeas : AEStronglyMeasurable (Function.uncurry laplaceSineIntegrand)
      ((volume.restrict (Ioc 0 X)).prod (volume.restrict (Ioi 0))) := by
    unfold laplaceSineIntegrand Function.uncurry
    fun_prop
  rw [integrable_prod_iff hmeas]
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hu0 : 0 < u := hu.1
    simpa [laplaceSineIntegrand] using
      (integrableOn_exp_mul_Ioi (a := -u) (by linarith) 0).mul_const (Real.sin u)
  · refine (integrableOn_const (C := (1 : ℝ)) measure_Ioc_lt_top.ne).mono'
      hmeas.norm.integral_prod_right' ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]
    exact integral_norm_laplaceSineIntegrand_le_one hu.1

private lemma hasDerivAt_laplaceSineAntiderivative (t u : ℝ) :
    HasDerivAt
      (fun v : ℝ ↦
        -Real.exp (-v * t) * (Real.cos v + t * Real.sin v) / (1 + t ^ 2))
      (laplaceSineIntegrand u t) u := by
  have hden : 1 + t ^ 2 ≠ 0 := by positivity
  have hexp : HasDerivAt (fun v : ℝ ↦ Real.exp (-v * t))
      (-t * Real.exp (-u * t)) u := by
    simpa only [Pi.neg_apply, id_eq, mul_neg, neg_mul, one_mul, mul_one, mul_comm] using
      ((hasDerivAt_id u).neg.mul_const t).exp
  have htrig : HasDerivAt (fun v : ℝ ↦ Real.cos v + t * Real.sin v)
      (-Real.sin u + t * Real.cos u) u :=
    (Real.hasDerivAt_cos u).add ((Real.hasDerivAt_sin u).const_mul t)
  have hvalue :
      -((-t * Real.exp (-u * t)) * (Real.cos u + t * Real.sin u) +
          Real.exp (-u * t) * (-Real.sin u + t * Real.cos u)) / (1 + t ^ 2) =
        laplaceSineIntegrand u t := by
    unfold laplaceSineIntegrand
    field_simp [hden]
    ring_nf
  exact (by
    simpa only [Pi.mul_apply, Pi.neg_apply, Pi.div_apply, neg_mul] using
      ((hexp.mul htrig).neg.div_const (1 + t ^ 2)).congr_deriv hvalue)

private lemma intervalIntegral_laplaceSineIntegrand (X t : ℝ) :
    ∫ u in (0 : ℝ)..X, laplaceSineIntegrand u t =
      (1 - Real.exp (-X * t) * (Real.cos X + t * Real.sin X)) / (1 + t ^ 2) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ ↦ hasDerivAt_laplaceSineAntiderivative t u)
    (Continuous.intervalIntegrable (by unfold laplaceSineIntegrand; fun_prop) 0 X)]
  simp only [Real.exp_zero, Real.cos_zero, Real.sin_zero, neg_zero, zero_mul]
  ring

private lemma integral_sinc_eq_pi_div_two_sub_remainder {X : ℝ} (hX : 0 < X) :
    ∫ u in (0 : ℝ)..X, Real.sinc u =
      Real.pi / 2 - ∫ t in Ioi 0, dirichletSineRemainderIntegrand X t := by
  have hprod := integrable_laplaceSineIntegrand_prod X
  have hprod' : Integrable (Function.uncurry laplaceSineIntegrand)
      ((volume.restrict (uIoc 0 X)).prod (volume.restrict (Ioi 0))) := by
    simpa [uIoc_of_le hX.le] using hprod
  have hswap := MeasureTheory.intervalIntegral_integral_swap hprod'
  have hleft :
      (∫ u in (0 : ℝ)..X, ∫ t in Ioi 0, laplaceSineIntegrand u t) =
        ∫ u in (0 : ℝ)..X, Real.sinc u := by
    apply intervalIntegral.integral_congr_Ioo_of_le hX.le
    intro u hu
    exact integral_laplaceSineIntegrand hu.1
  have hright :
      (∫ t in Ioi 0, ∫ u in (0 : ℝ)..X, laplaceSineIntegrand u t) =
        Real.pi / 2 - ∫ t in Ioi 0, dirichletSineRemainderIntegrand X t := by
    simp_rw [intervalIntegral_laplaceSineIntegrand]
    have hbase : IntegrableOn (fun t : ℝ ↦ (1 + t ^ 2)⁻¹) (Ioi 0) :=
      integrable_inv_one_add_sq.integrableOn
    have hrem := integrableOn_dirichletSineRemainderIntegrand_Ioi hX
    rw [show (fun t : ℝ ↦
          (1 - Real.exp (-X * t) * (Real.cos X + t * Real.sin X)) / (1 + t ^ 2)) =
        (fun t ↦ (1 + t ^ 2)⁻¹ - dirichletSineRemainderIntegrand X t) by
          funext t
          rw [dirichletSineRemainderIntegrand]
          ring]
    rw [integral_sub hbase hrem, integral_Ioi_inv_one_add_sq]
    simp
  rw [← hleft, hswap, hright]

/-- The coefficient-one finite Dirichlet sine remainder at a positive endpoint.

See `AkbaryHambrook2013v2`, Section 6, p. 17, and semantic review `SEM-450`.
-/
theorem abs_integral_sinc_sub_pi_div_two_le_inv
    {X : ℝ} (hX : 0 < X) :
    |(∫ u in (0 : ℝ)..X, Real.sinc u) - Real.pi / 2| ≤ X ^ (-1 : ℤ) := by
  rw [integral_sinc_eq_pi_div_two_sub_remainder hX]
  have hrem := integrableOn_dirichletSineRemainderIntegrand_Ioi hX
  calc
    |(Real.pi / 2 - ∫ t in Ioi 0, dirichletSineRemainderIntegrand X t) - Real.pi / 2| =
        |∫ t in Ioi 0, dirichletSineRemainderIntegrand X t| := by ring_nf; simp
    _ ≤ ∫ t in Ioi 0, ‖dirichletSineRemainderIntegrand X t‖ :=
      by
        simpa only [Real.norm_eq_abs] using
          (norm_integral_le_integral_norm
            (dirichletSineRemainderIntegrand X) (μ := volume.restrict (Ioi 0)))
    _ ≤ ∫ t in Ioi 0, Real.exp (-X * t) := by
      exact integral_mono_ae hrem.norm
        (integrableOn_exp_mul_Ioi (a := -X) (by linarith) 0)
        (ae_of_all _ fun t ↦ norm_dirichletSineRemainderIntegrand_le_exp X t)
    _ = X ^ (-1 : ℤ) := by
      rw [integral_exp_mul_Ioi (a := -X) (by linarith)]
      simp [zpow_neg]

/-- The signed finite Dirichlet sine remainder at any nonzero endpoint. -/
theorem abs_integral_sinc_sub_sign_pi_div_two_le_inv_abs
    {X : ℝ} (hX : X ≠ 0) :
    |(∫ u in (0 : ℝ)..X, Real.sinc u) -
      Real.sign X * (Real.pi / 2)| ≤ |X| ^ (-1 : ℤ) := by
  rcases lt_or_gt_of_ne hX with hXneg | hXpos
  · have h := abs_integral_sinc_sub_pi_div_two_le_inv (X := -X) (by linarith)
    have hneg : (∫ u in (0 : ℝ)..(-X), Real.sinc u) =
        -(∫ u in (0 : ℝ)..X, Real.sinc u) := by
      calc
        (∫ u in (0 : ℝ)..(-X), Real.sinc u) =
            ∫ u in (0 : ℝ)..(-X), Real.sinc (-u) := by
              apply intervalIntegral.integral_congr
              intro u _
              exact (Real.sinc_neg u).symm
        _ = ∫ u in X..(0 : ℝ), Real.sinc u := by
          simpa using (intervalIntegral.integral_comp_neg Real.sinc
            (a := (0 : ℝ)) (b := -X))
        _ = -(∫ u in (0 : ℝ)..X, Real.sinc u) :=
          intervalIntegral.integral_symm 0 X
    rw [hneg] at h
    have habs :
        |-(∫ u in (0 : ℝ)..X, Real.sinc u) - Real.pi / 2| =
          |(∫ u in (0 : ℝ)..X, Real.sinc u) + Real.pi / 2| := by
      rw [show -(∫ u in (0 : ℝ)..X, Real.sinc u) - Real.pi / 2 =
        -((∫ u in (0 : ℝ)..X, Real.sinc u) + Real.pi / 2) by ring, abs_neg]
    rw [habs] at h
    simpa [Real.sign_of_neg hXneg, abs_of_neg hXneg, zpow_neg] using h
  · simpa [Real.sign_of_pos hXpos, abs_of_pos hXpos] using
      abs_integral_sinc_sub_pi_div_two_le_inv hXpos

/-- The signed, scaled finite Dirichlet sine remainder.

The multiplier `Y` is essential: it is the Jacobian-normalized kernel under
the substitution `u = Y * t`.
-/
theorem abs_integral_mul_sinc_sub_sign_pi_div_two_le_inv
    {T Y : ℝ} (hT : 0 < T) (hY : Y ≠ 0) :
    |(∫ t in (0 : ℝ)..T, Y * Real.sinc (Y * t)) -
      Real.sign Y * (Real.pi / 2)| ≤ (T * |Y|) ^ (-1 : ℤ) := by
  have hTY : T * Y ≠ 0 := mul_ne_zero hT.ne' hY
  have h := abs_integral_sinc_sub_sign_pi_div_two_le_inv_abs hTY
  have hsign : Real.sign (T * Y) = Real.sign Y := by
    rcases lt_or_gt_of_ne hY with hYneg | hYpos
    · rw [Real.sign_of_neg (mul_neg_of_pos_of_neg hT hYneg), Real.sign_of_neg hYneg]
    · rw [Real.sign_of_pos (mul_pos hT hYpos), Real.sign_of_pos hYpos]
  have hsub : (∫ t in (0 : ℝ)..T, Y * Real.sinc (Y * t)) =
      ∫ u in (0 : ℝ)..(T * Y), Real.sinc u := by
    rw [intervalIntegral.integral_const_mul]
    have hchange := intervalIntegral.mul_integral_comp_mul_left (f := Real.sinc) Y
      (a := (0 : ℝ)) (b := T)
    simp only [mul_zero, mul_comm] at hchange
    exact hchange
  rw [← hsub] at h
  simpa [hsign, abs_mul, abs_of_pos hT, mul_assoc,
    mul_comm, mul_left_comm] using h

end

end BoundedGaps.Maynard
