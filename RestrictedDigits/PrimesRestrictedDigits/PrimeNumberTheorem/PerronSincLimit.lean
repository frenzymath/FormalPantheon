import PrimesRestrictedDigits.PrimeNumberTheorem.PerronSineIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
/-! # PerronSincLimit -/

open Complex MeasureTheory Set Filter
open scoped Interval Topology

namespace PrimesRestrictedDigits

private noncomputable def dampedSincKernel (a t u : Real) : Complex :=
  Complex.exp ((((-a : Real) : Complex) + Complex.I * (t : Complex)) * (u : Complex))

private theorem integrable_dampedSincKernel {a : Real} (ha : 0 < a) :
    Integrable (Function.uncurry (dampedSincKernel a))
      ((volume.restrict (uIoc 0 1)).prod (volume.restrict (Ioi 0))) := by
  have ht : Integrable (fun _ : Real => (1 : Real)) (volume.restrict (uIoc 0 1)) :=
    integrableOn_const (by simp)
  have hu : Integrable (fun u : Real => Real.exp (-a * u))
      (volume.restrict (Ioi 0)) :=
    integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ha) 0
  have hmeas : AEStronglyMeasurable (Function.uncurry (dampedSincKernel a))
      ((volume.restrict (uIoc 0 1)).prod (volume.restrict (Ioi 0))) := by
    apply Continuous.aestronglyMeasurable
    unfold dampedSincKernel Function.uncurry
    fun_prop
  refine (ht.mul_prod hu).mono' hmeas ?_
  filter_upwards with z
  change ‖dampedSincKernel a z.1 z.2‖ <= (1 : Real) * Real.exp (-a * z.2)
  rw [dampedSincKernel, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.I_re, Complex.I_im,
    Complex.mul_im, Complex.ofReal_im, zero_mul, one_mul, add_zero, sub_zero,
    mul_zero, zero_add]
  exact le_refl (Real.exp (-a * z.2))

private theorem integral_dampedSincKernel_Ioi {a t : Real} (ha : 0 < a) :
    (∫ u : Real in Ioi 0, dampedSincKernel a t u) =
      -1 / (((-a : Real) : Complex) + Complex.I * (t : Complex)) := by
  unfold dampedSincKernel
  rw [integral_exp_mul_complex_Ioi]
  · simp
  · simp only [Complex.add_re,  Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul,
      one_mul, sub_zero, add_zero]
    linarith

private theorem integral_dampedSincKernel_Ioi_re {a t : Real} (ha : 0 < a) :
    (∫ u : Real in Ioi 0, dampedSincKernel a t u).re =
      a / (a ^ 2 + t ^ 2) := by
  rw [integral_dampedSincKernel_Ioi ha]
  simp only [Complex.div_re, Complex.neg_re, Complex.one_re, Complex.one_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.mul_re, Complex.mul_im, zero_mul,
    one_mul, sub_zero, add_zero, zero_add, Complex.normSq_apply,
    Complex.neg_im, neg_zero]
  ring

private theorem integral_cos_mul_eq_sinc (u : Real) :
    (∫ t : Real in 0..1, Real.cos (t * u)) = Real.sinc u := by
  by_cases hu : u = 0
  · simp [hu]
  rw [intervalIntegral.integral_comp_mul_right Real.cos hu]
  simp [Real.sinc_of_ne_zero hu, div_eq_mul_inv]
  ring

private theorem intervalIntegral_dampedSincKernel_re (a u : Real) :
    (∫ t : Real in 0..1, dampedSincKernel a t u).re =
      Real.exp (-a * u) * Real.sinc u := by
  have hint : IntervalIntegrable
      (fun t : Real => dampedSincKernel a t u) volume 0 1 := by
    apply Continuous.intervalIntegrable
    unfold dampedSincKernel
    fun_prop
  calc
    (∫ t : Real in 0..1, dampedSincKernel a t u).re =
        ∫ t : Real in 0..1, (dampedSincKernel a t u).re :=
      (intervalIntegral.intervalIntegral_re hint).symm
    _ = Real.exp (-a * u) * Real.sinc u := by
      have hpoint : (fun t : Real => (dampedSincKernel a t u).re) =
          fun t : Real => Real.exp (-a * u) * Real.cos (t * u) := by
        funext t
        rw [dampedSincKernel, Complex.exp_re]
        simp only [Complex.mul_re, Complex.add_re, Complex.add_im,
          Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.mul_im,
          zero_mul, one_mul, sub_zero, add_zero, zero_add, mul_zero]
      rw [hpoint, intervalIntegral.integral_const_mul, integral_cos_mul_eq_sinc]

private theorem dampedSincKernel_swap {a : Real} (ha : 0 < a) :
    (∫ t : Real in 0..1, ∫ u : Real in Ioi 0, dampedSincKernel a t u) =
      ∫ u : Real in Ioi 0, ∫ t : Real in 0..1, dampedSincKernel a t u := by
  exact intervalIntegral_integral_swap (integrable_dampedSincKernel ha)

private theorem integral_exp_neg_mul_sinc_Ioi {a : Real} (ha : 0 < a) :
    (∫ u : Real in Ioi 0, Real.exp (-a * u) * Real.sinc u) =
      Real.arctan (1 / a) := by
  have hf := integrable_dampedSincKernel ha
  have hleft : IntervalIntegrable
      (fun t : Real => ∫ u : Real in Ioi 0, dampedSincKernel a t u)
      volume 0 1 := by
    rw [intervalIntegrable_iff]
    exact hf.integral_prod_left
  have hright : Integrable
      (fun u : Real => ∫ t : Real in 0..1, dampedSincKernel a t u)
      (volume.restrict (Ioi 0)) := by
    have h := hf.integral_prod_right
    simpa [intervalIntegral.integral_of_le (by norm_num : (0 : Real) <= 1),
      uIoc_of_le (by norm_num : (0 : Real) <= 1)] using h
  have hswap_re := congrArg Complex.re (dampedSincKernel_swap ha)
  have hre :
      (∫ t : Real in 0..1,
        (∫ u : Real in Ioi 0, dampedSincKernel a t u).re) =
        ∫ u : Real in Ioi 0,
          (∫ t : Real in 0..1, dampedSincKernel a t u).re := by
    calc
      _ = (∫ t : Real in 0..1,
          ∫ u : Real in Ioi 0, dampedSincKernel a t u).re :=
        intervalIntegral.intervalIntegral_re hleft
      _ = (∫ u : Real in Ioi 0,
          ∫ t : Real in 0..1, dampedSincKernel a t u).re := hswap_re
      _ = _ := (integral_re hright).symm
  have hleft_eq :
      (∫ t : Real in 0..1,
        (∫ u : Real in Ioi 0, dampedSincKernel a t u).re) =
        Real.arctan (1 / a) := by
    calc
      _ = ∫ t : Real in 0..1, a / (a ^ 2 + t ^ 2) := by
        apply intervalIntegral.integral_congr
        intro t _
        exact integral_dampedSincKernel_Ioi_re ha
      _ = Real.arctan (1 / a) := by
        rw [integral_div_sq_add_sq]
        simp
  have hright_eq :
      (∫ u : Real in Ioi 0,
        (∫ t : Real in 0..1, dampedSincKernel a t u).re) =
        ∫ u : Real in Ioi 0, Real.exp (-a * u) * Real.sinc u := by
    apply integral_congr_ae
    filter_upwards with u
    exact intervalIntegral_dampedSincKernel_re a u
  rw [hleft_eq, hright_eq] at hre
  exact hre.symm

private theorem integrableOn_exp_neg_mul_sinc_Ioi {a B : Real} (ha : 0 < a) :
    IntegrableOn (fun u : Real => Real.exp (-a * u) * Real.sinc u) (Ioi B) := by
  have hexp : IntegrableOn (fun u : Real => Real.exp (-a * u)) (Ioi B) :=
    integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ha) B
  refine hexp.mono' (by fun_prop) ?_
  filter_upwards with u
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  nlinarith [Real.abs_sinc_le_one u, Real.exp_pos (-a * u)]

private theorem abs_integral_exp_neg_mul_sinc_Ioi_le {a B : Real}
    (ha : 0 < a) (hB : 0 < B) :
    abs (∫ u : Real in Ioi B, Real.exp (-a * u) * Real.sinc u) <= 2 / B := by
  let U : Real -> Real := fun x => Real.exp (-a * x)
  let H : Real -> Real := fun x => ∫ u : Real in B..x, Real.sinc u
  let U' : Real -> Real := fun x => -a * Real.exp (-a * x)
  have hUderiv (x : Real) : HasDerivAt U (U' x) x := by
    dsimp [U, U']
    have h := (Real.hasDerivAt_exp (-a * x)).comp x
      ((hasDerivAt_const x (-a)).mul (hasDerivAt_id x))
    have h' := h.congr_deriv (g' := U' x) (by dsimp [U']; ring)
    apply h'.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun y => by
      simp only [Function.comp_apply]
  have hHderiv (x : Real) : HasDerivAt H (Real.sinc x) x := by
    dsimp [H]
    exact intervalIntegral.integral_hasDerivAt_right
      (Real.continuous_sinc.intervalIntegrable B x)
      Real.continuous_sinc.stronglyMeasurable.stronglyMeasurableAtFilter
      Real.continuous_sinc.continuousAt
  have hHcont : Continuous H :=
    continuous_iff_continuousAt.2 fun x => (hHderiv x).continuousAt
  have hHbound {x : Real} (hx : B <= x) : abs (H x) <= 2 / B :=
    abs_dirichletSineIntegral_le_two_div hB hx
  have huv' : IntegrableOn (U * fun x : Real => Real.sinc x) (Ioi B) := by
    change IntegrableOn (fun x : Real => U x * Real.sinc x) (Ioi B)
    simpa [U, neg_mul] using
      integrableOn_exp_neg_mul_sinc_Ioi (a := a) (B := B) ha
  have hu'v : IntegrableOn (U' * H) (Ioi B) := by
    have hexp : Integrable (fun x : Real => Real.exp (-a * x))
        (volume.restrict (Ioi B)) :=
      integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ha) B
    have hdom : Integrable (fun x : Real => (2 * a / B) * Real.exp (-a * x))
        (volume.restrict (Ioi B)) := hexp.const_mul (2 * a / B)
    refine hdom.mono' (by
      apply Continuous.aestronglyMeasurable
      exact (by fun_prop :
        Continuous (fun x : Real => -a * Real.exp (-a * x))).mul hHcont) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change abs (-a * Real.exp (-a * x) * H x) <=
      (2 * a / B) * Real.exp (-a * x)
    calc
      abs (-a * Real.exp (-a * x) * H x) =
          (a * Real.exp (-a * x)) * abs (H x) := by
        rw [abs_mul, abs_mul, abs_neg, abs_of_pos ha,
          abs_of_pos (Real.exp_pos _)]
      _ <= (a * Real.exp (-a * x)) * (2 / B) :=
        mul_le_mul_of_nonneg_left (hHbound hx.le)
          (mul_nonneg ha.le (Real.exp_pos _).le)
      _ = (2 * a / B) * Real.exp (-a * x) := by ring
  have hzero : Tendsto (U * H) (nhdsWithin B (Ioi B)) (nhds 0) := by
    change Tendsto (fun x => U x * H x) (nhdsWithin B (Ioi B)) (nhds 0)
    have hc : ContinuousAt (fun x => U x * H x) B :=
      (hUderiv B).continuousAt.mul (hHderiv B).continuousAt
    have ht : Tendsto (fun x => U x * H x) (nhdsWithin B (Ioi B))
        (nhds (U B * H B)) := hc.tendsto.mono_left inf_le_left
    have hval : U B * H B = 0 := by simp [H]
    rw [hval] at ht
    exact ht
  have hUzero : Tendsto U atTop (nhds 0) := by
    dsimp [U]
    exact Real.tendsto_exp_atBot.comp
      (tendsto_const_nhds.neg_mul_atTop (neg_lt_zero.mpr ha) tendsto_id)
  have hinfty : Tendsto (U * H) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (g := fun x : Real => U x * (2 / B))
    · exact Filter.Eventually.of_forall fun x => norm_nonneg _
    · filter_upwards [eventually_gt_atTop B] with x hx
      change abs (U x * H x) <= U x * (2 / B)
      rw [abs_mul, abs_of_pos]
      · exact mul_le_mul_of_nonneg_left (hHbound hx.le) (Real.exp_pos _).le
      · exact Real.exp_pos _
    · simpa using hUzero.mul_const (2 / B)
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul
    (a := B) (u := U) (v := H) (u' := U') (v' := Real.sinc)
    (fun x _ => hUderiv x) (fun x _ => hHderiv x) huv' hu'v hzero hinfty
  have hid :
      (∫ u : Real in Ioi B, Real.exp (-a * u) * Real.sinc u) =
        -(∫ u : Real in Ioi B, (-a * Real.exp (-a * u)) * H u) := by
    simpa [U, U', Pi.mul_apply] using hibp
  rw [hid, abs_neg]
  calc
    abs (∫ u : Real in Ioi B, (-a * Real.exp (-a * u)) * H u) <=
        ∫ u : Real in Ioi B, (2 * a / B) * Real.exp (-a * u) := by
      change ‖∫ u : Real in Ioi B, (-a * Real.exp (-a * u)) * H u‖ <= _
      apply norm_integral_le_of_norm_le
      · exact (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ha) B).const_mul
          (2 * a / B)
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        rw [Real.norm_eq_abs]
        calc
          abs (-a * Real.exp (-a * x) * H x) =
              (a * Real.exp (-a * x)) * abs (H x) := by
            rw [abs_mul, abs_mul, abs_neg, abs_of_pos ha,
              abs_of_pos (Real.exp_pos _)]
          _ <= (a * Real.exp (-a * x)) * (2 / B) :=
            mul_le_mul_of_nonneg_left (hHbound hx.le)
              (mul_nonneg ha.le (Real.exp_pos _).le)
          _ = (2 * a / B) * Real.exp (-a * x) := by ring
    _ = (2 / B) * Real.exp (-a * B) := by
      rw [integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr ha)]
      field_simp
    _ <= 2 / B := by
      have hexp : Real.exp (-a * B) <= 1 := by
        rw [<- Real.exp_zero]
        exact Real.exp_le_exp.mpr (by nlinarith)
      exact mul_le_of_le_one_right (by positivity) hexp

private theorem integral_exp_neg_mul_sinc_Ioi_eq_add {a B : Real}
    (ha : 0 < a) (hB : 0 < B) :
    (∫ u : Real in Ioi 0, Real.exp (-a * u) * Real.sinc u) =
      (∫ u : Real in 0..B, Real.exp (-a * u) * Real.sinc u) +
        ∫ u : Real in Ioi B, Real.exp (-a * u) * Real.sinc u := by
  let f : Real -> Real := fun u => Real.exp (-a * u) * Real.sinc u
  have htotal : IntegrableOn f (Ioi 0) := by
    simpa [f] using integrableOn_exp_neg_mul_sinc_Ioi (a := a) (B := 0) ha
  have hlocal : IntegrableOn f (Ioc 0 B) :=
    htotal.mono_set fun _ hx => hx.1
  have htail : IntegrableOn f (Ioi B) :=
    htotal.mono_set fun _ hx => hB.trans hx
  have hunion := setIntegral_union
    (f := f) (s := Ioc 0 B) (t := Ioi B)
    (by rw [Set.disjoint_left]; exact fun _ hx hx' => (not_lt_of_ge hx.2) hx')
    measurableSet_Ioi hlocal htail
  rw [Ioc_union_Ioi_eq_Ioi hB.le] at hunion
  rw [intervalIntegral.integral_of_le hB.le]
  exact hunion

/-- The finite Dirichlet sine integral has an explicit error from `pi/2`. -/
theorem abs_dirichletSineIntegral_sub_pi_div_two_le_two_div
    {B : Real} (hB : 0 < B) :
    abs ((∫ u : Real in 0..B, Real.sinc u) - Real.pi / 2) <= 2 / B := by
  let dampedLocal : Real -> Real := fun r =>
    ∫ u : Real in 0..B, Real.exp (-(r ^ (-1 : Int)) * u) * Real.sinc u
  have hlocal_cont : Continuous (fun a : Real =>
      ∫ u : Real in 0..B, Real.exp (-a * u) * Real.sinc u) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    fun_prop
  have hlocal_lim : Tendsto dampedLocal atTop
      (nhds (∫ u : Real in 0..B, Real.sinc u)) := by
    have h := hlocal_cont.continuousAt.tendsto.comp tendsto_inv_atTop_zero
    dsimp [dampedLocal]
    simp only [zpow_neg_one]
    convert h using 1
    · funext r
      rfl
    · simp
  have harctan_lim : Tendsto Real.arctan atTop (nhds (Real.pi / 2)) :=
    (tendsto_nhdsWithin_iff.mp Real.tendsto_arctan_atTop).1
  have hdiff_lim : Tendsto (fun r => abs (dampedLocal r - Real.arctan r)) atTop
      (nhds (abs ((∫ u : Real in 0..B, Real.sinc u) - Real.pi / 2))) :=
    (hlocal_lim.sub harctan_lim).abs
  apply le_of_tendsto hdiff_lim
  filter_upwards [eventually_gt_atTop 0] with r hr
  have ha : 0 < r ^ (-1 : Int) := zpow_pos hr _
  have hsplit := integral_exp_neg_mul_sinc_Ioi_eq_add ha hB
  have htotal := integral_exp_neg_mul_sinc_Ioi ha
  have htail := abs_integral_exp_neg_mul_sinc_Ioi_le ha hB
  have hinv : 1 / (r ^ (-1 : Int)) = r := by
    rw [zpow_neg_one]
    field_simp
  rw [htotal, hinv] at hsplit
  change abs ((∫ u : Real in 0..B,
    Real.exp (-(r ^ (-1 : Int)) * u) * Real.sinc u) - Real.arctan r) <= 2 / B
  calc
    abs ((∫ u : Real in 0..B,
        Real.exp (-(r ^ (-1 : Int)) * u) * Real.sinc u) - Real.arctan r) =
        abs (-(∫ u : Real in Ioi B,
          Real.exp (-(r ^ (-1 : Int)) * u) * Real.sinc u)) := by
      rw [hsplit]
      congr 1
      ring
    _ = abs (∫ u : Real in Ioi B,
        Real.exp (-(r ^ (-1 : Int)) * u) * Real.sinc u) := abs_neg _
    _ <= 2 / B := htail

/-- The finite Dirichlet sine integral converges to `pi/2`. -/
theorem tendsto_dirichletSineIntegral :
    Tendsto (fun A : Real => ∫ u : Real in 0..A, Real.sinc u) atTop
      (nhds (Real.pi / 2)) := by
  have hnorm : Tendsto (fun A : Real =>
      ‖(∫ u : Real in 0..A, Real.sinc u) - Real.pi / 2‖) atTop (nhds 0) := by
    apply squeeze_zero' (g := fun A : Real => 2 / A)
    · exact Filter.Eventually.of_forall fun _ => norm_nonneg _
    · filter_upwards [eventually_gt_atTop 0] with A hA
      rw [Real.norm_eq_abs]
      exact abs_dirichletSineIntegral_sub_pi_div_two_le_two_div hA
    · simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul (2 : Real)
  have hdiff : Tendsto (fun A : Real =>
      (∫ u : Real in 0..A, Real.sinc u) - Real.pi / 2) atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  convert hdiff.add_const (Real.pi / 2) using 1 <;> simp

end PrimesRestrictedDigits
