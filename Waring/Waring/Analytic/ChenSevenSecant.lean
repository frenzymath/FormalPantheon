import Waring.Analytic.ChenSevenRightQuadrature
import Mathlib.Analysis.Convex.Deriv

/-!
# Secant-phase estimates for Chen's Lemma 7

This file bounds the error made by replacing a convex phase by its secant on
unit intervals and evaluates the resulting linear-phase integrals.
-/

namespace Waring.Analytic

open MeasureTheory Set
open scoped Interval

/-- The vertical gap from the secant line of `theta` on `[a,b]` to `theta`. -/
noncomputable def secantGap (theta : Real → Real) (a b x : Real) : Real :=
  theta a + (x - a) * ((theta b - theta a) / (b - a)) - theta x

/-- A convex graph lies below each of its secants. -/
theorem secantGap_nonneg_of_convexOn
    {theta : Real → Real} {a b : Real} (hab : a < b)
    (hconv : ConvexOn Real (Icc a b) theta) :
    ∀ x ∈ Icc a b, 0 ≤ secantGap theta a b x := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with rfl | hax
  · simp [secantGap]
  rcases eq_or_lt_of_le hx.2 with rfl | hxb
  · unfold secantGap
    field_simp [sub_ne_zero.mpr hax.ne']
    linarith
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hb : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  have key := hconv.secant_mono_aux1 ha hb hax hxb
  have hden : 0 < b - a := sub_pos.mpr hab
  unfold secantGap
  have hrewrite :
      theta a + (x - a) * ((theta b - theta a) / (b - a)) =
        ((b - x) * theta a + (x - a) * theta b) / (b - a) := by
    field_simp
    ring
  rw [hrewrite]
  exact sub_nonneg.mpr ((le_div_iff₀ hden).2 (by nlinarith [key]))

/-- The secant gap is controlled by the endpoint derivative spread. -/
theorem secantGap_le_deriv_sub_of_convexOn
    {theta : Real → Real} (htheta : ContDiff Real 1 theta)
    {a b : Real} (hab : a < b) (hconv : ConvexOn Real (Icc a b) theta) :
    ∀ x ∈ Icc a b,
      secantGap theta a b x ≤
        (x - a) * (deriv theta b - deriv theta a) := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hb : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  have hmdb : (theta b - theta a) / (b - a) ≤ deriv theta b := by
    simpa only [slope_def_field] using hconv.slope_le_deriv ha hb hab
      (htheta.differentiable one_ne_zero b)
  intro x hx
  rcases eq_or_lt_of_le hx.1 with rfl | hax
  · simp [secantGap]
  have hdam : deriv theta a ≤ (theta x - theta a) / (x - a) := by
    simpa only [slope_def_field] using hconv.deriv_le_slope ha hx hax
      (htheta.differentiable one_ne_zero a)
  have htangent : (x - a) * deriv theta a ≤ theta x - theta a := by
    have h := (le_div_iff₀ (sub_pos.mpr hax)).1 hdam
    simpa only [mul_comm] using h
  have hsecant := mul_le_mul_of_nonneg_left hmdb (sub_nonneg.mpr hx.1)
  calc
    secantGap theta a b x =
        (x - a) * ((theta b - theta a) / (b - a)) -
          (theta x - theta a) := by
      unfold secantGap
      ring
    _ ≤ (x - a) * deriv theta b - (x - a) * deriv theta a :=
      sub_le_sub hsecant htangent
    _ = (x - a) * (deriv theta b - deriv theta a) := by ring

/-- The integral secant gap is at most a triangular derivative-spread
bound. -/
theorem integral_secantGap_bounds_of_convexOn
    {theta : Real → Real} (htheta : ContDiff Real 1 theta)
    {a b : Real} (hab : a < b) (hconv : ConvexOn Real (Icc a b) theta) :
    0 ≤ ∫ x in a..b, secantGap theta a b x ∧
      (∫ x in a..b, secantGap theta a b x) ≤
        (b - a) ^ 2 / 2 * (deriv theta b - deriv theta a) := by
  have hgapCont : Continuous (secantGap theta a b) := by
    unfold secantGap
    fun_prop
  have hboundCont :
      Continuous (fun x => (x - a) * (deriv theta b - deriv theta a)) := by
    fun_prop
  have hgapInt : IntervalIntegrable (secantGap theta a b) volume a b :=
    hgapCont.intervalIntegrable a b
  have hboundInt : IntervalIntegrable
      (fun x => (x - a) * (deriv theta b - deriv theta a)) volume a b :=
    hboundCont.intervalIntegrable a b
  constructor
  · exact intervalIntegral.integral_nonneg hab.le
      (secantGap_nonneg_of_convexOn hab hconv)
  · calc
      (∫ x in a..b, secantGap theta a b x) ≤
          ∫ x in a..b, (x - a) * (deriv theta b - deriv theta a) :=
        intervalIntegral.integral_mono_on hab.le hgapInt hboundInt
          (secantGap_le_deriv_sub_of_convexOn htheta hab hconv)
      _ = (b - a) ^ 2 / 2 * (deriv theta b - deriv theta a) := by
        rw [intervalIntegral.integral_mul_const]
        have hsub :
            (∫ x in a..b, x - a) =
              (∫ x in a..b, x) - ∫ _ in a..b, a := by
          simpa only [Pi.sub_apply] using intervalIntegral.integral_sub
            (f := fun x : Real => x) (g := fun _ : Real => a)
            (continuous_id.intervalIntegrable a b)
            (continuous_const.intervalIntegrable a b)
        rw [hsub, integral_id, intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring

/-- A monotone derivative supplies the convexity used in the secant bound. -/
theorem integral_secantGap_bounds_of_monotoneOn_deriv
    {theta : Real → Real} (htheta : ContDiff Real 1 theta)
    {a b : Real} (hab : a < b)
    (hmono : MonotoneOn (deriv theta) (Icc a b)) :
    0 ≤ ∫ x in a..b, secantGap theta a b x ∧
      (∫ x in a..b, secantGap theta a b x) ≤
        (b - a) ^ 2 / 2 * (deriv theta b - deriv theta a) := by
  apply integral_secantGap_bounds_of_convexOn htheta hab
  apply (hmono.mono interior_subset).convexOn_of_deriv (convex_Icc a b)
  · exact htheta.continuous.continuousOn
  · exact (htheta.differentiable one_ne_zero).differentiableOn

/-- Unit-interval specialization of the integral secant-gap bound. -/
theorem integral_unit_secantGap_bounds_of_monotoneOn_deriv
    {theta : Real → Real} (htheta : ContDiff Real 1 theta) (a : Real)
    (hmono : MonotoneOn (deriv theta) (Icc a (a + 1))) :
    0 ≤ ∫ x in a..a + 1,
        theta a + (x - a) * (theta (a + 1) - theta a) - theta x ∧
      (∫ x in a..a + 1,
        theta a + (x - a) * (theta (a + 1) - theta a) - theta x) ≤
          (deriv theta (a + 1) - deriv theta a) / 2 := by
  simpa [secantGap, div_eq_mul_inv, mul_assoc, mul_comm] using
    integral_secantGap_bounds_of_monotoneOn_deriv htheta
      (a := a) (b := a + 1) (by linarith) hmono

/-- The integral of a nonconstant linear phase over a unit interval. -/
theorem integral_exp_secant (a theta delta : Real) (hdelta : 0 < delta) :
    (∫ x in a..a + 1,
      Complex.exp (Complex.I *
        ((theta + (x - a) * delta : Real) : Complex))) =
      (Complex.I * (delta : Complex))⁻¹ *
        (Complex.exp (Complex.I * ((theta + delta : Real) : Complex)) -
          Complex.exp (Complex.I * (theta : Complex))) := by
  have hdeltaC : (delta : Complex) ≠ 0 := by exact_mod_cast hdelta.ne'
  let F : Real → Complex := fun x =>
    (Complex.I * (delta : Complex))⁻¹ *
      Complex.exp (Complex.I *
        ((theta + (x - a) * delta : Real) : Complex))
  have hderiv (x : Real) : HasDerivAt F
      (Complex.exp (Complex.I *
        ((theta + (x - a) * delta : Real) : Complex))) x := by
    have hr : HasDerivAt
        (fun y : Real => theta + (y - a) * delta) delta x := by
      simpa using
        (((hasDerivAt_id x).sub_const a).mul_const delta).const_add theta
    have hc0 := Complex.ofRealCLM.hasFDerivAt.comp x hr.hasFDerivAt
    have hc : HasDerivAt
        (fun y : Real => ((theta + (y - a) * delta : Real) : Complex))
        (delta : Complex) x := by
      simpa [Function.comp_def, Complex.ofRealCLM_apply] using hc0.hasDerivAt
    have harg := hc.const_mul Complex.I
    have hexp := harg.cexp
    apply ((hexp.const_mul
      (Complex.I * (delta : Complex))⁻¹)).congr_deriv
    field_simp
  have hint : IntervalIntegrable
      (fun x : Real => Complex.exp (Complex.I *
        ((theta + (x - a) * delta : Real) : Complex))) volume a (a + 1) := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hderiv x) hint]
  simp only [F]
  push_cast
  ring_nf

/-- A phase in `(0,pi]` does not return to one after one increment. -/
theorem exp_I_mul_sub_one_ne_zero
    {delta : Real} (hdelta : 0 < delta) (hdeltapi : delta ≤ Real.pi) :
    Complex.exp (Complex.I * (delta : Complex)) - 1 ≠ 0 := by
  have hcoslt : Real.cos delta < 1 := by
    have hanti := Real.strictAntiOn_cos
      (show (0 : Real) ∈ Icc 0 Real.pi from ⟨le_rfl, Real.pi_pos.le⟩)
      (show delta ∈ Icc 0 Real.pi from ⟨hdelta.le, hdeltapi⟩) hdelta
    simpa using hanti
  intro hzero
  have heq : Complex.exp (Complex.I * (delta : Complex)) = 1 :=
    sub_eq_zero.mp hzero
  have hre := congrArg Complex.re heq
  have hexp :
      Complex.exp (Complex.I * (delta : Complex)) =
        (Real.cos delta : Complex) +
          Complex.I * (Real.sin delta : Complex) := by
    rw [mul_comm, Complex.exp_mul_I]
    push_cast
    ring
  rw [hexp] at hre
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.one_re] at hre
  norm_num at hre
  linarith

/-- A left endpoint sample minus its secant-phase integral is the correction
coefficient times the successive exponential difference. -/
theorem exp_sub_integral_exp_secant_eq_phaseCorrection_mul
    (a theta delta : Real) (hdelta : 0 < delta)
    (hdeltapi : delta ≤ Real.pi) :
    Complex.exp (Complex.I * (theta : Complex)) -
        (∫ x in a..a + 1,
          Complex.exp (Complex.I *
            ((theta + (x - a) * delta : Real) : Complex))) =
      phaseCorrection delta *
        (Complex.exp (Complex.I * ((theta + delta : Real) : Complex)) -
          Complex.exp (Complex.I * (theta : Complex))) := by
  rw [integral_exp_secant a theta delta hdelta]
  have hdeltaC : (delta : Complex) ≠ 0 := by exact_mod_cast hdelta.ne'
  have hIC : Complex.I * (delta : Complex) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero hdeltaC
  have hA := exp_I_mul_sub_one_ne_zero hdelta hdeltapi
  have hdiff :
      Complex.exp (Complex.I * ((theta + delta : Real) : Complex)) -
          Complex.exp (Complex.I * (theta : Complex)) =
        Complex.exp (Complex.I * (theta : Complex)) *
          (Complex.exp (Complex.I * (delta : Complex)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hdiff, phaseCorrection_eq_inv_sub hdelta hdeltapi]
  field_simp

/-- The analogous exact identity for the right endpoint sample. -/
theorem exp_right_sub_integral_exp_secant_eq_rightPhaseCorrection_mul
    (a theta delta : Real) (hdelta : 0 < delta)
    (hdeltapi : delta ≤ Real.pi) :
    Complex.exp (Complex.I * ((theta + delta : Real) : Complex)) -
        (∫ x in a..a + 1,
          Complex.exp (Complex.I *
            ((theta + (x - a) * delta : Real) : Complex))) =
      rightPhaseCorrection delta *
        (Complex.exp (Complex.I * ((theta + delta : Real) : Complex)) -
          Complex.exp (Complex.I * (theta : Complex))) := by
  have hleft := exp_sub_integral_exp_secant_eq_phaseCorrection_mul
    a theta delta hdelta hdeltapi
  rw [rightPhaseCorrection_eq_phaseCorrection_add_one]
  calc
    Complex.exp (Complex.I * ((theta + delta : Real) : Complex)) -
          (∫ x in a..a + 1,
            Complex.exp (Complex.I *
              ((theta + (x - a) * delta : Real) : Complex))) =
        (Complex.exp (Complex.I * (theta : Complex)) -
            (∫ x in a..a + 1,
              Complex.exp (Complex.I *
                ((theta + (x - a) * delta : Real) : Complex)))) +
          (Complex.exp (Complex.I * ((theta + delta : Real) : Complex)) -
            Complex.exp (Complex.I * (theta : Complex))) := by ring
    _ = phaseCorrection delta *
          (Complex.exp (Complex.I * ((theta + delta : Real) : Complex)) -
            Complex.exp (Complex.I * (theta : Complex))) +
        (Complex.exp (Complex.I * ((theta + delta : Real) : Complex)) -
          Complex.exp (Complex.I * (theta : Complex))) := by rw [hleft]
    _ = (phaseCorrection delta + 1) *
        (Complex.exp (Complex.I * ((theta + delta : Real) : Complex)) -
          Complex.exp (Complex.I * (theta : Complex))) := by ring

/-- Replacing a convex phase by its secant on one unit interval costs at most
half the derivative increase on that interval. -/
theorem norm_integral_exp_secant_sub_exp_le
    {theta : Real → Real} (htheta : ContDiff Real 1 theta) (a : Real)
    (hmono : MonotoneOn (deriv theta) (Icc a (a + 1))) :
    ‖(∫ x in a..a + 1,
        Complex.exp (Complex.I *
          ((theta a + (x - a) * (theta (a + 1) - theta a) : Real) :
            Complex))) -
      (∫ x in a..a + 1,
        Complex.exp (Complex.I * (theta x : Complex)))‖ ≤
      (deriv theta (a + 1) - deriv theta a) / 2 := by
  let gap : Real → Real := fun x =>
    theta a + (x - a) * (theta (a + 1) - theta a) - theta x
  have hconv : ConvexOn Real (Icc a (a + 1)) theta := by
    apply (hmono.mono interior_subset).convexOn_of_deriv
      (convex_Icc a (a + 1))
    · exact htheta.continuous.continuousOn
    · exact (htheta.differentiable one_ne_zero).differentiableOn
  have hgapNonneg : ∀ x ∈ Icc a (a + 1), 0 ≤ gap x := by
    intro x hx
    simpa [gap, secantGap] using
      secantGap_nonneg_of_convexOn (theta := theta) (by linarith) hconv x hx
  have hgapBounds := integral_unit_secantGap_bounds_of_monotoneOn_deriv
    htheta a hmono
  have hsecInt : IntervalIntegrable
      (fun x : Real => Complex.exp (Complex.I *
        ((theta a + (x - a) * (theta (a + 1) - theta a) : Real) :
          Complex))) volume a (a + 1) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hthetaInt : IntervalIntegrable
      (fun x : Real => Complex.exp (Complex.I * (theta x : Complex)))
      volume a (a + 1) := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [← intervalIntegral.integral_sub hsecInt hthetaInt]
  calc
    ‖∫ x in a..a + 1,
        (Complex.exp (Complex.I *
          ((theta a + (x - a) * (theta (a + 1) - theta a) : Real) :
            Complex)) -
          Complex.exp (Complex.I * (theta x : Complex)))‖ ≤
        ∫ x in a..a + 1,
          ‖Complex.exp (Complex.I *
              ((theta a + (x - a) * (theta (a + 1) - theta a) : Real) :
                Complex)) -
            Complex.exp (Complex.I * (theta x : Complex))‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by linarith)
    _ ≤ ∫ x in a..a + 1, gap x := by
      apply intervalIntegral.integral_mono_on (by linarith)
      · apply Continuous.intervalIntegrable
        fun_prop
      · apply Continuous.intervalIntegrable
        dsimp [gap]
        fun_prop
      · intro x hx
        calc
          ‖Complex.exp (Complex.I *
                ((theta a + (x - a) * (theta (a + 1) - theta a) : Real) :
                  Complex)) -
              Complex.exp (Complex.I * (theta x : Complex))‖ ≤
              |(theta a + (x - a) * (theta (a + 1) - theta a)) - theta x| :=
            norm_exp_I_mul_sub_exp_I_mul_le _ _
          _ = gap x := by rw [abs_of_nonneg (hgapNonneg x hx)]
    _ ≤ (deriv theta (a + 1) - deriv theta a) / 2 := by
      simpa [gap] using hgapBounds.2

/-- The total secant replacement error over consecutive unit intervals is at
most two when the derivative spread is at most `pi`. -/
theorem norm_sum_integral_exp_secant_sub_integral_le_two
    {theta : Real → Real} (htheta : ContDiff Real 1 theta) (n : Nat)
    (hmono : MonotoneOn (deriv theta) (Icc 0 n))
    (hspread : deriv theta n - deriv theta 0 ≤ Real.pi) :
    ‖(∑ i ∈ Finset.range n,
        ∫ x in (i : Real)..(i : Real) + 1,
          Complex.exp (Complex.I *
            ((theta i + (x - i) * (theta (i + 1) - theta i) : Real) :
              Complex))) -
      (∫ x in (0 : Real)..n,
        Complex.exp (Complex.I * (theta x : Complex)))‖ ≤ 2 := by
  have hthetaCont : Continuous
      (fun x : Real => Complex.exp (Complex.I * (theta x : Complex))) := by
    fun_prop
  have htrueSum :
      (∑ i ∈ Finset.range n,
        ∫ x in (i : Real)..(i : Real) + 1,
          Complex.exp (Complex.I * (theta x : Complex))) =
        ∫ x in (0 : Real)..n,
          Complex.exp (Complex.I * (theta x : Complex)) := by
    simpa only [Nat.cast_zero, Nat.cast_add, Nat.cast_one] using
      intervalIntegral.sum_integral_adjacent_intervals
        (a := fun i : Nat => (i : Real)) (n := n)
        (fun i _ => by
          simpa only [Nat.cast_add, Nat.cast_one] using
            hthetaCont.intervalIntegrable (i : Real) ((i : Real) + 1))
  rw [← htrueSum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        ‖(∫ x in (i : Real)..(i : Real) + 1,
            Complex.exp (Complex.I *
              ((theta i + (x - i) * (theta (i + 1) - theta i) : Real) :
                Complex))) -
          (∫ x in (i : Real)..(i : Real) + 1,
            Complex.exp (Complex.I * (theta x : Complex)))‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range n,
        (deriv theta ((i : Real) + 1) - deriv theta i) / 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hiNat : i < n := Finset.mem_range.mp hi
      apply norm_integral_exp_secant_sub_exp_le htheta i
      apply hmono.mono
      intro x hx
      constructor
      · exact (Nat.cast_nonneg i).trans hx.1
      · have hiCast : ((i + 1 : Nat) : Real) ≤ n := by
          exact_mod_cast Nat.succ_le_of_lt hiNat
        norm_num at hiCast ⊢
        exact hx.2.trans hiCast
    _ = (deriv theta n - deriv theta 0) / 2 := by
      rw [← Finset.sum_div]
      have htel := Finset.sum_range_sub
        (fun i : Nat => deriv theta (i : Real)) n
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] using
        congrArg (fun x : Real => x / 2) htel
    _ ≤ Real.pi / 2 := by linarith
    _ ≤ 2 := by linarith [Real.pi_lt_four]

/-- Right endpoint samples of a convex slow phase differ from its integral by
at most four on an integer interval. -/
theorem norm_sum_range_exp_right_sub_integral_le_four
    {theta : Real → Real} (htheta : ContDiff Real 1 theta) (n : Nat)
    (hpos : ∀ i, i < n → 0 < theta (i + 1) - theta i)
    (hpi : ∀ i, i < n → theta (i + 1) - theta i ≤ Real.pi)
    (hinc : ∀ i, i + 1 < n →
      theta (i + 1) - theta i ≤ theta (i + 2) - theta (i + 1))
    (hmono : MonotoneOn (deriv theta) (Icc 0 n))
    (hspread : deriv theta n - deriv theta 0 ≤ Real.pi) :
    ‖(∑ i ∈ Finset.range n,
        Complex.exp (Complex.I * (theta (i + 1) : Complex))) -
      (∫ x in (0 : Real)..n,
        Complex.exp (Complex.I * (theta x : Complex)))‖ ≤ 4 := by
  let delta : Nat → Real := fun i => theta (i + 1) - theta i
  let secants : Complex := ∑ i ∈ Finset.range n,
    ∫ x in (i : Real)..(i : Real) + 1,
      Complex.exp (Complex.I *
        ((theta i + (x - i) * delta i : Real) : Complex))
  have hsamples :
      ‖(∑ i ∈ Finset.range n,
          Complex.exp (Complex.I * (theta (i + 1) : Complex))) - secants‖ ≤ 2 := by
    rw [show (∑ i ∈ Finset.range n,
        Complex.exp (Complex.I * (theta (i + 1) : Complex))) - secants =
      ∑ i ∈ Finset.range n,
        rightPhaseCorrection (delta i) *
          (Complex.exp (Complex.I * (theta (i + 1) : Complex)) -
            Complex.exp (Complex.I * (theta i : Complex))) by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      have hiNat : i < n := Finset.mem_range.mp hi
      simpa [secants, delta] using
        exp_right_sub_integral_exp_secant_eq_rightPhaseCorrection_mul
          (i : Real) (theta i) (delta i)
            (by simpa [delta] using hpos i hiNat)
            (by simpa [delta] using hpi i hiNat)]
    have hcorr := norm_sum_rightPhaseCorrection_mul_exp_sub_le_two
      (fun i : Nat => theta i) delta n
      (fun i hi => by simpa [delta] using hpos i hi)
      (fun i hi => by simpa [delta] using hpi i hi)
      (fun i hi => by
        dsimp [delta]
        norm_num
        have hreal : (i : Real) + 1 + 1 = (i : Real) + 2 := by ring
        rw [hreal]
        linarith [hinc i hi])
    simpa only [Nat.cast_add, Nat.cast_one] using hcorr
  have hsecants :
      ‖secants - ∫ x in (0 : Real)..n,
        Complex.exp (Complex.I * (theta x : Complex))‖ ≤ 2 := by
    simpa [secants, delta] using
      norm_sum_integral_exp_secant_sub_integral_le_two
        htheta n hmono hspread
  rw [show (∑ i ∈ Finset.range n,
      Complex.exp (Complex.I * (theta (i + 1) : Complex))) -
        (∫ x in (0 : Real)..n,
          Complex.exp (Complex.I * (theta x : Complex))) =
      ((∑ i ∈ Finset.range n,
        Complex.exp (Complex.I * (theta (i + 1) : Complex))) - secants) +
        (secants - ∫ x in (0 : Real)..n,
          Complex.exp (Complex.I * (theta x : Complex))) by ring]
  exact (norm_add_le _ _).trans (by linarith)

end Waring.Analytic
