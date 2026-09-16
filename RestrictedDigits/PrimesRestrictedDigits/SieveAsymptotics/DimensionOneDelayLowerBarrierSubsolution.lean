import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneDelayLowerBarrierCalculus

/-!
# Unit-window subsolution for the explicit lower delay barrier

This evaluates the exponential comparison integral by interval FTC.
-/

open MeasureTheory Set

noncomputable section

namespace PrimesRestrictedDigits

theorem dimensionOneDelayAuxiliary_slope_exp_gap
    {s : Real} (hs : Real.exp 5000 + 1 <= s) :
    0 < Real.log s + Real.log (Real.log s) +
        (3 / 2 : Real) * Real.log (Real.log s) / Real.log s ∧
      1 + s * (Real.log s + Real.log (Real.log s) +
        (3 / 2 : Real) * Real.log (Real.log s) / Real.log s) <
        Real.exp (Real.log s + Real.log (Real.log s) +
          (3 / 2 : Real) * Real.log (Real.log s) / Real.log s) := by
  have hs0 : 0 < s := by linarith [Real.exp_pos (5000 : Real)]
  have hsLog : 5000 < Real.log s :=
    (Real.lt_log_iff_exp_lt hs0).2 (by linarith)
  have hsLogPos : 0 < Real.log s := by linarith
  have hmPos : 0 < Real.log (Real.log s) := by
    apply Real.log_pos
    linarith [hsLog]
  have hmOne : 1 < Real.log (Real.log s) := by
    apply (Real.lt_log_iff_exp_lt (by positivity)).2
    have hthree : (3 : Real) < Real.log s := by linarith [hsLog]
    exact Real.exp_one_lt_three.trans hthree
  have hqPos : 0 < Real.log s + Real.log (Real.log s) +
      (3 / 2 : Real) * Real.log (Real.log s) / Real.log s := by
    positivity
  have hExpDecomp :
      Real.exp (Real.log s + Real.log (Real.log s) +
        (3 / 2 : Real) * Real.log (Real.log s) / Real.log s) =
        s * Real.log s *
          Real.exp ((3 / 2 : Real) * Real.log (Real.log s) /
            Real.log s) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_log hs0,
      Real.exp_log hsLogPos]
  have hExpLower : s * (Real.log s +
      (3 / 2 : Real) * Real.log (Real.log s)) <=
      Real.exp (Real.log s + Real.log (Real.log s) +
        (3 / 2 : Real) * Real.log (Real.log s) / Real.log s) := by
    rw [hExpDecomp]
    have h := Real.add_one_le_exp
      ((3 / 2 : Real) * Real.log (Real.log s) / Real.log s)
    calc
      s * (Real.log s +
          (3 / 2 : Real) * Real.log (Real.log s)) =
          (s * Real.log s) *
            (1 + (3 / 2 : Real) * Real.log (Real.log s) /
              Real.log s) := by field_simp [hsLogPos.ne']
      _ <= (s * Real.log s) *
          Real.exp ((3 / 2 : Real) * Real.log (Real.log s) /
            Real.log s) :=
        mul_le_mul_of_nonneg_left (by simpa [add_comm] using h) (by positivity)
  have hfrac : (1 / 4 : Real) <
      (Real.log s - 3) / (2 * Real.log s) := by
    apply (lt_div_iff₀ (show 0 < 2 * Real.log s by positivity)).2
    nlinarith [hsLog]
  have hratioPos : 0 < (Real.log s - 3) / (2 * Real.log s) :=
    lt_trans (by norm_num) hfrac
  have hdelta : (1 / 4 : Real) <
      Real.log (Real.log s) / 2 -
        (3 / 2 : Real) * Real.log (Real.log s) / Real.log s := by
    have hmul := mul_lt_mul_of_pos_right hmOne hratioPos
    have hident : Real.log (Real.log s) / 2 -
        (3 / 2 : Real) * Real.log (Real.log s) / Real.log s =
        Real.log (Real.log s) *
          (Real.log s - 3) / (2 * Real.log s) := by
      field_simp [hsLogPos.ne']
    rw [hident]
    exact hfrac.trans (by convert hmul using 1 <;> ring)
  have hs4 : 4 < s := by
    have h := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
    linarith
  have hprod : 1 < s *
      (Real.log (Real.log s) / 2 -
        (3 / 2 : Real) * Real.log (Real.log s) / Real.log s) := by
    have h1 : 1 < 4 *
        (Real.log (Real.log s) / 2 -
          (3 / 2 : Real) * Real.log (Real.log s) / Real.log s) := by
      nlinarith [hdelta]
    have h2 := mul_lt_mul_of_pos_right hs4 (by
      have : 0 < Real.log (Real.log s) / 2 -
          (3 / 2 : Real) * Real.log (Real.log s) / Real.log s :=
        lt_trans (by norm_num) hdelta
      exact this)
    exact h1.trans h2
  constructor
  · exact hqPos
  · calc
      1 + s * (Real.log s + Real.log (Real.log s) +
          (3 / 2 : Real) * Real.log (Real.log s) / Real.log s) <
          s * (Real.log s +
            (3 / 2 : Real) * Real.log (Real.log s)) := by
        nlinarith [hprod]
      _ <= Real.exp (Real.log s + Real.log (Real.log s) +
          (3 / 2 : Real) * Real.log (Real.log s) / Real.log s) := hExpLower

private theorem dimensionOneDelayAuxiliary_exp_integral
    {s : Real} (hs : Real.exp 5000 + 1 <= s) :
    ∫ x in s - 1..s,
        Real.exp ((Real.log s + Real.log (Real.log s) +
          (3 / 2 : Real) * Real.log (Real.log s) / Real.log s) *
          (s - x)) =
      (Real.exp (Real.log s + Real.log (Real.log s) +
        (3 / 2 : Real) * Real.log (Real.log s) / Real.log s) - 1) /
        (Real.log s + Real.log (Real.log s) +
          (3 / 2 : Real) * Real.log (Real.log s) / Real.log s) := by
  let q : Real := Real.log s + Real.log (Real.log s) +
    (3 / 2 : Real) * Real.log (Real.log s) / Real.log s
  have hq : 0 < q := by
    dsimp [q]
    exact (dimensionOneDelayAuxiliary_slope_exp_gap hs).1
  have hsMinus : 0 < s - 1 := by linarith [Real.exp_pos (5000 : Real)]
  have hInterval : s - 1 <= s := by linarith
  let arg : Real -> Real :=
    (fun _ : Real => q) * ((fun _ : Real => s) - id)
  let f : Real -> Real := Real.exp ∘ arg
  let P : Real -> Real := (fun _ : Real => -(1 / q)) * f
  have hfCont : ContinuousOn f (Icc (s - 1) s) := by
    dsimp [f, arg]
    exact Real.continuous_exp.comp_continuousOn
      ((continuousOn_const.mul (continuousOn_const.sub continuousOn_id)))
  have hfi : IntervalIntegrable f volume (s - 1) s :=
    hfCont.intervalIntegrable_of_Icc hInterval
  have hPCont : ContinuousOn P (Icc (s - 1) s) := by
    dsimp [P]
    exact continuousOn_const.mul hfCont
  have hPDeriv : ∀ x ∈ Ioo (s - 1) s,
      HasDerivAt P (f x) x := by
    intro x hx
    have harg := (hasDerivAt_const x q).mul
      ((hasDerivAt_const x s).sub (hasDerivAt_id x))
    have hexp := (Real.hasDerivAt_exp (q * (s - x))).comp x harg
    have hP := (hasDerivAt_const x (-1 / q)).mul hexp
    have hP' : HasDerivAt ((fun _ : Real => -1 / q) * f) (f x) x := by
      apply hP.congr_deriv
      dsimp [f, arg]
      field_simp [hq.ne']
      ring_nf
    simpa [P, div_eq_mul_inv] using hP'
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hInterval hPCont hPDeriv hfi
  have hEval : ∫ x in s - 1..s, f x =
      (Real.exp q - 1) / q := by
    rw [hFTC]
    dsimp [P, f, arg]
    have hsExp : Real.exp (q * (s - s)) = 1 := by ring_nf; simp
    have hsmExp : Real.exp (q * (s - (s - 1))) = Real.exp q := by
      congr 1
      ring
    rw [hsExp, hsmExp]
    field_simp [hq.ne']
    ring
  dsimp [f, arg, q] at hEval
  exact hEval

theorem dimensionOneDelayAuxiliaryLowerScale_unit_subsolution
    {s : Real} (hs : Real.exp 5000 + 1 <= s) :
    s * dimensionOneDelayAuxiliaryLowerScale s <
      ∫ x in s - 1..s, dimensionOneDelayAuxiliaryLowerScale x := by
  have hsMinus : 0 < s - 1 := by linarith [Real.exp_pos (5000 : Real)]
  have hInterval : s - 1 <= s := by linarith
  have hExpOne : 1 < Real.exp (5000 : Real) := by
    have h := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
    linarith
  have hCarrier : Icc (s - 1) s ⊆ Ioi (1 : Real) := by
    intro t ht
    change 1 < t
    exact by linarith [ht.1, hs, hExpOne]
  have hBCont : ContinuousOn dimensionOneDelayAuxiliaryLowerScale
      (Icc (s - 1) s) :=
    dimensionOneDelayAuxiliaryLowerScale_continuousOn.mono hCarrier
  have hBInt : IntervalIntegrable dimensionOneDelayAuxiliaryLowerScale
      volume (s - 1) s := hBCont.intervalIntegrable_of_Icc hInterval
  let q : Real := Real.log s + Real.log (Real.log s) +
    (3 / 2 : Real) * Real.log (Real.log s) / Real.log s
  have hq : 0 < q := by
    dsimp [q]
    exact (dimensionOneDelayAuxiliary_slope_exp_gap hs).1
  have hPointwise : ∀ x ∈ Icc (s - 1) s,
      dimensionOneDelayAuxiliaryLowerScale s *
          Real.exp (q * (s - x)) <=
        dimensionOneDelayAuxiliaryLowerScale x := by
    intro x hx
    have hSlope := dimensionOneDelayAuxiliaryExponent_window_slope hs hx
    have hExp : -dimensionOneDelayAuxiliaryExponent s + q * (s - x) <=
        -dimensionOneDelayAuxiliaryExponent x := by
      dsimp [q] at hSlope ⊢
      linarith
    unfold dimensionOneDelayAuxiliaryLowerScale
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr hExp
  let f : Real -> Real := fun x =>
    dimensionOneDelayAuxiliaryLowerScale s * Real.exp (q * (s - x))
  have hfCont : ContinuousOn f (Icc (s - 1) s) := by
    dsimp [f]
    exact continuousOn_const.mul
      (Real.continuous_exp.comp_continuousOn
        (continuousOn_const.mul (continuousOn_const.sub continuousOn_id)))
  have hfi : IntervalIntegrable f volume (s - 1) s :=
    hfCont.intervalIntegrable_of_Icc hInterval
  have hIntegral := intervalIntegral.integral_mono_on hInterval hfi hBInt
    (by intro x hx; exact hPointwise x hx)
  have hExpIntegral := dimensionOneDelayAuxiliary_exp_integral hs
  have hScaled : dimensionOneDelayAuxiliaryLowerScale s *
      ((Real.exp q - 1) / q) <=
      ∫ x in s - 1..s, dimensionOneDelayAuxiliaryLowerScale x := by
    calc
      dimensionOneDelayAuxiliaryLowerScale s * ((Real.exp q - 1) / q) =
          ∫ x in s - 1..s, f x := by
        dsimp [f]
        rw [intervalIntegral.integral_const_mul, hExpIntegral]
      _ <= _ := hIntegral
  have hGap := dimensionOneDelayAuxiliary_slope_exp_gap hs
  have hRatio : s < (Real.exp q - 1) / q := by
    apply (lt_div_iff₀ hq).2
    linarith [hGap.2]
  have hStrict := mul_lt_mul_of_pos_left hRatio
    (dimensionOneDelayAuxiliaryLowerScale_pos s)
  calc
    s * dimensionOneDelayAuxiliaryLowerScale s <
        dimensionOneDelayAuxiliaryLowerScale s * ((Real.exp q - 1) / q) := by
      simpa [mul_comm] using hStrict
    _ <= _ := hScaled

end PrimesRestrictedDigits
