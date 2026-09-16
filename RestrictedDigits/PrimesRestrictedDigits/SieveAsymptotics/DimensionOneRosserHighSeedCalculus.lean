import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserHighSeedScalars
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Calculus for the independent high-rank Rosser seed

This file proves the derivative reserves, unit shift, and shifted integral bound for the
elementary seed envelope.
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

private theorem dimensionOneRosserSeedExponent_hasDerivAt
    {t : Real} (ht : 1 < t) :
    HasDerivAt
      (fun u : Real => u * (4 - Real.log (dimensionOneRosserSeedTilt u)))
      (3 - Real.log (dimensionOneRosserSeedTilt t) +
        1 / Real.log t) t := by
  have htPos : 0 < t := by linarith
  have htNe : t ≠ 0 := htPos.ne'
  have hlogPos : 0 < Real.log t := Real.log_pos ht
  have hlogNe : Real.log t ≠ 0 := hlogPos.ne'
  have hdenNe : 1024 * Real.log t ≠ 0 :=
    mul_ne_zero (by norm_num) hlogNe
  have htiltNe : dimensionOneRosserSeedTilt t ≠ 0 := by
    rw [dimensionOneRosserSeedTilt]
    exact div_ne_zero htNe hdenNe
  have hden : HasDerivAt (fun u : Real => 1024 * Real.log u)
      (1024 * t⁻¹) t := by
    simpa only [smul_eq_mul] using
      (Real.hasDerivAt_log htNe).const_mul 1024
  have hid : HasDerivAt (fun u : Real => u) 1 t := hasDerivAt_id t
  have htilt : HasDerivAt dimensionOneRosserSeedTilt
      ((1 * (1024 * Real.log t) - t * (1024 * t⁻¹)) /
        (1024 * Real.log t) ^ 2) t := by
    unfold dimensionOneRosserSeedTilt
    exact hid.div hden hdenNe
  have hlogTilt := htilt.log htiltNe
  have hexponentRaw := hid.mul
    ((hasDerivAt_const t 4).sub hlogTilt)
  change HasDerivAt
      (fun u : Real => u * (4 - Real.log (dimensionOneRosserSeedTilt u)))
      _ t at hexponentRaw
  simp only [Pi.sub_apply,  one_mul, zero_sub] at hexponentRaw
  apply hexponentRaw.congr_deriv
  unfold dimensionOneRosserSeedTilt
  field_simp [htNe, hlogNe]
  ring

/-- Exact derivative of the independent seed envelope on its positive
logarithmic domain. -/
theorem dimensionOneRosserSeedEnvelope_hasDerivAt
    {t : Real} (ht : 1 < t) :
    HasDerivAt dimensionOneRosserSeedEnvelope
      (dimensionOneRosserSeedEnvelope t *
        (3 - Real.log (dimensionOneRosserSeedTilt t) +
          1 / Real.log t)) t := by
  unfold dimensionOneRosserSeedEnvelope
  exact (dimensionOneRosserSeedExponent_hasDerivAt ht).exp

/-- The independent seed envelope is continuous above one. -/
theorem dimensionOneRosserSeedEnvelope_continuousOn :
    ContinuousOn dimensionOneRosserSeedEnvelope (Set.Ioi 1) := by
  intro t ht
  exact (dimensionOneRosserSeedEnvelope_hasDerivAt
    ht).continuousAt.continuousWithinAt

private theorem dimensionOneRosserSeedEnvelope_log_tilt_bounds
    {t : Real} (ht : Real.exp 5000 <= t) :
    1477 <= Real.log (dimensionOneRosserSeedTilt t) /\
      Real.log (dimensionOneRosserSeedTilt t) <= Real.log t /\
      0 < Real.log t := by
  have htPos : 0 < t := (Real.exp_pos 5000).trans_le ht
  have hlogLower : 5000 <= Real.log t :=
    (Real.le_log_iff_exp_le htPos).2 ht
  have hlogPos : 0 < Real.log t := by linarith
  have htNe : t ≠ 0 := htPos.ne'
  have hlogNe : Real.log t ≠ 0 := hlogPos.ne'
  have hdenPos : 0 < 1024 * Real.log t :=
    mul_pos (by norm_num) hlogPos
  have hdenNe : 1024 * Real.log t ≠ 0 := hdenPos.ne'
  have hlogLogLe : Real.log (Real.log t) <=
      2 * Real.sqrt (Real.log t) := by
    have h := Real.log_le_rpow_div hlogPos.le
      (by norm_num : (0 : Real) < 1 / 2)
    rw [<- Real.sqrt_eq_rpow] at h
    norm_num at h
    linarith
  have hSqrtSq : Real.sqrt (Real.log t) ^ 2 = Real.log t :=
    Real.sq_sqrt hlogPos.le
  have hSqrtFour : 4 <= Real.sqrt (Real.log t) := by
    nlinarith [Real.sqrt_nonneg (Real.log t)]
  have hSqrtProduct :
      0 <= Real.sqrt (Real.log t) * (Real.sqrt (Real.log t) - 4) :=
    mul_nonneg (Real.sqrt_nonneg _) (by linarith)
  have hlogLogHalf : Real.log (Real.log t) <= Real.log t / 2 := by
    nlinarith
  have hlog1024 : Real.log (1024 : Real) <= 1023 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 1024)]
  have hlogTiltDiv : Real.log (dimensionOneRosserSeedTilt t) =
      Real.log t - Real.log (1024 * Real.log t) := by
    rw [dimensionOneRosserSeedTilt, Real.log_div htNe hdenNe]
  have hlogTiltExpanded : Real.log (dimensionOneRosserSeedTilt t) =
      Real.log t - Real.log 1024 - Real.log (Real.log t) := by
    rw [hlogTiltDiv, Real.log_mul (by norm_num) hlogNe]
    ring
  have hlogTiltLower :
      1477 <= Real.log (dimensionOneRosserSeedTilt t) := by
    rw [hlogTiltExpanded]
    linarith
  have hdenOne : (1 : Real) <= 1024 * Real.log t := by
    nlinarith
  have hlogTiltUpper :
      Real.log (dimensionOneRosserSeedTilt t) <= Real.log t := by
    rw [hlogTiltDiv]
    linarith [Real.log_nonneg hdenOne]
  exact ⟨hlogTiltLower, hlogTiltUpper, hlogPos⟩

/-- The derivative coefficient has a uniform negative reserve on the
inclusive large domain. -/
theorem dimensionOneRosserSeedEnvelope_derivCoefficient_le
    {t : Real} (ht : Real.exp 5000 <= t) :
    3 - Real.log (dimensionOneRosserSeedTilt t) +
      1 / Real.log t <= -8 := by
  obtain ⟨hlogTilt, _hlogTiltUpper, hlogPos⟩ :=
    dimensionOneRosserSeedEnvelope_log_tilt_bounds ht
  have hinv : 1 / Real.log t <= 1 := by
    rw [div_le_iff₀ hlogPos]
    nlinarith
  linarith

/-- The derivative coefficient is bounded below by the negative logarithm
on the inclusive large domain. -/
theorem neg_log_le_dimensionOneRosserSeedEnvelope_derivCoefficient
    {t : Real} (ht : Real.exp 5000 <= t) :
    -Real.log t <=
      3 - Real.log (dimensionOneRosserSeedTilt t) +
        1 / Real.log t := by
  obtain ⟨_hlogTiltLower, hlogTilt, hlogPos⟩ :=
    dimensionOneRosserSeedEnvelope_log_tilt_bounds ht
  have hinvPos : 0 < 1 / Real.log t := one_div_pos.mpr hlogPos
  linarith

private theorem dimensionOneRosserSeedEnvelope_deriv_continuousAt
    {t : Real} (ht : 1 < t) :
    ContinuousAt (fun u => dimensionOneRosserSeedEnvelope u *
      (3 - Real.log (dimensionOneRosserSeedTilt u) +
        1 / Real.log u)) t := by
  have htPos : 0 < t := by linarith
  have htNe : t ≠ 0 := htPos.ne'
  have hlogPos : 0 < Real.log t := Real.log_pos ht
  have hlogNe : Real.log t ≠ 0 := hlogPos.ne'
  have hdenNe : 1024 * Real.log t ≠ 0 :=
    mul_ne_zero (by norm_num) hlogNe
  have htiltNe : dimensionOneRosserSeedTilt t ≠ 0 := by
    rw [dimensionOneRosserSeedTilt]
    exact div_ne_zero htNe hdenNe
  have hid : ContinuousAt (fun u : Real => u) t := continuousAt_id
  have hden : ContinuousAt (fun u : Real => 1024 * Real.log u) t :=
    continuousAt_const.mul (Real.continuousAt_log htNe)
  have htilt : ContinuousAt dimensionOneRosserSeedTilt t := by
    unfold dimensionOneRosserSeedTilt
    exact hid.div hden hdenNe
  have hlogTilt : ContinuousAt
      (fun u => Real.log (dimensionOneRosserSeedTilt u)) t :=
    (Real.continuousAt_log htiltNe).comp htilt
  have hinvLog : ContinuousAt (fun u : Real => 1 / Real.log u) t :=
    continuousAt_const.div (Real.continuousAt_log htNe) hlogNe
  exact (dimensionOneRosserSeedEnvelope_hasDerivAt ht).continuousAt.mul
    ((continuousAt_const.sub hlogTilt).add hinvLog)

private theorem dimensionOneRosserSeedEnvelope_deriv_continuousOn
    {a b : Real} (ha : 1 < a) :
    ContinuousOn (fun t => dimensionOneRosserSeedEnvelope t *
      (3 - Real.log (dimensionOneRosserSeedTilt t) +
        1 / Real.log t)) (Icc a b) := by
  intro t ht
  exact (dimensionOneRosserSeedEnvelope_deriv_continuousAt
    (ha.trans_le ht.1)).continuousWithinAt

/-- The independent seed envelope is strictly decreasing on the inclusive
large domain. -/
theorem dimensionOneRosserSeedEnvelope_strictAntiOn :
    StrictAntiOn dimensionOneRosserSeedEnvelope
      (Set.Ici (Real.exp 5000)) := by
  refine strictAntiOn_of_hasDerivWithinAt_neg
    (D := Set.Ici (Real.exp 5000))
    (f' := fun t => dimensionOneRosserSeedEnvelope t *
      (3 - Real.log (dimensionOneRosserSeedTilt t) +
        1 / Real.log t))
    (convex_Ici _) ?_ ?_ ?_
  · apply dimensionOneRosserSeedEnvelope_continuousOn.mono
    intro t ht
    have hexpOne : 1 < Real.exp 5000 := by
      linarith [Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)]
    exact hexpOne.trans_le ht
  · intro t ht
    rw [interior_Ici] at ht
    have hexpOne : 1 < Real.exp 5000 := by
      linarith [Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)]
    exact (dimensionOneRosserSeedEnvelope_hasDerivAt
      (hexpOne.trans ht)).hasDerivWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    exact mul_neg_of_pos_of_neg
      (dimensionOneRosserSeedEnvelope_pos t)
      ((dimensionOneRosserSeedEnvelope_derivCoefficient_le
        ht.le).trans_lt (by norm_num))

/-- A unit backward shift costs at most one factor of the current
parameter. -/
theorem dimensionOneRosserSeedEnvelope_shift_le
    {s : Real} (hs : Real.exp 5000 + 1 <= s) :
    dimensionOneRosserSeedEnvelope (s - 1) <=
      s * dimensionOneRosserSeedEnvelope s := by
  let E : Real -> Real := fun t =>
    t * (4 - Real.log (dimensionOneRosserSeedTilt t))
  let F : Real -> Real := fun t => E t + t * Real.log s
  have hsMinus : Real.exp 5000 <= s - 1 := by linarith
  have hsPos : 0 < s := by
    linarith [Real.exp_pos (5000 : Real)]
  have hInterval : s - 1 <= s := by linarith
  have hFContinuous : ContinuousOn F (Icc (s - 1) s) := by
    intro t ht
    have htOne : 1 < t := by
      have hexpOne : 1 < Real.exp 5000 := by
        linarith [Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)]
      exact hexpOne.trans_le (hsMinus.trans ht.1)
    exact ((dimensionOneRosserSeedExponent_hasDerivAt htOne).continuousAt.add
      (continuousAt_id.mul continuousAt_const)).continuousWithinAt
  have hFDeriv : forall t, t ∈ interior (Icc (s - 1) s) ->
      HasDerivWithinAt F
        (3 - Real.log (dimensionOneRosserSeedTilt t) +
          1 / Real.log t + Real.log s)
        (interior (Icc (s - 1) s)) t := by
    intro t ht
    rw [interior_Icc] at ht
    have htLarge : Real.exp 5000 <= t := hsMinus.trans ht.1.le
    have htOne : 1 < t := by
      have hexpOne : 1 < Real.exp 5000 := by
        linarith [Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)]
      exact hexpOne.trans_le htLarge
    have hderiv := (dimensionOneRosserSeedExponent_hasDerivAt htOne).add
      ((hasDerivAt_id t).mul_const (Real.log s))
    change HasDerivAt F _ t at hderiv
    simpa only [one_mul] using hderiv.hasDerivWithinAt
  have hFDerivNonneg : forall t, t ∈ interior (Icc (s - 1) s) ->
      0 <= 3 - Real.log (dimensionOneRosserSeedTilt t) +
        1 / Real.log t + Real.log s := by
    intro t ht
    rw [interior_Icc] at ht
    have htLarge : Real.exp 5000 <= t := hsMinus.trans ht.1.le
    have hlower :=
      neg_log_le_dimensionOneRosserSeedEnvelope_derivCoefficient htLarge
    have hlog : Real.log t <= Real.log s :=
      Real.strictMonoOn_log.monotoneOn
        ((Real.exp_pos 5000).trans_le htLarge) hsPos ht.2.le
    linarith
  have hFMono : MonotoneOn F (Icc (s - 1) s) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      hFContinuous hFDeriv hFDerivNonneg
  have hFEndpoints : F (s - 1) <= F s :=
    hFMono (left_mem_Icc.mpr hInterval) (right_mem_Icc.mpr hInterval)
      hInterval
  have hExponent : E (s - 1) <= E s + Real.log s := by
    dsimp only [F] at hFEndpoints
    linarith
  unfold dimensionOneRosserSeedEnvelope
  calc
    Real.exp ((s - 1) *
        (4 - Real.log (dimensionOneRosserSeedTilt (s - 1)))) <=
        Real.exp (s * (4 - Real.log (dimensionOneRosserSeedTilt s)) +
          Real.log s) := Real.exp_le_exp.mpr hExponent
    _ = s * Real.exp
        (s * (4 - Real.log (dimensionOneRosserSeedTilt s))) := by
      rw [Real.exp_add, Real.exp_log hsPos]
      ring

/-- The shifted seed envelope consumes at most one quarter of the envelope
drop across the propagation interval. -/
theorem integral_dimensionOneRosserSeedEnvelope_shift_le
    {s s0 : Real} (hs : Real.exp 5000 + 1 <= s)
    (hss0 : s <= s0) :
    (∫ t in s..s0,
      dimensionOneRosserSeedEnvelope (t - 1) / (t - 1)) <=
      (dimensionOneRosserSeedEnvelope s -
        dimensionOneRosserSeedEnvelope s0) / 4 := by
  let d : Real -> Real := fun t =>
    3 - Real.log (dimensionOneRosserSeedTilt t) + 1 / Real.log t
  have hsOne : 1 < s := by
    linarith [Real.exp_pos (5000 : Real)]
  have hShiftContinuous : ContinuousOn (fun t =>
      dimensionOneRosserSeedEnvelope (t - 1) / (t - 1))
      (Icc s s0) := by
    intro t ht
    have htLarge : Real.exp 5000 + 1 <= t := hs.trans ht.1
    have htShiftOne : 1 < t - 1 := by
      have hExpOne : 1 < Real.exp 5000 := by
        linarith [Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)]
      linarith
    have hshift : ContinuousAt (fun u : Real => u - 1) t :=
      continuousAt_id.sub continuousAt_const
    have hnumerator : ContinuousAt
        (fun u => dimensionOneRosserSeedEnvelope (u - 1)) t :=
      (dimensionOneRosserSeedEnvelope_hasDerivAt
        htShiftOne).continuousAt.comp_of_eq hshift rfl
    exact (hnumerator.div hshift (by linarith)).continuousWithinAt
  have hShiftIntegrable : IntervalIntegrable (fun t =>
      dimensionOneRosserSeedEnvelope (t - 1) / (t - 1))
      volume s s0 :=
    hShiftContinuous.intervalIntegrable_of_Icc hss0
  have hDerivContinuous : ContinuousOn (fun t =>
      dimensionOneRosserSeedEnvelope t * d t) (Icc s s0) := by
    exact dimensionOneRosserSeedEnvelope_deriv_continuousOn hsOne
  have hDerivIntegrable : IntervalIntegrable (fun t =>
      dimensionOneRosserSeedEnvelope t * d t) volume s s0 :=
    hDerivContinuous.intervalIntegrable_of_Icc hss0
  have hNegDerivIntegrable : IntervalIntegrable (fun t =>
      -(dimensionOneRosserSeedEnvelope t * d t) / 4) volume s s0 :=
    hDerivIntegrable.neg.div_const 4
  have hPointwise : forall t, t ∈ Icc s s0 ->
      dimensionOneRosserSeedEnvelope (t - 1) / (t - 1) <=
        -(dimensionOneRosserSeedEnvelope t * d t) / 4 := by
    intro t ht
    have htLarge : Real.exp 5000 + 1 <= t := hs.trans ht.1
    have htPos : 0 < t := by
      linarith [Real.exp_pos (5000 : Real)]
    have htMinusPos : 0 < t - 1 := by
      linarith [Real.exp_pos (5000 : Real)]
    have htTwo : 2 <= t := by
      have hExpOne : 1 < Real.exp 5000 := by
        linarith [Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)]
      linarith
    have hShift := dimensionOneRosserSeedEnvelope_shift_le htLarge
    have hRatio : t / (t - 1) <= 2 := by
      rw [div_le_iff₀ htMinusPos]
      linarith
    have hFirst :
        dimensionOneRosserSeedEnvelope (t - 1) / (t - 1) <=
          2 * dimensionOneRosserSeedEnvelope t := by
      calc
        dimensionOneRosserSeedEnvelope (t - 1) / (t - 1) <=
            (t * dimensionOneRosserSeedEnvelope t) / (t - 1) :=
          div_le_div_of_nonneg_right hShift htMinusPos.le
        _ = (t / (t - 1)) * dimensionOneRosserSeedEnvelope t := by ring
        _ <= 2 * dimensionOneRosserSeedEnvelope t :=
          mul_le_mul_of_nonneg_right hRatio
            (dimensionOneRosserSeedEnvelope_pos t).le
    have hCoefficient : d t <= -8 :=
      dimensionOneRosserSeedEnvelope_derivCoefficient_le
        (by linarith : Real.exp 5000 <= t)
    have hMul : dimensionOneRosserSeedEnvelope t * d t <=
        dimensionOneRosserSeedEnvelope t * (-8) :=
      mul_le_mul_of_nonneg_left hCoefficient
        (dimensionOneRosserSeedEnvelope_pos t).le
    have hSecond : 2 * dimensionOneRosserSeedEnvelope t <=
        -(dimensionOneRosserSeedEnvelope t * d t) / 4 := by
      linarith
    exact hFirst.trans hSecond
  have hIntegralLe := intervalIntegral.integral_mono_on hss0
    hShiftIntegrable hNegDerivIntegrable hPointwise
  have hEnvelopeContinuous : ContinuousOn dimensionOneRosserSeedEnvelope
      (Icc s s0) :=
    dimensionOneRosserSeedEnvelope_continuousOn.mono (by
      intro t ht
      exact hsOne.trans_le ht.1)
  have hEnvelopeDeriv : forall t, t ∈ Ioo s s0 ->
      HasDerivAt dimensionOneRosserSeedEnvelope
        (dimensionOneRosserSeedEnvelope t * d t) t := by
    intro t ht
    exact dimensionOneRosserSeedEnvelope_hasDerivAt
      (hsOne.trans ht.1)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hss0 hEnvelopeContinuous hEnvelopeDeriv hDerivIntegrable
  calc
    (∫ t in s..s0,
        dimensionOneRosserSeedEnvelope (t - 1) / (t - 1)) <=
        ∫ t in s..s0,
          -(dimensionOneRosserSeedEnvelope t * d t) / 4 := hIntegralLe
    _ = (dimensionOneRosserSeedEnvelope s -
        dimensionOneRosserSeedEnvelope s0) / 4 := by
      rw [intervalIntegral.integral_div,
        intervalIntegral.integral_neg, hFTC]
      ring

end PrimesRestrictedDigits
