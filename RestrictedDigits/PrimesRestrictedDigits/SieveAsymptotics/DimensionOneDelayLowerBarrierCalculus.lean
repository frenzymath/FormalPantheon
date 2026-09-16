import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceSeedNormalization
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneDelayPairing
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Calculus for an explicit lower delay barrier

The auxiliary profile is the source-scale lower barrier. Global propagation is in a later
module.
-/

open MeasureTheory Set

noncomputable section

namespace PrimesRestrictedDigits

def dimensionOneDelayAuxiliaryExponent : Real -> Real :=
  (fun s => s * Real.log s) +
    (fun s => s * Real.log (Real.log s)) -
    (fun s => s) +
    (fun s => 7 * (s * Real.log (Real.log s) / Real.log s))

noncomputable def dimensionOneDelayAuxiliaryLowerScale (s : Real) : Real :=
  Real.exp (-dimensionOneDelayAuxiliaryExponent s)

theorem dimensionOneDelayAuxiliaryLowerScale_pos (s : Real) :
    0 < dimensionOneDelayAuxiliaryLowerScale s := by
  unfold dimensionOneDelayAuxiliaryLowerScale
  exact Real.exp_pos _

theorem dimensionOneDelayAuxiliaryLowerScale_continuousOn :
    ContinuousOn dimensionOneDelayAuxiliaryLowerScale (Ioi (1 : Real)) := by
  intro s hs
  change 1 < s at hs
  have hs0 : 0 < s := by linarith
  have hlog : 0 < Real.log s := Real.log_pos hs
  have hlogAt : ContinuousAt (fun t : Real => Real.log t) s :=
    Real.continuousAt_log hs0.ne'
  have hloglog : ContinuousAt (fun t : Real =>
      Real.log (Real.log t)) s :=
    (Real.continuousAt_log hlog.ne').comp hlogAt
  have hquot : ContinuousAt (fun t : Real =>
      Real.log (Real.log t) / Real.log t) s :=
    hloglog.div hlogAt hlog.ne'
  have hExp : ContinuousAt (fun t : Real =>
      -t * Real.log t - t * Real.log (Real.log t) + t -
        7 * t * Real.log (Real.log t) / Real.log t) s := by
    exact ((continuousAt_id.neg.mul hlogAt).sub
      (continuousAt_id.mul hloglog)).add continuousAt_id |>.sub
        (((continuousAt_const.mul continuousAt_id).mul hloglog).div
          hlogAt hlog.ne')
  have hcomp : ContinuousWithinAt
      (Real.exp ∘ fun t : Real =>
        -t * Real.log t - t * Real.log (Real.log t) + t -
          7 * t * Real.log (Real.log t) / Real.log t)
      (Ioi (1 : Real)) s :=
    (Real.continuous_exp.continuousAt.comp hExp).continuousWithinAt
  have hEq : (fun t : Real =>
      Real.exp (-dimensionOneDelayAuxiliaryExponent t)) =
      (Real.exp ∘ fun t : Real =>
        -t * Real.log t - t * Real.log (Real.log t) + t -
          7 * t * Real.log (Real.log t) / Real.log t) := by
    funext t
    simp [dimensionOneDelayAuxiliaryExponent]
    ring
  change ContinuousWithinAt
    (fun t : Real => Real.exp (-dimensionOneDelayAuxiliaryExponent t))
    (Ioi (1 : Real)) s
  rw [hEq]
  exact hcomp

private theorem dimensionOneDelayAuxiliaryRatio_hasDerivAt
    {t : Real} (ht : 1 < t) :
    HasDerivAt (fun u : Real =>
      u * Real.log (Real.log u) / Real.log u)
      (Real.log (Real.log t) * (Real.log t - 1) / (Real.log t) ^ 2 +
        1 / (Real.log t) ^ 2) t := by
  have ht0 : 0 < t := by linarith
  have hlog : 0 < Real.log t := Real.log_pos ht
  have hlogAt : HasDerivAt Real.log (1 / t) t := by
    simpa [one_div] using Real.hasDerivAt_log ht0.ne'
  have hloglog := hlogAt.log hlog.ne'
  have hnum := (hasDerivAt_id t).mul hloglog
  have hquot := hnum.div hlogAt hlog.ne'
  apply hquot.congr_deriv
  simp only [id_eq, Pi.mul_apply]
  field_simp [ht0.ne', hlog.ne']
  ring_nf

theorem dimensionOneDelayAuxiliaryExponent_hasDerivAt
    {t : Real} (ht : 1 < t) :
    HasDerivAt dimensionOneDelayAuxiliaryExponent
      (Real.log t + Real.log (Real.log t) + 1 / Real.log t +
        7 * (Real.log (Real.log t) * (Real.log t - 1) /
          (Real.log t) ^ 2 + 1 / (Real.log t) ^ 2)) t := by
  have ht0 : 0 < t := by linarith
  have hlog := Real.hasDerivAt_log ht0.ne'
  have hloglog := hlog.log (Real.log_pos ht).ne'
  have hfirst := (hasDerivAt_id t).mul hlog
  have hsecond := (hasDerivAt_id t).mul hloglog
  have hratio := dimensionOneDelayAuxiliaryRatio_hasDerivAt ht
  unfold dimensionOneDelayAuxiliaryExponent
  have h := hfirst.add hsecond
  have h' := (h.sub (hasDerivAt_id t)).add (hratio.const_mul 7)
  change HasDerivAt
    ((fun u : Real => u * Real.log u) +
      (fun u => u * Real.log (Real.log u)) -
      (fun u : Real => u) +
      (fun u : Real => 7 * (u * Real.log (Real.log u) / Real.log u)))
    _ t
  apply h'.congr_deriv
  simp only [id_eq,    one_mul]
  field_simp [ht0.ne', (Real.log_pos ht).ne']
  ring_nf

theorem dimensionOneDelayAuxiliaryLowerScale_hasDerivAt
    {t : Real} (ht : 1 < t) :
    HasDerivAt dimensionOneDelayAuxiliaryLowerScale
      (-dimensionOneDelayAuxiliaryLowerScale t *
        (Real.log t + Real.log (Real.log t) + 1 / Real.log t +
          7 * (Real.log (Real.log t) * (Real.log t - 1) /
            (Real.log t) ^ 2 + 1 / (Real.log t) ^ 2))) t := by
  unfold dimensionOneDelayAuxiliaryLowerScale
  have h := (dimensionOneDelayAuxiliaryExponent_hasDerivAt ht).neg.exp
  apply h.congr_deriv
  simp only [ Pi.neg_apply]
  ring

private theorem dimensionOneDelayAuxiliary_log_window_lower
    {s t : Real} (hs : Real.exp 5000 + 1 <= s)
    (ht : t ∈ Icc (s - 1) s) :
    Real.log s - 1 / (s - 1) <= Real.log t := by
  have hs0 : 0 < s := by linarith [Real.exp_pos (5000 : Real)]
  have hsMinus : 0 < s - 1 := by linarith [Real.exp_pos (5000 : Real)]
  have ht0 : 0 < t := lt_of_lt_of_le hsMinus ht.1
  have hfrac : s / t <= s / (s - 1) :=
    div_le_div_of_nonneg_left hs0.le hsMinus ht.1
  have hfrac' : s / (s - 1) = 1 + 1 / (s - 1) := by
    field_simp [ne_of_gt hsMinus]
    ring
  have hlogratio := Real.log_le_sub_one_of_pos (div_pos hs0 ht0)
  have hlogdiv : Real.log s - Real.log t = Real.log (s / t) := by
    rw [Real.log_div hs0.ne' ht0.ne']
  have hlogbound : Real.log (s / t) <= 1 / (s - 1) := by
    calc
      Real.log (s / t) <= s / t - 1 := hlogratio
      _ <= 1 / (s - 1) := by linarith [hfrac, hfrac', hsMinus]
  have hdiff : Real.log s - Real.log t <= 1 / (s - 1) := by
    rw [hlogdiv]
    exact hlogbound
  linarith

private theorem dimensionOneDelayAuxiliary_loglog_window_lower
    {s t : Real} (hs : Real.exp 5000 + 1 <= s)
    (ht : t ∈ Icc (s - 1) s) :
    Real.log (Real.log s) - 1 / (s - 1) <=
      Real.log (Real.log t) := by
  have hlogLower := dimensionOneDelayAuxiliary_log_window_lower hs ht
  have hs0 : 0 < s := by linarith [Real.exp_pos (5000 : Real)]
  have hsLog : 5000 < Real.log s :=
    (Real.lt_log_iff_exp_lt hs0).2 (by linarith)
  have hsMinus : 0 < s - 1 := by linarith [Real.exp_pos (5000 : Real)]
  have ht0 : 0 < t := lt_of_lt_of_le hsMinus ht.1
  have hexpOne : Real.exp 1 <= t := by
    have hExp : Real.exp 1 < Real.exp 5000 :=
      Real.exp_lt_exp.mpr (by norm_num)
    have hLeft : Real.exp 5000 <= s - 1 := by linarith
    exact le_trans (le_of_lt hExp) (le_trans hLeft ht.1)
  have htLog : 1 <= Real.log t :=
    (Real.le_log_iff_exp_le (by positivity)).2 hexpOne
  have hlogt : 0 < Real.log t := lt_of_lt_of_le (by norm_num) htLog
  have hratio : Real.log s / Real.log t <=
      1 + (1 / (s - 1)) / Real.log t := by
    apply (div_le_iff₀ hlogt).2
    calc
      Real.log s <= Real.log t + 1 / (s - 1) := by linarith
      _ = (1 + (1 / (s - 1)) / Real.log t) * Real.log t := by
        field_simp [hlogt.ne']
  have hsOne : 1 < s := by
    nlinarith [Real.exp_pos (5000 : Real)]
  have hlogratio := Real.log_le_sub_one_of_pos
    (div_pos (Real.log_pos hsOne) hlogt)
  have hlogdiv : Real.log (Real.log s) - Real.log (Real.log t) =
      Real.log (Real.log s / Real.log t) := by
    rw [Real.log_div (Real.log_pos hsOne).ne' hlogt.ne']
  have hbound : Real.log (Real.log s) - Real.log (Real.log t) <=
      1 / (s - 1) := by
    rw [hlogdiv]
    calc
      Real.log (Real.log s / Real.log t) <=
          Real.log s / Real.log t - 1 := hlogratio
      _ <= (1 / (s - 1)) / Real.log t := by linarith [hratio]
      _ <= 1 / (s - 1) := by
        apply (div_le_iff₀ hlogt).2
        have hEta : 0 <= 1 / (s - 1) := by positivity
        have hmul := mul_le_mul_of_nonneg_left htLog hEta
        simpa using hmul
  linarith

private theorem dimensionOneDelayAuxiliaryExponent_derivative_lower
    {s t : Real} (hs : Real.exp 5000 + 1 <= s)
    (ht : t ∈ Icc (s - 1) s) :
    Real.log s + Real.log (Real.log s) +
        (3 / 2 : Real) * Real.log (Real.log s) / Real.log s <=
      Real.log t + Real.log (Real.log t) + 1 / Real.log t +
        7 * (Real.log (Real.log t) * (Real.log t - 1) /
          (Real.log t) ^ 2 + 1 / (Real.log t) ^ 2) := by
  have hs0 : 0 < s := by linarith [Real.exp_pos (5000 : Real)]
  have hsMinus : 0 < s - 1 := by linarith [Real.exp_pos (5000 : Real)]
  have ht0 : 0 < t := lt_of_lt_of_le hsMinus ht.1
  have hsOne : 1 < s := by nlinarith [Real.exp_pos (5000 : Real)]
  have hsLog : 5000 < Real.log s :=
    (Real.lt_log_iff_exp_lt hs0).2 (by linarith)
  have htLogOne : 1 <= Real.log t := by
    have hExp : Real.exp 1 <= t := by
      have hExpLt : Real.exp 1 < Real.exp 5000 :=
        Real.exp_lt_exp.mpr (by norm_num)
      exact le_trans (le_of_lt hExpLt)
        (le_trans (by linarith : Real.exp 5000 <= s - 1) ht.1)
    exact (Real.le_log_iff_exp_le (by positivity)).2 hExp
  have htLogPos : 0 < Real.log t := lt_of_lt_of_le (by norm_num) htLogOne
  have hsLogPos : 0 < Real.log s := by linarith
  have hlogUpper : Real.log t <= Real.log s :=
    Real.strictMonoOn_log.monotoneOn (show t ∈ Ioi (0 : Real) by exact ht0)
      (show s ∈ Ioi (0 : Real) by exact hs0) ht.2
  have hmPos : 0 < Real.log (Real.log s) := by
    apply Real.log_pos
    linarith [hsLog]
  have hlogLower := dimensionOneDelayAuxiliary_log_window_lower hs ht
  have hloglogLower := dimensionOneDelayAuxiliary_loglog_window_lower hs ht
  have hEtaLeOne : 1 / (s - 1) <= 1 := by
    apply (div_le_iff₀ hsMinus).2
    have h := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
    linarith
  have hmOne : 1 < Real.log (Real.log s) := by
    apply (Real.lt_log_iff_exp_lt (by positivity)).2
    have hthree : (3 : Real) < Real.log s := by linarith [hsLog]
    exact Real.exp_one_lt_three.trans hthree
  have hSminusTwo : 2 <= s - 1 := by
    have h := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
    linarith
  have hEtaHalf : 1 / (s - 1) <= (1 / 2 : Real) := by
    apply (div_le_iff₀ hsMinus).2
    linarith
  have hratioHalf : (1 / 2 : Real) <=
      (Real.log t - 1) / Real.log t := by
    apply (le_div_iff₀ htLogPos).2
    linarith [htLogOne]
  have hinv : 1 / Real.log s <= 1 / Real.log t :=
    one_div_le_one_div_of_le htLogPos hlogUpper
  have hReserve : 2 / (s - 1) <= 1 / Real.log s := by
    have hden : 0 < 2 * Real.log s := mul_pos (by norm_num) hsLogPos
    have hcore : 2 * Real.log s <= s - 1 := by
      have h := dimensionOneRosserSeed_log_mul_lt hs
      linarith
    calc
      2 / (s - 1) <= 2 / (2 * Real.log s) := by
        apply div_le_div_of_nonneg_left (by norm_num) hden
        exact hcore
      _ = 1 / Real.log s := by field_simp
  have hBase : Real.log s + Real.log (Real.log s) <=
      Real.log t + Real.log (Real.log t) + 1 / Real.log t := by
    have hsum : Real.log s + Real.log (Real.log s) <=
        Real.log t + Real.log (Real.log t) + 2 / (s - 1) := by
      calc
        Real.log s + Real.log (Real.log s) =
            (Real.log s - 1 / (s - 1)) +
              (Real.log (Real.log s) - 1 / (s - 1)) +
              2 / (s - 1) := by ring
        _ <= Real.log t + Real.log (Real.log t) +
            2 / (s - 1) := by linarith [hlogLower, hloglogLower]
    have htail : 2 / (s - 1) <= 1 / Real.log t :=
      hReserve.trans hinv
    linarith
  have hpLower : 0 <= Real.log (Real.log s) - 1 / (s - 1) := by
    linarith [hmOne, hEtaHalf]
  have hpNonneg : 0 <= Real.log (Real.log t) :=
    (Real.log_pos (by linarith [htLogOne])).le
  have hmLower : Real.log (Real.log s) / 2 <=
      Real.log (Real.log s) - 1 / (s - 1) := by
    linarith [hmOne, hEtaHalf]
  have hprod : Real.log (Real.log s) / 4 / Real.log s <=
      Real.log (Real.log t) * (Real.log t - 1) /
        (Real.log t) ^ 2 := by
    have hfirst : Real.log (Real.log s) / 4 <=
        Real.log (Real.log t) * ((Real.log t - 1) / Real.log t) := by
      calc
        Real.log (Real.log s) / 4 =
            (Real.log (Real.log s) / 2) * (1 / 2) := by ring
        _ <= (Real.log (Real.log s) - 1 / (s - 1)) * (1 / 2) :=
          mul_le_mul_of_nonneg_right hmLower (by norm_num)
        _ <= Real.log (Real.log t) * (1 / 2) :=
          mul_le_mul_of_nonneg_right hloglogLower (by norm_num)
        _ <= Real.log (Real.log t) *
            ((Real.log t - 1) / Real.log t) :=
          mul_le_mul_of_nonneg_left hratioHalf hpNonneg
    have hsecond :=
      mul_le_mul_of_nonneg_right hfirst (one_div_pos.mpr htLogPos).le
    calc
      Real.log (Real.log s) / 4 / Real.log s <=
          Real.log (Real.log s) / 4 / Real.log t := by
        have h := mul_le_mul_of_nonneg_left hinv (by positivity :
          0 <= Real.log (Real.log s) / 4)
        simpa [div_eq_mul_inv] using h
      _ <= Real.log (Real.log t) *
          ((Real.log t - 1) / Real.log t) / Real.log t := by
        simpa [div_eq_mul_inv] using hsecond
      _ = _ := by
        field_simp [htLogPos.ne']
  have hError : (3 / 2 : Real) * Real.log (Real.log s) /
      Real.log s <=
        7 * (Real.log (Real.log t) * (Real.log t - 1) /
          (Real.log t) ^ 2 + 1 / (Real.log t) ^ 2) := by
    have hcoef : (3 / 2 : Real) *
        Real.log (Real.log s) / Real.log s <=
        7 * (Real.log (Real.log s) / 4 / Real.log s) := by
      have hnon : 0 <= Real.log (Real.log s) / Real.log s :=
        div_nonneg hmPos.le hsLogPos.le
      have hmul := mul_le_mul_of_nonneg_right
        (show (3 / 2 : Real) <= 7 / 4 by norm_num) hnon
      calc
        (3 / 2 : Real) * Real.log (Real.log s) / Real.log s =
            (3 / 2 : Real) *
              (Real.log (Real.log s) / Real.log s) := by ring
        _ <= (7 / 4 : Real) *
            (Real.log (Real.log s) / Real.log s) := hmul
        _ = 7 * (Real.log (Real.log s) / 4 / Real.log s) := by ring
    calc
      (3 / 2 : Real) * Real.log (Real.log s) / Real.log s <=
          7 * (Real.log (Real.log s) / 4 / Real.log s) := by
            simpa [mul_div_assoc] using hcoef
      _ <= 7 * (Real.log (Real.log t) * (Real.log t - 1) /
          (Real.log t) ^ 2) :=
        mul_le_mul_of_nonneg_left hprod (by norm_num)
      _ <= 7 * (Real.log (Real.log t) * (Real.log t - 1) /
          (Real.log t) ^ 2 + 1 / (Real.log t) ^ 2) := by
        exact mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right (by positivity)) (by norm_num)
  linarith [hBase, hError]

private theorem dimensionOneDelayAuxiliaryExponent_continuousOn :
    ContinuousOn dimensionOneDelayAuxiliaryExponent (Ioi (1 : Real)) := by
  intro t ht
  exact (dimensionOneDelayAuxiliaryExponent_hasDerivAt ht).continuousAt
    |>.continuousWithinAt

theorem dimensionOneDelayAuxiliaryExponent_window_slope
    {s x : Real} (hs : Real.exp 5000 + 1 <= s)
    (hx : x ∈ Icc (s - 1) s) :
    dimensionOneDelayAuxiliaryExponent x +
        (Real.log s + Real.log (Real.log s) +
          (3 / 2 : Real) * Real.log (Real.log s) / Real.log s) *
          (s - x) <= dimensionOneDelayAuxiliaryExponent s := by
  have hsMinus : 0 < s - 1 := by linarith [Real.exp_pos (5000 : Real)]
  have hInterval : s - 1 <= s := by linarith
  have hExpOne : 1 < Real.exp (5000 : Real) := by
    have h := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
    linarith
  have hLower : Real.exp 5000 <= s - 1 := by linarith [hs]
  have hCarrier : Icc (s - 1) s ⊆ Ioi (1 : Real) := by
    intro t ht
    change 1 < t
    exact by linarith [ht.1, hLower, hExpOne]
  let q : Real := Real.log s + Real.log (Real.log s) +
    (3 / 2 : Real) * Real.log (Real.log s) / Real.log s
  let H : Real -> Real := fun t =>
    dimensionOneDelayAuxiliaryExponent t - q * t
  have hHCont : ContinuousOn H (Icc (s - 1) s) := by
    exact (dimensionOneDelayAuxiliaryExponent_continuousOn.mono hCarrier).sub
      (continuousOn_const.mul continuousOn_id)
  have hHDeriv : ∀ t ∈ interior (Icc (s - 1) s),
      HasDerivWithinAt H
        (Real.log t + Real.log (Real.log t) + 1 / Real.log t +
          7 * (Real.log (Real.log t) * (Real.log t - 1) /
            (Real.log t) ^ 2 + 1 / (Real.log t) ^ 2) - q)
        (interior (Icc (s - 1) s)) t := by
    intro t ht
    rw [interior_Icc] at ht
    have hderiv := (dimensionOneDelayAuxiliaryExponent_hasDerivAt
      (by exact hCarrier ⟨ht.1.le, ht.2.le⟩)).sub
      (hasDerivAt_const t q |>.mul (hasDerivAt_id t))
    change HasDerivAt H _ t at hderiv
    simpa [q] using hderiv.hasDerivWithinAt
  have hHNonneg : ∀ t ∈ interior (Icc (s - 1) s),
      0 <= Real.log t + Real.log (Real.log t) + 1 / Real.log t +
        7 * (Real.log (Real.log t) * (Real.log t - 1) /
          (Real.log t) ^ 2 + 1 / (Real.log t) ^ 2) - q := by
    intro t ht
    rw [interior_Icc] at ht
    exact sub_nonneg.mpr (dimensionOneDelayAuxiliaryExponent_derivative_lower
      hs ⟨ht.1.le, ht.2.le⟩)
  have hMono : MonotoneOn H (Icc (s - 1) s) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      hHCont hHDeriv hHNonneg
  have hEndpoints := hMono hx (right_mem_Icc.mpr hInterval) hx.2
  dsimp [H, q] at hEndpoints
  linarith

end PrimesRestrictedDigits
