import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceRecurrenceReserve

/-!
# Core algebra for the source joint endpoint ledger

These ordered-ring helpers collect the transported boundary, first endpoint,
and strict pre-absorption second estimate.  The sign-specific source wrappers
live in `DimensionOneRosserSourceJointLedger.lean`.
-/

namespace PrimesRestrictedDigits

theorem dimensionOneRosserSourceBoundaryProfile_le
    {K L s0 endpoint current : Real}
    (hK : 0 <= K) (hL : 0 < L) (hs0 : 0 < s0) (hs0L : s0 <= L)
    (hendpoint : endpoint <= 2 * current) (hcurrent : 0 <= current) :
    ((1 + K * s0 / L) / s0) * L ^ (-1 / 24 : Real) * endpoint <=
      (2 * (1 + K) / s0) * L ^ (-1 / 24 : Real) * current := by
  have hs0Div : s0 / L <= 1 := (div_le_one hL).2 hs0L
  have hKratio : K * s0 / L <= K := by
    have h := mul_le_mul_of_nonneg_left hs0Div hK
    calc
      K * s0 / L = K * (s0 / L) := by ring
      _ <= K * 1 := h
      _ = K := by ring
  have hone : 1 + K * s0 / L <= 1 + K := by linarith
  have hcoef0 : 0 <= ((1 + K * s0 / L) / s0) *
      L ^ (-1 / 24 : Real) := by positivity
  have hcoef : ((1 + K * s0 / L) / s0) *
        L ^ (-1 / 24 : Real) <=
      ((1 + K) / s0) * L ^ (-1 / 24 : Real) := by
    gcongr
  calc
    ((1 + K * s0 / L) / s0) * L ^ (-1 / 24 : Real) * endpoint <=
        ((1 + K * s0 / L) / s0) * L ^ (-1 / 24 : Real) *
          (2 * current) := mul_le_mul_of_nonneg_left hendpoint hcoef0
    _ <= ((1 + K) / s0) * L ^ (-1 / 24 : Real) *
          (2 * current) := by
      exact mul_le_mul_of_nonneg_right hcoef (mul_nonneg (by norm_num) hcurrent)
    _ = (2 * (1 + K) / s0) * L ^ (-1 / 24 : Real) * current := by ring

theorem dimensionOneRosserSourceSecondProfile_lt
    {raw relaxed scale decay main kernel endpoint profile : Real}
    (hscale : 0 <= scale) (hdecay : 0 <= decay)
    (hraw : raw <= relaxed)
    (hrelaxed : relaxed < scale * decay * (main * profile + kernel))
    (hendpoint : kernel <= endpoint * profile) :
    raw < scale * decay * (main * profile + endpoint * profile) := by
  have hinside : main * profile + kernel <=
      main * profile + endpoint * profile := by
    simpa only [add_comm] using add_le_add_left hendpoint (main * profile)
  exact hraw.trans_lt (hrelaxed.trans_le
    (mul_le_mul_of_nonneg_left hinside (mul_nonneg hscale hdecay)))

theorem dimensionOneRosserSourceJointLedger_of_estimates
    {boundary first second scale decay profile modelDiff cb ef main e2 target D : Real}
    (hscale : 0 < scale) (hdecay : 0 <= decay) (hprofile : 0 <= profile)
    (hD : 0 <= D)
    (hboundary : boundary < scale * decay * (cb * profile))
    (hfirst : first <= scale * (modelDiff + decay * (ef * profile)))
    (hsecond : second < scale * decay * (main * profile + e2 * profile))
    (hbudget : cb + ef + D * (main + e2) <= D * target) :
    boundary + first + D * second <
      scale * (modelDiff + D * target * decay * profile) := by
  have hsecondScaled : D * second <=
      D * (scale * decay * (main * profile + e2 * profile)) :=
    mul_le_mul_of_nonneg_left hsecond.le hD
  have hbudgetScaled := mul_le_mul_of_nonneg_right hbudget
    (mul_nonneg hdecay hprofile)
  calc
    boundary + first + D * second <
        scale * decay * (cb * profile) +
          scale * (modelDiff + decay * (ef * profile)) +
          D * (scale * decay * (main * profile + e2 * profile)) := by
      exact add_lt_add_of_lt_of_le
        (add_lt_add_of_lt_of_le hboundary hfirst) hsecondScaled
    _ = scale * (modelDiff + decay *
        ((cb + ef + D * (main + e2)) * profile)) := by ring
    _ <= scale * (modelDiff + decay * ((D * target) * profile)) := by
      have hinner : decay * ((cb + ef + D * (main + e2)) * profile) <=
          decay * ((D * target) * profile) := by
        calc
          _ = (cb + ef + D * (main + e2)) * (decay * profile) := by ring
          _ <= (D * target) * (decay * profile) := hbudgetScaled
          _ = _ := by ring
      apply mul_le_mul_of_nonneg_left _ hscale.le
      simpa only [add_comm] using add_le_add_left hinner modelDiff
    _ = scale * (modelDiff + D * target * decay * profile) := by ring

theorem dimensionOneRosserSourceJointScalarBudget
    {c D K L s0 : Real} (_hc : 0 <= c) (hD : 1 <= D) (hK : 0 <= K)
    (hL : 1 <= L) (hs0 : 1 <= s0)
    (hDdom : 2 * (1 + K) + 2304 * c * K <= D)
    (hsmall : 6 * (1 + 2304 * K) <= L ^ (1 / 24 : Real)) :
    (2 * (1 + K) / s0) * L ^ (-1 / 24 : Real) +
        (2304 * c * K / s0) * L ^ (-1 / 24 : Real) +
        D * ((1 - 1 / s0) ^ (2 / 3 : Real) +
          (2304 * K / s0) * L ^ (-1 / 24 : Real)) <=
      D * (1 - 1 / (2 * s0)) := by
  have hD0 : 0 <= D := zero_le_one.trans hD
  have hscale0 : 0 <= 1 / s0 * L ^ (-1 / 24 : Real) := by positivity
  have hdomScaled := mul_le_mul_of_nonneg_right hDdom hscale0
  have hboundaryFirst :
      (2 * (1 + K) / s0) * L ^ (-1 / 24 : Real) +
          (2304 * c * K / s0) * L ^ (-1 / 24 : Real) <=
        D * (1 / s0 * L ^ (-1 / 24 : Real)) := by
    calc
      _ = (2 * (1 + K) + 2304 * c * K) *
          (1 / s0 * L ^ (-1 / 24 : Real)) := by ring
      _ <= _ := hdomScaled
  have hE : 0 <= 1 + 2304 * K := by positivity
  have hreserve := dimensionOneRosserSourceRecurrenceReserve_le
    hE hL hs0 hsmall
  calc
    (2 * (1 + K) / s0) * L ^ (-1 / 24 : Real) +
          (2304 * c * K / s0) * L ^ (-1 / 24 : Real) +
          D * ((1 - 1 / s0) ^ (2 / 3 : Real) +
            (2304 * K / s0) * L ^ (-1 / 24 : Real)) <=
        D * (1 / s0 * L ^ (-1 / 24 : Real)) +
          D * ((1 - 1 / s0) ^ (2 / 3 : Real) +
            (2304 * K / s0) * L ^ (-1 / 24 : Real)) := by
      exact add_le_add_left hboundaryFirst _
    _ = D * ((1 - 1 / s0) ^ (2 / 3 : Real) +
        (1 + 2304 * K) / s0 * L ^ (-1 / 24 : Real)) := by ring
    _ <= D * (1 - 1 / (2 * s0)) :=
      mul_le_mul_of_nonneg_left hreserve hD0

end PrimesRestrictedDigits
