import PrimesRestrictedDigits.ExceptionalMinorArcs.SplitPrimeExceptionalHighLogSaving
import PrimesRestrictedDigits.MajorArcs.M2Absorption
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Scalar thresholds for Proposition 9.3

This absorbs the generic fixed power saving into an arbitrary logarithmic saving and verifies
the source log-log region width uniformly in the region arity.
-/

open Filter Asymptotics

namespace PrimesRestrictedDigits

noncomputable section

/-- A positive decimal length has logarithm at least one. -/
theorem one_le_log_powTen_of_pos {length : Nat} (hlength : 0 < length) :
    1 ≤ Real.log (((10 ^ length : Nat) : Real)) := by
  have hlengthBound := length_succ_le_two_mul_log_powTen hlength
  have htwo : (2 : Real) ≤ (length + 1 : Nat) := by
    exact_mod_cast (show 2 ≤ length + 1 by omega)
  linarith

/-- The fixed generic power saving eventually dominates any natural
logarithmic power on decimal scales. -/
theorem exists_genericPowerSaving_logThreshold (A : Nat) :
    ∃ length0 : Nat, ∀ length : Nat, length0 ≤ length →
      1 / (((10 ^ length : Nat) : Real) ^
          (127 / 21338240 : Real)) ≤
        1 / Real.log (((10 ^ length : Nat) : Real)) ^ A := by
  have hbound :=
    (isLittleO_log_rpow_rpow_atTop (A : Real)
      (by norm_num : (0 : Real) < 127 / 21338240)).bound zero_lt_one
  have hreal : ∀ᶠ X : Real in atTop,
      1 / X ^ (127 / 21338240 : Real) ≤
        1 / Real.log X ^ A := by
    filter_upwards [hbound, eventually_gt_atTop (1 : Real)] with X hgrowth hX
    have hXPos : 0 < X := zero_lt_one.trans hX
    have hlogPos : 0 < Real.log X := Real.log_pos hX
    have hleft : 0 ≤ Real.log X ^ (A : Real) :=
      Real.rpow_nonneg hlogPos.le _
    have hright : 0 ≤ X ^ (127 / 21338240 : Real) :=
      Real.rpow_nonneg hXPos.le _
    have hgrowth' : Real.log X ^ (A : Real) ≤
        X ^ (127 / 21338240 : Real) := by
      simpa only [Real.norm_of_nonneg hleft, Real.norm_of_nonneg hright,
        one_mul] using hgrowth
    rw [Real.rpow_natCast] at hgrowth'
    exact one_div_le_one_div_of_le (pow_pos hlogPos A) hgrowth'
  have hpow :
      Tendsto (fun length : Nat => (10 : Real) ^ length) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hpull := hpow.eventually hreal
  have hpull' : ∀ᶠ length : Nat in atTop,
      1 / (((10 ^ length : Nat) : Real) ^
          (127 / 21338240 : Real)) ≤
        1 / Real.log (((10 ^ length : Nat) : Real)) ^ A := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hpull
  exact eventually_atTop.mp hpull'

/-- The log-log region width satisfies the product-scale margin uniformly in
every arity allowed by the source. -/
theorem exists_exceptionalLogLogWidthMarginThreshold
    (eta mu : Real) (heta : 0 < eta) (hmu : 0 < mu) :
    ∃ length0 : Nat, ∀ length : Nat, length0 ≤ length →
      let delta := majorArcM2LogLogDelta (10 ^ length)
      0 ≤ delta ∧
        ∀ k : Nat, ((k + 1 : Nat) : Real) ≤ 2 / eta →
          ((k + 1 : Nat) : Real) * delta +
            1 / (length : Real) ≤ mu := by
  let scale : Nat → Real := fun length => ((10 ^ length : Nat) : Real)
  have hscale : Tendsto scale atTop atTop := by
    simpa only [scale, Nat.cast_pow, Nat.cast_ofNat] using
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : Real) < 10))
  have hlog : Tendsto (fun length => Real.log (scale length)) atTop atTop :=
    Real.tendsto_log_atTop.comp hscale
  have hloglog :
      Tendsto (fun length => Real.log (Real.log (scale length))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  have hdelta : Tendsto
      (fun length => (Real.log (Real.log (scale length)))⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hloglog
  have hlengthInv :
      Tendsto (fun length : Nat => (length : Real)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hdeltaSmall : ∀ᶠ length : Nat in atTop,
      (Real.log (Real.log (scale length)))⁻¹ < mu * eta / 4 :=
    (tendsto_order.1 hdelta).2 (mu * eta / 4) (by positivity)
  have hlengthSmall : ∀ᶠ length : Nat in atTop,
      (length : Real)⁻¹ < mu / 2 :=
    (tendsto_order.1 hlengthInv).2 (mu / 2) (by positivity)
  have hloglogOne : ∀ᶠ length : Nat in atTop,
      1 ≤ Real.log (Real.log (scale length)) :=
    hloglog.eventually_ge_atTop 1
  apply eventually_atTop.mp
  filter_upwards [hdeltaSmall, hlengthSmall, hloglogOne] with length
      hdeltaSmallAt hlengthSmallAt hloglogOneAt
  dsimp only
  have hdeltaNonneg :
      0 ≤ (Real.log (Real.log (((10 ^ length : Nat) : Real))))⁻¹ :=
    inv_nonneg.mpr (zero_le_one.trans hloglogOneAt)
  refine ⟨by simpa only [majorArcM2LogLogDelta] using hdeltaNonneg, ?_⟩
  intro k hell
  have hfirst :
      ((k + 1 : Nat) : Real) *
          (Real.log (Real.log (((10 ^ length : Nat) : Real))))⁻¹ ≤
        mu / 2 := by
    calc
      ((k + 1 : Nat) : Real) *
          (Real.log (Real.log (((10 ^ length : Nat) : Real))))⁻¹ ≤
          (2 / eta) * (mu * eta / 4) := by
        exact mul_le_mul hell hdeltaSmallAt.le hdeltaNonneg (by positivity)
      _ = mu / 2 := by
        field_simp [heta.ne']
        ring
  have hsecond : 1 / (length : Real) ≤ mu / 2 := by
    simpa only [one_div] using hlengthSmallAt.le
  simpa only [majorArcM2LogLogDelta] using (show
    ((k + 1 : Nat) : Real) *
          (Real.log (Real.log (((10 ^ length : Nat) : Real))))⁻¹ +
        1 / (length : Real) ≤ mu by linarith)

end

end PrimesRestrictedDigits
