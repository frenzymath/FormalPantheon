import PrimesRestrictedDigits.PrimeNumberTheorem.MaynardBuchstabAbsorption

/-!
# Maynard's normalized Buchstab asymptotic

This file packages the finite normalized estimate as a compact-uniform
epsilon theorem and as the fixed-parameter limit displayed in Maynard's
Eq. (5.2).
-/

namespace PrimesRestrictedDigits

open Filter Topology

/-- A compact-uniform epsilon consequence of the finite normalized estimate.
The eventual threshold is chosen before the later admissible `u`. -/
theorem eventually_maynardRoughCount_power_normalized_uniform :
    ∀ U : Real, 1 ≤ U →
      ∀ ε : Real, 0 < ε →
        ∀ᶠ Y : Real in atTop, ∀ u : Real,
          u ≤ U →
          1 + (Real.sqrt (Real.log Y))⁻¹ < u →
          |(maynardRoughCount Y (Y ^ (1 / u)) : Real) /
              (u * Y / Real.log Y) - buchstabFunction u| < ε := by
  intro U hU ε hε
  obtain ⟨C, hC, hError⟩ :=
    exists_maynardRoughCount_power_normalized_error U hU
  have hU0 : 0 < U := zero_lt_one.trans_le hU
  have hY : ∀ᶠ Y : Real in atTop, 1 < Y := eventually_gt_atTop 1
  have hyU : ∀ᶠ Y : Real in atTop, 2 ≤ Y ^ (1 / U) :=
    (tendsto_rpow_atTop (one_div_pos.mpr hU0)).eventually_ge_atTop 2
  have hrate : ∀ᶠ Y : Real in atTop, C / Real.log Y < ε :=
    (Real.tendsto_log_atTop.const_div_atTop C).eventually_lt_const hε
  filter_upwards [hY, hyU, hrate] with Y hY' hyU' hrate'
  intro u huU hmove
  have hlogY : 0 < Real.log Y := Real.log_pos hY'
  have hsqrt : 0 < Real.sqrt (Real.log Y) := Real.sqrt_pos.2 hlogY
  have hu1 : 1 < u := by
    have hinv : 0 < (Real.sqrt (Real.log Y))⁻¹ := inv_pos.mpr hsqrt
    linarith
  have hu0 : 0 < u := zero_lt_one.trans hu1
  have hexp : 1 / U ≤ 1 / u := one_div_le_one_div_of_le hu0 huU
  have hy : 2 ≤ Y ^ (1 / u) :=
    hyU'.trans (Real.rpow_le_rpow_of_exponent_le hY'.le hexp)
  have hnorm := hError Y u hY' hy huU hmove
  calc
    |(maynardRoughCount Y (Y ^ (1 / u)) : Real) /
        (u * Y / Real.log Y) - buchstabFunction u| ≤
        C / (u * Real.log Y) := hnorm
    _ ≤ C / Real.log Y := by
      apply div_le_div_of_nonneg_left hC.le hlogY
      nlinarith
    _ < ε := hrate'

/-- Maynard's Eq. (5.2) in its literal fixed-`u` normalized limit form. -/
theorem tendsto_maynardRoughCount_power_normalized
    {u : Real} (hu : 1 < u) :
    Tendsto
      (fun Y : Real =>
        (maynardRoughCount Y (Y ^ (1 / u)) : Real) /
          (u * Y / Real.log Y))
      atTop (nhds (buchstabFunction u)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have huniform :=
    eventually_maynardRoughCount_power_normalized_uniform u hu.le ε hε
  have hroot : Tendsto (fun Y : Real => Real.sqrt (Real.log Y)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  have hinv : Tendsto
      (fun Y : Real => (Real.sqrt (Real.log Y))⁻¹) atTop (nhds 0) :=
    hroot.inv_tendsto_atTop
  have hmove : ∀ᶠ Y : Real in atTop,
      1 + (Real.sqrt (Real.log Y))⁻¹ < u := by
    have hadd : Tendsto
        (fun Y : Real => 1 + (Real.sqrt (Real.log Y))⁻¹)
        atTop (nhds 1) := by
      simpa using tendsto_const_nhds.add hinv
    exact hadd.eventually_lt_const hu
  filter_upwards [huniform, hmove] with Y huniformY hmoveY
  simpa [Real.dist_eq] using huniformY u le_rfl hmoveY

end PrimesRestrictedDigits
