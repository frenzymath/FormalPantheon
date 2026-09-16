import PrimesRestrictedDigits.PrimeNumberTheorem.MaynardBuchstab

/-!
# Absorbing the Maynard Buchstab secondary term

This file turns the explicit power-threshold secondary term and strict-cutoff
endpoint from `MaynardBuchstab` into the same log-square scale as the compact-
uniform remainder, under Maynard's moving lower bound on the Buchstab
parameter.
-/

namespace PrimesRestrictedDigits

private theorem one_le_four_mul_buchstabScale
    {Y : Real} (hY : 1 < Y) :
    1 ≤ 4 * (Y / Real.log Y ^ 2) := by
  have hY0 : 0 ≤ Y := hY.le.trans' zero_le_one
  have hlogY : 0 < Real.log Y := Real.log_pos hY
  have hlogSqrt : Real.log Y ≤ 2 * Real.sqrt Y := by
    have h := Real.log_le_rpow_div (x := Y) (ε := (1 / 2 : Real)) hY0 (by norm_num)
    rw [← Real.sqrt_eq_rpow] at h
    simpa [div_eq_mul_inv, mul_comm] using h
  have hlogSq : Real.log Y ^ 2 ≤ 4 * Y := by
    nlinarith [Real.sq_sqrt hY0]
  have hquarter : (1 : Real) / 4 ≤ Y / Real.log Y ^ 2 := by
    rw [div_le_div_iff₀ (by norm_num : (0 : Real) < 4)
      (sq_pos_of_pos hlogY)]
    nlinarith
  nlinarith

private theorem maynard_power_secondary_le_log_sq
    {U Y u : Real} (hU : 1 ≤ U) (hY : 1 < Y) (huU : u ≤ U)
    (hmove : 1 + (Real.sqrt (Real.log Y))⁻¹ < u) :
    Y ^ (1 / u) / Real.log (Y ^ (1 / u)) ≤
      2 * U ^ 3 * (Y / Real.log Y ^ 2) := by
  let L : Real := Real.log Y
  let s : Real := Real.sqrt L
  let t : Real := L * (u - 1) / u
  have hY0 : 0 < Y := zero_lt_one.trans hY
  have hL : 0 < L := by simpa [L] using Real.log_pos hY
  have hs : 0 < s := by simpa [s] using Real.sqrt_pos.2 hL
  have hU0 : 0 < U := zero_lt_one.trans_le hU
  have hinvS : 0 < s⁻¹ := inv_pos.mpr hs
  have hu1 : 1 < u := by linarith
  have hu0 : 0 < u := zero_lt_one.trans hu1
  have hmoveSub : s⁻¹ < u - 1 := by
    simpa [s, L] using sub_lt_sub_right hmove 1
  have hmoveMul : 1 < (u - 1) * s := by
    have h := mul_lt_mul_of_pos_right hmoveSub hs
    simpa [inv_mul_cancel₀ hs.ne', mul_comm] using h
  have hsSq : s ^ 2 = L := Real.sq_sqrt hL.le
  have hsu : s * u ≤ s * U := mul_le_mul_of_nonneg_left huU hs.le
  have hsUProd : s * U < U * L * (u - 1) := by
    have h := mul_lt_mul_of_pos_left hmoveMul (mul_pos hU0 hs)
    rw [show U * s * ((u - 1) * s) = U * s ^ 2 * (u - 1) by ring] at h
    rw [hsSq] at h
    nlinarith
  have hst : s / U < t := by
    rw [div_lt_div_iff₀ hU0 hu0]
    nlinarith
  have ht : 0 < t := (div_pos hs hU0).trans hst
  have hTaylor := Real.pow_div_factorial_le_exp t ht.le 2
  norm_num at hTaylor
  have hsDiv : 0 ≤ s / U := (div_pos hs hU0).le
  have hsqDiv : (s / U) ^ 2 ≤ t ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hst.le)
      (add_nonneg ht.le hsDiv)]
  have hExpLower : L / (2 * U ^ 2) ≤ Real.exp t := by
    calc
      L / (2 * U ^ 2) = (s / U) ^ 2 / 2 := by
        rw [← hsSq]
        field_simp

      _ ≤ t ^ 2 / 2 := by linarith
      _ ≤ Real.exp t := hTaylor
  have hLowerPos : 0 < L / (2 * U ^ 2) := by positivity
  have hExpInv : Real.exp (-t) ≤ 2 * U ^ 2 / L := by
    rw [Real.exp_neg]
    calc
      (Real.exp t)⁻¹ ≤ (L / (2 * U ^ 2))⁻¹ :=
        by simpa [one_div] using
          one_div_le_one_div_of_le hLowerPos hExpLower
      _ = 2 * U ^ 2 / L := by field_simp
  have hRatioEq : Y ^ (1 / u) / Y = Real.exp (-t) := by
    calc
      Y ^ (1 / u) / Y = Y ^ (1 / u) / Y ^ (1 : Real) := by rw [Real.rpow_one]
      _ = Y ^ (1 / u - 1) := (Real.rpow_sub hY0 (1 / u) 1).symm
      _ = Real.exp (Real.log Y * (1 / u - 1)) :=
        Real.rpow_def_of_pos hY0 _
      _ = Real.exp (-t) := by
        congr 1
        dsimp [t, L]
        field_simp
        ring
  have hRatio : Y ^ (1 / u) / Y ≤ 2 * U ^ 2 / L := by
    rw [hRatioEq]
    exact hExpInv
  have hlogPower :
      Real.log (Y ^ (1 / u)) = (1 / u) * L := by
    simpa [L] using Real.log_rpow hY0 (1 / u)
  have hsecondaryEq :
      Y ^ (1 / u) / Real.log (Y ^ (1 / u)) =
        (Y ^ (1 / u) / Y) * (u * Y / L) := by
    rw [hlogPower]
    field_simp
  rw [hsecondaryEq]
  calc
    (Y ^ (1 / u) / Y) * (u * Y / L) ≤
        (2 * U ^ 2 / L) * (u * Y / L) := by
      exact mul_le_mul_of_nonneg_right hRatio (by positivity)
    _ ≤ (2 * U ^ 2 / L) * (U * Y / L) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right huU hY0.le) hL.le
    _ = 2 * U ^ 3 * (Y / Real.log Y ^ 2) := by
      dsimp [L]
      field_simp

/-- The strict outer endpoint and power-threshold secondary term both fit the
log-square scale on Maynard's moving parameter range. -/
theorem exists_maynardRoughCount_power_log_sq_error :
    ∀ U : Real, 1 ≤ U →
      ∃ C : Real, 0 < C ∧
        ∀ Y u : Real, 1 < Y → 2 ≤ Y ^ (1 / u) → u ≤ U →
          1 + (Real.sqrt (Real.log Y))⁻¹ < u →
          |(maynardRoughCount Y (Y ^ (1 / u)) : Real) -
            buchstabFunction u * u * Y / Real.log Y| ≤
            C * (Y / Real.log Y ^ 2) := by
  intro U hU
  obtain ⟨C0, hC0, hError⟩ := exists_maynardRoughCount_power_error U hU
  refine ⟨C0 + 2 * U ^ 3 + 4, by positivity, ?_⟩
  intro Y u hY hy huU hmove
  have hlogY : 0 < Real.log Y := Real.log_pos hY
  have hsqrt : 0 < Real.sqrt (Real.log Y) := Real.sqrt_pos.2 hlogY
  have hu : 1 ≤ u := by
    have hinv : 0 < (Real.sqrt (Real.log Y))⁻¹ := inv_pos.mpr hsqrt
    linarith
  have hBase := hError Y u (zero_lt_one.trans hY) hy hu huU
  have hsecondary := maynard_power_secondary_le_log_sq hU hY huU hmove
  have hendpoint := one_le_four_mul_buchstabScale hY
  have hscale : 0 ≤ Y / Real.log Y ^ 2 := by positivity
  calc
    |(maynardRoughCount Y (Y ^ (1 / u)) : Real) -
        buchstabFunction u * u * Y / Real.log Y| ≤
        C0 * (Y / Real.log Y ^ 2) +
          Y ^ (1 / u) / Real.log (Y ^ (1 / u)) + 1 := hBase
    _ ≤ C0 * (Y / Real.log Y ^ 2) +
          2 * U ^ 3 * (Y / Real.log Y ^ 2) +
          4 * (Y / Real.log Y ^ 2) := by linarith
    _ = (C0 + 2 * U ^ 3 + 4) * (Y / Real.log Y ^ 2) := by ring

/-- The finite normalized rate obtained by dividing the log-square estimate
by Maynard's positive source scale `u*Y/log Y`. -/
theorem exists_maynardRoughCount_power_normalized_error :
    ∀ U : Real, 1 ≤ U →
      ∃ C : Real, 0 < C ∧
        ∀ Y u : Real, 1 < Y → 2 ≤ Y ^ (1 / u) → u ≤ U →
          1 + (Real.sqrt (Real.log Y))⁻¹ < u →
          |(maynardRoughCount Y (Y ^ (1 / u)) : Real) /
              (u * Y / Real.log Y) - buchstabFunction u| ≤
            C / (u * Real.log Y) := by
  intro U hU
  obtain ⟨C, hC, hError⟩ :=
    exists_maynardRoughCount_power_log_sq_error U hU
  refine ⟨C, hC, ?_⟩
  intro Y u hY hy huU hmove
  have hY0 : 0 < Y := zero_lt_one.trans hY
  have hlogY : 0 < Real.log Y := Real.log_pos hY
  have hsqrt : 0 < Real.sqrt (Real.log Y) := Real.sqrt_pos.2 hlogY
  have hu : 0 < u := by
    have hinv : 0 < (Real.sqrt (Real.log Y))⁻¹ := inv_pos.mpr hsqrt
    linarith
  have hscale : 0 < u * Y / Real.log Y := by positivity
  have hbase := hError Y u hY hy huU hmove
  have hnorm :
      (maynardRoughCount Y (Y ^ (1 / u)) : Real) /
          (u * Y / Real.log Y) - buchstabFunction u =
        ((maynardRoughCount Y (Y ^ (1 / u)) : Real) -
          buchstabFunction u * (u * Y / Real.log Y)) /
            (u * Y / Real.log Y) := by
    field_simp
  have hbase' :
      |(maynardRoughCount Y (Y ^ (1 / u)) : Real) -
          buchstabFunction u * (u * Y / Real.log Y)| ≤
        C * (Y / Real.log Y ^ 2) := by
    convert hbase using 1; ring_nf
  rw [hnorm, abs_div, abs_of_pos hscale]
  calc
    |(maynardRoughCount Y (Y ^ (1 / u)) : Real) -
        buchstabFunction u * (u * Y / Real.log Y)| /
          (u * Y / Real.log Y) ≤
        (C * (Y / Real.log Y ^ 2)) / (u * Y / Real.log Y) :=
      div_le_div_of_nonneg_right hbase' hscale.le
    _ = C / (u * Real.log Y) := by
      field_simp

end PrimesRestrictedDigits
