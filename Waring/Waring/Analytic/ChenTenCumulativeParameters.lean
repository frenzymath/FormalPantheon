import Waring.Analytic.ChenTenCumulativeSource

/-!
# Parameters for Chen's cumulative-count estimate

This file chooses the averaging length used in the cumulative argument and
establishes the upper, lower, positivity, and room inequalities required by
the shift-square count estimate.
-/

set_option autoImplicit false

namespace Waring.Analytic

noncomputable section

/-- The integer averaging length obtained by flooring half of `P ^ (24 / 5)`. -/
def chenTenAverageLength (P : Nat) : Nat :=
  Nat.floor ((P : Real) ^ (24 / 5 : Real) / 2)

private theorem sixtyFour_le_rpow_three_fifths
    {P : Nat} (hPbig : (10 : Nat) ^ 100 ≤ P) :
    (64 : Real) ≤ (P : Real) ^ (3 / 5 : Real) := by
  have hP0 : (0 : Real) ≤ P := by positivity
  apply le_of_pow_le_pow_left₀ (by norm_num : (5 : Nat) ≠ 0)
    (Real.rpow_nonneg hP0 _)
  rw [← Real.rpow_mul_natCast hP0]
  rw [show (3 / 5 : Real) * (5 : Nat) = (3 : Nat) by norm_num,
    Real.rpow_natCast]
  have hcast : (((10 : Nat) ^ 100 : Nat) : Real) ≤ (P : Real) := by
    exact_mod_cast hPbig
  calc
    (64 : Real) ^ 5 ≤ ((((10 : Nat) ^ 100 : Nat) : Real)) ^ 3 := by norm_num
    _ ≤ (P : Real) ^ 3 := pow_le_pow_left₀ (by positivity) hcast 3

private theorem four_le_rpow_twentyFour_fifths
    {P : Nat} (hPbig : (10 : Nat) ^ 100 ≤ P) :
    (4 : Real) ≤ (P : Real) ^ (24 / 5 : Real) := by
  have hP0 : (0 : Real) ≤ P := by positivity
  apply le_of_pow_le_pow_left₀ (by norm_num : (5 : Nat) ≠ 0)
    (Real.rpow_nonneg hP0 _)
  rw [← Real.rpow_mul_natCast hP0]
  rw [show (24 / 5 : Real) * (5 : Nat) = (24 : Nat) by norm_num,
    Real.rpow_natCast]
  have hcast : (((10 : Nat) ^ 100 : Nat) : Real) ≤ (P : Real) := by
    exact_mod_cast hPbig
  calc
    (4 : Real) ^ 5 ≤ ((((10 : Nat) ^ 100 : Nat) : Real)) ^ 24 := by norm_num
    _ ≤ (P : Real) ^ 24 := pow_le_pow_left₀ (by positivity) hcast 24

private theorem four_le_rpow_one_fifth
    {P : Nat} (hPbig : (10 : Nat) ^ 100 ≤ P) :
    (4 : Real) ≤ (P : Real) ^ (1 / 5 : Real) := by
  have hP0 : (0 : Real) ≤ P := by positivity
  apply le_of_pow_le_pow_left₀ (by norm_num : (5 : Nat) ≠ 0)
    (Real.rpow_nonneg hP0 _)
  rw [← Real.rpow_mul_natCast hP0]
  rw [show (1 / 5 : Real) * (5 : Nat) = 1 by norm_num,
    Real.rpow_one]
  have hcast : (((10 : Nat) ^ 100 : Nat) : Real) ≤ (P : Real) := by
    exact_mod_cast hPbig
  exact (by norm_num : (4 : Real) ^ 5 ≤ (((10 : Nat) ^ 100 : Nat) : Real)).trans
    hcast

/-- The averaging length is at most its unfloored real-valued scale. -/
theorem chenTenAverageLength_cast_le (P : Nat) :
    (chenTenAverageLength P : Real) ≤
      (P : Real) ^ (24 / 5 : Real) / 2 := by
  exact Nat.floor_le (by positivity)

/-- The lower target bound gives the required upper bound on the averaging length. -/
theorem chenTenAverageLength_upper_source
    {P N : Nat} (hP : 0 < P)
    (hNlower : (P : Real) ^ 5 / 2 ≤ (N : Real)) :
    (chenTenAverageLength P : Real) ≤
      (N : Real) * (P : Real) ^ (-1 / 5 : Real) := by
  have hPR : (0 : Real) < P := by exact_mod_cast hP
  calc
    (chenTenAverageLength P : Real) ≤
        (P : Real) ^ (24 / 5 : Real) / 2 := chenTenAverageLength_cast_le P
    _ = ((P : Real) ^ 5 * (P : Real) ^ (-1 / 5 : Real)) / 2 := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_add hPR]
      norm_num
    _ = ((P : Real) ^ 5 / 2) *
        (P : Real) ^ (-1 / 5 : Real) := by
      ring
    _ ≤ (N : Real) * (P : Real) ^ (-1 / 5 : Real) := by
      exact mul_le_mul_of_nonneg_right hNlower (by positivity)

/-- Explicit power hypotheses give the required lower bound on the averaging length. -/
theorem chenTenAverageLength_lower_source
    {P N : Nat} (hP : 0 < P)
    (hNupper : N ≤ (P + 1) ^ 5)
    (hPow64 : (64 : Real) ≤ (P : Real) ^ (3 / 5 : Real))
    (hPow4 : (4 : Real) ≤ (P : Real) ^ (24 / 5 : Real)) :
    (N : Real) ^ (4 / 5 : Real) * (P : Real) ^ (1 / 5 : Real) ≤
      (chenTenAverageLength P : Real) := by
  have hPR : (0 : Real) < P := by exact_mod_cast hP
  have hP1 : (1 : Real) ≤ P := by exact_mod_cast hP
  have hNcast : (N : Real) ≤ ((P + 1 : Nat) : Real) ^ 5 := by
    exact_mod_cast hNupper
  have hNrpow : (N : Real) ^ (4 / 5 : Real) ≤
      ((P : Real) + 1) ^ 4 := by
    have hr := Real.rpow_le_rpow (by positivity) hNcast
      (by norm_num : (0 : Real) ≤ 4 / 5)
    calc
      (N : Real) ^ (4 / 5 : Real) ≤
          (((P + 1 : Nat) : Real) ^ 5) ^ (4 / 5 : Real) := hr
      _ = ((P : Real) + 1) ^ 4 := by
        push_cast
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul (by positivity : 0 ≤ (P : Real) + 1)]
        norm_num
  have hPplus : (P : Real) + 1 ≤ 2 * P := by linarith
  have hNcoarse : (N : Real) ^ (4 / 5 : Real) ≤
      16 * (P : Real) ^ 4 := by
    calc
      (N : Real) ^ (4 / 5 : Real) ≤ ((P : Real) + 1) ^ 4 := hNrpow
      _ ≤ (2 * (P : Real)) ^ 4 := by gcongr
      _ = 16 * (P : Real) ^ 4 := by ring
  have htarget :
      (N : Real) ^ (4 / 5 : Real) * (P : Real) ^ (1 / 5 : Real) ≤
        16 * (P : Real) ^ (21 / 5 : Real) := by
    calc
      (N : Real) ^ (4 / 5 : Real) * (P : Real) ^ (1 / 5 : Real) ≤
          (16 * (P : Real) ^ 4) * (P : Real) ^ (1 / 5 : Real) := by
        gcongr
      _ = 16 * (P : Real) ^ (21 / 5 : Real) := by
        rw [← Real.rpow_natCast (P : Real) 4]
        calc
          16 * (P : Real) ^ (4 : Real) * (P : Real) ^ (1 / 5 : Real) =
              16 * ((P : Real) ^ (4 : Real) *
                (P : Real) ^ (1 / 5 : Real)) := by ring
          _ = 16 * (P : Real) ^ ((4 : Real) + 1 / 5) := by
            rw [Real.rpow_add hPR]
          _ = 16 * (P : Real) ^ (21 / 5 : Real) := by norm_num
  have hquarter : 16 * (P : Real) ^ (21 / 5 : Real) ≤
      (P : Real) ^ (24 / 5 : Real) / 4 := by
    have hmul := mul_le_mul_of_nonneg_right hPow64
      (Real.rpow_nonneg hPR.le (21 / 5 : Real))
    have hpow : (P : Real) ^ (3 / 5 : Real) *
        (P : Real) ^ (21 / 5 : Real) =
          (P : Real) ^ (24 / 5 : Real) := by
      rw [← Real.rpow_add hPR]
      norm_num
    rw [hpow] at hmul
    nlinarith
  have hfloor : (P : Real) ^ (24 / 5 : Real) / 2 - 1 <
      (chenTenAverageLength P : Real) := by
    exact Nat.sub_one_lt_floor _
  calc
    (N : Real) ^ (4 / 5 : Real) * (P : Real) ^ (1 / 5 : Real) ≤
        16 * (P : Real) ^ (21 / 5 : Real) := htarget
    _ ≤ (P : Real) ^ (24 / 5 : Real) / 4 := hquarter
    _ ≤ (P : Real) ^ (24 / 5 : Real) / 2 - 1 := by linarith
    _ ≤ (chenTenAverageLength P : Real) := hfloor.le

/-- The chosen averaging length is positive above Chen's large-parameter threshold. -/
theorem chenTenAverageLength_pos
    {P : Nat} (hPbig : (10 : Nat) ^ 100 ≤ P) :
    0 < chenTenAverageLength P := by
  rw [chenTenAverageLength, Nat.floor_pos]
  have h4 := four_le_rpow_twentyFour_fifths hPbig
  linarith

/-- The chosen averaging length is at least two above the large-parameter threshold. -/
theorem two_le_chenTenAverageLength
    {P : Nat} (hPbig : (10 : Nat) ^ 100 ≤ P) :
    2 ≤ chenTenAverageLength P := by
  rw [chenTenAverageLength]
  apply Nat.le_floor
  have h4 := four_le_rpow_twentyFour_fifths hPbig
  linarith

/-- Twice the averaging length is bounded by its defining real power. -/
theorem twice_chenTenAverageLength_le_rpow
    (P : Nat) :
    2 * (chenTenAverageLength P : Real) ≤
      (P : Real) ^ (24 / 5 : Real) := by
  have hM := chenTenAverageLength_cast_le P
  linarith

/-- The defining real power is at most four times the floored averaging length. -/
theorem rpow_le_four_mul_chenTenAverageLength
    {P : Nat} (hPbig : (10 : Nat) ^ 100 ≤ P) :
    (P : Real) ^ (24 / 5 : Real) ≤
      4 * (chenTenAverageLength P : Real) := by
  have h4 := four_le_rpow_twentyFour_fifths hPbig
  have hfloor : (P : Real) ^ (24 / 5 : Real) / 2 - 1 <
      (chenTenAverageLength P : Real) := by
    exact Nat.sub_one_lt_floor _
  have hquarter : (P : Real) ^ (24 / 5 : Real) / 4 ≤
      (chenTenAverageLength P : Real) := by
    linarith
  linarith

/-- The large-parameter threshold discharges the explicit power hypotheses for the lower bound. -/
theorem chenTenAverageLength_lower_source_of_large
    {P N : Nat} (hPbig : (10 : Nat) ^ 100 ≤ P)
    (hNupper : N ≤ (P + 1) ^ 5) :
    (N : Real) ^ (4 / 5 : Real) * (P : Real) ^ (1 / 5 : Real) ≤
      (chenTenAverageLength P : Real) := by
  have hP : 0 < P := lt_of_lt_of_le (by norm_num) hPbig
  exact chenTenAverageLength_lower_source hP hNupper
    (sixtyFour_le_rpow_three_fifths hPbig)
    (four_le_rpow_twentyFour_fifths hPbig)

/-- The target interval leaves room for both shifts and the `K15` error threshold. -/
theorem chenTenAverageLength_room
    {P N : Nat} (hPbig : (10 : Nat) ^ 100 ≤ P)
    (hNlower : (P : Real) ^ 5 / 2 ≤ (N : Real)) :
    15 ^ 5 + 2 * chenTenAverageLength P + 1 ≤ N := by
  have hP : 0 < P := lt_of_lt_of_le (by norm_num) hPbig
  have hPR : (0 : Real) < P := by exact_mod_cast hP
  have hM := chenTenAverageLength_cast_le P
  have htwoM : (2 * chenTenAverageLength P : Nat) ≤
      (P : Real) ^ (24 / 5 : Real) := by
    push_cast
    linarith
  have hroot := four_le_rpow_one_fifth hPbig
  have hpowSplit : (P : Real) ^ (24 / 5 : Real) *
      (P : Real) ^ (1 / 5 : Real) = (P : Real) ^ 5 := by
    rw [← Real.rpow_add hPR]
    norm_num
  have hfirst : (P : Real) ^ (24 / 5 : Real) ≤
      (P : Real) ^ 5 / 4 := by
    have hmul := mul_le_mul_of_nonneg_left hroot
      (Real.rpow_nonneg hPR.le (24 / 5 : Real))
    rw [mul_comm, hpowSplit] at hmul
    linarith
  have hconstNat : 4 * (15 ^ 5 + 1) ≤ P ^ 5 := by
    calc
      4 * (15 ^ 5 + 1) ≤ ((10 : Nat) ^ 100) ^ 5 := by norm_num
      _ ≤ P ^ 5 := Nat.pow_le_pow_left hPbig 5
  have hconst : ((15 ^ 5 + 1 : Nat) : Real) ≤
      (P : Real) ^ 5 / 4 := by
    have hc : ((4 * (15 ^ 5 + 1) : Nat) : Real) ≤
        ((P ^ 5 : Nat) : Real) := by exact_mod_cast hconstNat
    push_cast at hc
    nlinarith
  have htotal : ((15 ^ 5 + 1 : Nat) : Real) +
      2 * (chenTenAverageLength P : Real) ≤ (N : Real) := by
    calc
      ((15 ^ 5 + 1 : Nat) : Real) +
          2 * (chenTenAverageLength P : Real) ≤
          ((15 ^ 5 + 1 : Nat) : Real) +
            (P : Real) ^ (24 / 5 : Real) := by
        linarith
      _ ≤ (P : Real) ^ 5 / 4 + (P : Real) ^ 5 / 4 :=
        add_le_add hconst hfirst
      _ = (P : Real) ^ 5 / 2 := by ring
      _ ≤ (N : Real) := hNlower
  have hcast : ((15 ^ 5 + 1 + 2 * chenTenAverageLength P : Nat) : Real) ≤
      (N : Real) := by
    push_cast
    exact htotal
  have hnat : 15 ^ 5 + 1 + 2 * chenTenAverageLength P ≤ N := by
    exact_mod_cast hcast
  omega

/-- The chosen averaging length satisfies the source form of the cumulative shift-count estimate. -/
theorem chenTen_shiftSquareCount_cumulative_error_source
    {P N : Nat} (hPbig : (10 : Nat) ^ 100 ≤ P)
    (hNlower : (P : Real) ^ 5 / 2 ≤ (N : Real))
    (hNupper : N ≤ (P + 1) ^ 5) :
    |(scratchShiftSquareCount P N (chenTenAverageLength P) : Real) -
        (3 * chenTenT15 * (N : Real) ^ 2) *
          (chenTenAverageLength P : Real) ^ 2| ≤
      (3000 * chenTenT15 * (N : Real) ^ 2 *
        (P : Real) ^ (-1 / 5 : Real)) *
          (chenTenAverageLength P : Real) ^ 2 := by
  have hP : 0 < P := lt_of_lt_of_le (by norm_num) hPbig
  have hNreal : (0 : Real) < N :=
    lt_of_lt_of_le (by positivity : (0 : Real) < (P : Real) ^ 5 / 2) hNlower
  have hN : 0 < N := by exact_mod_cast hNreal
  exact chenTen_shiftSquareCount_cumulative_error_of_scales hP hN
    (chenTenAverageLength_pos hPbig)
    (chenTenAverageLength_room hPbig hNlower) hNupper
    (chenTenAverageLength_lower_source_of_large hPbig hNupper)
    (chenTenAverageLength_upper_source hP hNlower)

end

end Waring.Analytic
