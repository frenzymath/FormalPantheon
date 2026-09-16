import PrimesRestrictedDigits.ExceptionalMinorArcs.AnglesGeneratingLinesExponents
import Mathlib.Tactic.GCongr

/-!
# Comparable-band exponent bounds for angles generating lines

This module proves the real-power inequalities used in the two branches of Proposition 13.4.
-/

namespace PrimesRestrictedDigits

private theorem comparableBandMomentPower_le
    (X B H p : Real) (hX : 0 < X) (hB : 0 < B)
    (hH : 0 <= H) (hp : 0 <= p)
    (hHbound : H <=
      (10 * B) ^ (235 / 154 : Real) * X ^ (59 / 433 : Real)) :
    H ^ p <=
      10 ^ ((235 / 154 : Real) * p) *
        B ^ ((235 / 154 : Real) * p) *
          X ^ ((59 / 433 : Real) * p) := by
  calc
    H ^ p <=
        ((10 * B) ^ (235 / 154 : Real) *
          X ^ (59 / 433 : Real)) ^ p :=
      Real.rpow_le_rpow hH hHbound hp
    _ = ((10 * B) ^ (235 / 154 : Real)) ^ p *
        (X ^ (59 / 433 : Real)) ^ p := by
      rw [Real.mul_rpow (Real.rpow_nonneg (by positivity) _)
        (Real.rpow_nonneg hX.le _)]
    _ = (10 * B) ^ ((235 / 154 : Real) * p) *
        X ^ ((59 / 433 : Real) * p) := by
      rw [← Real.rpow_mul (by positivity : (0 : Real) <= 10 * B)]
      rw [← Real.rpow_mul hX.le]
    _ = (10 ^ ((235 / 154 : Real) * p) *
          B ^ ((235 / 154 : Real) * p)) *
        X ^ ((59 / 433 : Real) * p) := by
      rw [Real.mul_rpow (by norm_num : (0 : Real) <= 10) hB.le]
    _ = 10 ^ ((235 / 154 : Real) * p) *
        B ^ ((235 / 154 : Real) * p) *
          X ^ ((59 / 433 : Real) * p) := by ring

/-- The trivial branch after multiplying the weighted sum by `N*K`. -/
theorem anglesGeneratingLines_trivial_band_bound
    (X B H W Q : Real)
    (hX : 0 < X) (hB : 0 < B)
    (hBupper : B <= X ^ (23 / 80 : Real))
    (hH : 0 <= H)
    (hHbound : H <=
      (10 * B) ^ (235 / 154 : Real) * X ^ (59 / 433 : Real))
    (hW : W <= H ^ 2 / B ^ 2)
    (hQ : 0 <= Q) (hQupper : Q <= X ^ (57 / 80 : Real) / B) :
    W * Q <=
      10 ^ (2 * (235 / 154 : Real)) *
        X ^ (1 - anglesGeneratingLinesSavingLimit) := by
  have hHpow : H ^ 2 <=
      10 ^ (2 * (235 / 154 : Real)) *
        B ^ (2 * (235 / 154 : Real)) *
          X ^ (2 * (59 / 433 : Real)) := by
    have hp := comparableBandMomentPower_le X B H 2
      hX hB hH (by norm_num) hHbound
    calc
      H ^ 2 = H ^ (2 : Real) := (Real.rpow_natCast H 2).symm
      _ <= 10 ^ ((235 / 154 : Real) * 2) *
          B ^ ((235 / 154 : Real) * 2) *
            X ^ ((59 / 433 : Real) * 2) := hp
      _ = 10 ^ (2 * (235 / 154 : Real)) *
          B ^ (2 * (235 / 154 : Real)) *
            X ^ (2 * (59 / 433 : Real)) := by norm_num
  have hBpow :
      B ^ (2 * (235 / 154 : Real) - 3) <=
        X ^ ((23 / 80 : Real) *
          (2 * (235 / 154 : Real) - 3)) := by
    have hbase := Real.rpow_le_rpow hB.le hBupper
      (by norm_num : (0 : Real) <= 2 * (235 / 154 : Real) - 3)
    calc
      B ^ (2 * (235 / 154 : Real) - 3) <=
          (X ^ (23 / 80 : Real)) ^
            (2 * (235 / 154 : Real) - 3) := hbase
      _ = X ^ ((23 / 80 : Real) *
          (2 * (235 / 154 : Real) - 3)) := by
        rw [← Real.rpow_mul hX.le]
  have hBdiv :
      B ^ (2 * (235 / 154 : Real)) / B ^ 2 / B =
        B ^ (2 * (235 / 154 : Real) - 3) := by
    calc
      B ^ (2 * (235 / 154 : Real)) / B ^ 2 / B =
          B ^ (2 * (235 / 154 : Real)) / B ^ 3 := by
        field_simp
      _ = B ^ (2 * (235 / 154 : Real)) / B ^ (3 : Real) := by
        exact congrArg
          (fun z : Real => B ^ (2 * (235 / 154 : Real)) / z)
          (Real.rpow_natCast B 3).symm
      _ = B ^ (2 * (235 / 154 : Real) - 3) :=
        (Real.rpow_sub hB _ _).symm
  have hXmul :
      X ^ (2 * (59 / 433 : Real)) * X ^ (57 / 80 : Real) =
        X ^ (2 * (59 / 433 : Real) + 57 / 80) :=
    (Real.rpow_add hX _ _).symm
  calc
    W * Q <= (H ^ 2 / B ^ 2) * Q :=
      mul_le_mul_of_nonneg_right hW hQ
    _ <= (H ^ 2 / B ^ 2) * (X ^ (57 / 80 : Real) / B) := by
      gcongr
    _ <=
        ((10 ^ (2 * (235 / 154 : Real)) *
            B ^ (2 * (235 / 154 : Real)) *
              X ^ (2 * (59 / 433 : Real))) / B ^ 2) *
          (X ^ (57 / 80 : Real) / B) := by
      gcongr
    _ = 10 ^ (2 * (235 / 154 : Real)) *
        B ^ (2 * (235 / 154 : Real) - 3) *
          X ^ (2 * (59 / 433 : Real) + 57 / 80) := by
      rw [show
        10 ^ (2 * (235 / 154 : Real)) *
              B ^ (2 * (235 / 154 : Real)) *
                X ^ (2 * (59 / 433 : Real)) / B ^ 2 *
              (X ^ (57 / 80 : Real) / B) =
            10 ^ (2 * (235 / 154 : Real)) *
              (B ^ (2 * (235 / 154 : Real)) / B ^ 2 / B) *
                (X ^ (2 * (59 / 433 : Real)) *
                  X ^ (57 / 80 : Real)) by field_simp]
      rw [hBdiv, hXmul]
    _ <= 10 ^ (2 * (235 / 154 : Real)) *
        X ^ ((23 / 80 : Real) *
          (2 * (235 / 154 : Real) - 3)) *
          X ^ (2 * (59 / 433 : Real) + 57 / 80) := by
      gcongr
    _ = 10 ^ (2 * (235 / 154 : Real)) *
        X ^ (1 - anglesGeneratingLinesSavingLimit) := by
      calc
        10 ^ (2 * (235 / 154 : Real)) *
              X ^ ((23 / 80 : Real) *
                (2 * (235 / 154 : Real) - 3)) *
              X ^ (2 * (59 / 433 : Real) + 57 / 80) =
            10 ^ (2 * (235 / 154 : Real)) *
              (X ^ ((23 / 80 : Real) *
                  (2 * (235 / 154 : Real) - 3)) *
                X ^ (2 * (59 / 433 : Real) + 57 / 80)) := by ring
        _ = 10 ^ (2 * (235 / 154 : Real)) *
            X ^ ((23 / 80 : Real) *
                (2 * (235 / 154 : Real) - 3) +
              (2 * (59 / 433 : Real) + 57 / 80)) := by
          rw [← Real.rpow_add hX]
        _ = 10 ^ (2 * (235 / 154 : Real)) *
            X ^ (1 - anglesGeneratingLinesSavingLimit) := by
          congr 2
          norm_num [anglesGeneratingLinesSavingLimit]

/-- The first bracket in the large-`N*K` branch. -/
theorem anglesGeneratingLines_first_band_factor_bound
    (X B H R : Real) (hX : 0 < X) (hB : 0 < B)
    (hBupper : B <= X ^ (23 / 80 : Real))
    (hH : 0 <= H)
    (hHbound : H <=
      (10 * B) ^ (235 / 154 : Real) * X ^ (59 / 433 : Real))
    (_hR : 0 <= R) (hRupper : R <= B * X ^ (23 / 80 : Real)) :
    H ^ (5 / 4 : Real) / B ^ 2 * R <=
      10 ^ ((235 / 154 : Real) * (5 / 4 : Real)) *
        X ^ (23 / 32 - (5 / 4) * (127 / 5334560) : Real) := by
  have hHpow := comparableBandMomentPower_le X B H (5 / 4 : Real)
    hX hB hH (by norm_num) hHbound
  have hExponent :
      0 <= (235 / 154 : Real) * (5 / 4 : Real) - 1 := by norm_num
  have hBpow :
      B ^ ((235 / 154 : Real) * (5 / 4 : Real) - 1) <=
        X ^ ((23 / 80 : Real) *
          ((235 / 154 : Real) * (5 / 4 : Real) - 1)) := by
    calc
      B ^ ((235 / 154 : Real) * (5 / 4 : Real) - 1) <=
          (X ^ (23 / 80 : Real)) ^
            ((235 / 154 : Real) * (5 / 4 : Real) - 1) :=
        Real.rpow_le_rpow hB.le hBupper hExponent
      _ = X ^ ((23 / 80 : Real) *
          ((235 / 154 : Real) * (5 / 4 : Real) - 1)) := by
        rw [← Real.rpow_mul hX.le]
  have hBdiv :
      B ^ ((235 / 154 : Real) * (5 / 4 : Real)) / B ^ 2 * B =
        B ^ ((235 / 154 : Real) * (5 / 4 : Real) - 1) := by
    calc
      B ^ ((235 / 154 : Real) * (5 / 4 : Real)) / B ^ 2 * B =
          B ^ ((235 / 154 : Real) * (5 / 4 : Real)) / B := by
        field_simp
      _ = B ^ ((235 / 154 : Real) * (5 / 4 : Real) - 1) := by
        simpa using
          (Real.rpow_sub hB
            ((235 / 154 : Real) * (5 / 4 : Real)) 1).symm
  have hXmul :
      X ^ ((59 / 433 : Real) * (5 / 4 : Real)) *
          X ^ (23 / 80 : Real) =
        X ^ ((59 / 433 : Real) * (5 / 4 : Real) + 23 / 80) :=
    (Real.rpow_add hX _ _).symm
  calc
    H ^ (5 / 4 : Real) / B ^ 2 * R <=
        H ^ (5 / 4 : Real) / B ^ 2 *
          (B * X ^ (23 / 80 : Real)) := by gcongr
    _ <=
        (10 ^ ((235 / 154 : Real) * (5 / 4 : Real)) *
              B ^ ((235 / 154 : Real) * (5 / 4 : Real)) *
                X ^ ((59 / 433 : Real) * (5 / 4 : Real))) / B ^ 2 *
          (B * X ^ (23 / 80 : Real)) := by gcongr
    _ = 10 ^ ((235 / 154 : Real) * (5 / 4 : Real)) *
        B ^ ((235 / 154 : Real) * (5 / 4 : Real) - 1) *
          X ^ ((59 / 433 : Real) * (5 / 4 : Real) + 23 / 80) := by
      rw [show
        (10 ^ ((235 / 154 : Real) * (5 / 4 : Real)) *
              B ^ ((235 / 154 : Real) * (5 / 4 : Real)) *
                X ^ ((59 / 433 : Real) * (5 / 4 : Real))) / B ^ 2 *
            (B * X ^ (23 / 80 : Real)) =
          10 ^ ((235 / 154 : Real) * (5 / 4 : Real)) *
            (B ^ ((235 / 154 : Real) * (5 / 4 : Real)) / B ^ 2 * B) *
              (X ^ ((59 / 433 : Real) * (5 / 4 : Real)) *
                X ^ (23 / 80 : Real)) by field_simp]
      rw [hBdiv, hXmul]
    _ <= 10 ^ ((235 / 154 : Real) * (5 / 4 : Real)) *
        X ^ ((23 / 80 : Real) *
            ((235 / 154 : Real) * (5 / 4 : Real) - 1)) *
          X ^ ((59 / 433 : Real) * (5 / 4 : Real) + 23 / 80) := by
      gcongr
    _ = 10 ^ ((235 / 154 : Real) * (5 / 4 : Real)) *
        X ^ (23 / 32 - (5 / 4) * (127 / 5334560) : Real) := by
      calc
        10 ^ ((235 / 154 : Real) * (5 / 4 : Real)) *
              X ^ ((23 / 80 : Real) *
                ((235 / 154 : Real) * (5 / 4 : Real) - 1)) *
              X ^ ((59 / 433 : Real) * (5 / 4 : Real) + 23 / 80) =
            10 ^ ((235 / 154 : Real) * (5 / 4 : Real)) *
              (X ^ ((23 / 80 : Real) *
                  ((235 / 154 : Real) * (5 / 4 : Real) - 1)) *
                X ^ ((59 / 433 : Real) * (5 / 4 : Real) + 23 / 80)) := by ring
        _ = 10 ^ ((235 / 154 : Real) * (5 / 4 : Real)) *
            X ^ ((23 / 80 : Real) *
                  ((235 / 154 : Real) * (5 / 4 : Real) - 1) +
                ((59 / 433 : Real) * (5 / 4 : Real) + 23 / 80)) := by
          rw [← Real.rpow_add hX]
        _ = 10 ^ ((235 / 154 : Real) * (5 / 4 : Real)) *
            X ^ (23 / 32 - (5 / 4) * (127 / 5334560) : Real) := by
          congr 2
          norm_num

/-- The first source power divided by `N^2` has the claimed saving. -/
theorem anglesGeneratingLines_first_N_factor_bound
    (X N : Real) (hX : 0 < X) (hN : X ^ (9 / 25 : Real) <= N) :
    X ^ (23 / 32 - (5 / 4) * (127 / 5334560) : Real) / N ^ 2 <=
      X ^ (-anglesGeneratingLinesFirstSaving) := by
  have hNpos : 0 < N := (Real.rpow_pos_of_pos hX _).trans_le hN
  have hNpow : X ^ (18 / 25 : Real) <= N ^ 2 := by
    calc
      X ^ (18 / 25 : Real) = X ^ ((9 / 25 : Real) * 2) := by norm_num
      _ = (X ^ (9 / 25 : Real)) ^ (2 : Real) :=
        Real.rpow_mul hX.le _ _
      _ = (X ^ (9 / 25 : Real)) ^ 2 :=
        Real.rpow_natCast _ 2
      _ <= N ^ 2 := pow_le_pow_left₀ (Real.rpow_nonneg hX.le _) hN 2
  calc
    X ^ (23 / 32 - (5 / 4) * (127 / 5334560) : Real) / N ^ 2 <=
        X ^ (23 / 32 - (5 / 4) * (127 / 5334560) : Real) /
          X ^ (18 / 25 : Real) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hX.le _)
        (Real.rpow_pos_of_pos hX _) hNpow
    _ = X ^ ((23 / 32 - (5 / 4) * (127 / 5334560) : Real) -
        18 / 25) := (Real.rpow_sub hX _ _).symm
    _ = X ^ (-anglesGeneratingLinesFirstSaving) := by
      congr 1
      norm_num [anglesGeneratingLinesFirstSaving]

/-- The second bracket in the large-`N*K` branch. -/
theorem anglesGeneratingLines_second_band_factor_bound
    (X B H R : Real) (hX : 0 < X) (hB : 0 < B)
    (hBupper : B <= X ^ (23 / 80 : Real))
    (hH : 0 <= H)
    (hHbound : H <=
      (10 * B) ^ (235 / 154 : Real) * X ^ (59 / 433 : Real))
    (hR : 0 <= R) (hRupper : R <= B * X ^ (23 / 80 : Real)) :
    H ^ (3 / 2 : Real) / B ^ 2 / X ^ (1 / 2 : Real) * R ^ 2 <=
      10 ^ ((235 / 154 : Real) * (3 / 2 : Real)) *
        X ^ (15 / 16 - (3 / 2) * (127 / 5334560) : Real) := by
  have hHpow := comparableBandMomentPower_le X B H (3 / 2 : Real)
    hX hB hH (by norm_num) hHbound
  have hRpow : R ^ 2 <= (B * X ^ (23 / 80 : Real)) ^ 2 :=
    pow_le_pow_left₀ hR hRupper 2
  have hBpow :
      B ^ ((235 / 154 : Real) * (3 / 2 : Real)) <=
        X ^ ((23 / 80 : Real) *
          ((235 / 154 : Real) * (3 / 2 : Real))) := by
    calc
      B ^ ((235 / 154 : Real) * (3 / 2 : Real)) <=
          (X ^ (23 / 80 : Real)) ^
            ((235 / 154 : Real) * (3 / 2 : Real)) :=
        Real.rpow_le_rpow hB.le hBupper (by norm_num)
      _ = X ^ ((23 / 80 : Real) *
          ((235 / 154 : Real) * (3 / 2 : Real))) := by
        rw [← Real.rpow_mul hX.le]
  have hXsquare :
      (X ^ (23 / 80 : Real)) ^ 2 = X ^ (2 * (23 / 80 : Real)) := by
    calc
      (X ^ (23 / 80 : Real)) ^ 2 =
          (X ^ (23 / 80 : Real)) ^ (2 : Real) :=
        (Real.rpow_natCast _ 2).symm
      _ = X ^ ((23 / 80 : Real) * 2) :=
        (Real.rpow_mul hX.le _ _).symm
      _ = X ^ (2 * (23 / 80 : Real)) := by
        congr 1
        ring
  have hXpart :
      X ^ ((59 / 433 : Real) * (3 / 2 : Real)) /
          X ^ (1 / 2 : Real) *
            (X ^ (23 / 80 : Real)) ^ 2 =
        X ^ ((59 / 433 : Real) * (3 / 2 : Real) - 1 / 2 +
          2 * (23 / 80 : Real)) := by
    rw [← Real.rpow_sub hX, hXsquare]
    rw [← Real.rpow_add hX]
  calc
    H ^ (3 / 2 : Real) / B ^ 2 / X ^ (1 / 2 : Real) * R ^ 2 <=
        H ^ (3 / 2 : Real) / B ^ 2 / X ^ (1 / 2 : Real) *
          (B * X ^ (23 / 80 : Real)) ^ 2 := by gcongr
    _ <=
        (10 ^ ((235 / 154 : Real) * (3 / 2 : Real)) *
              B ^ ((235 / 154 : Real) * (3 / 2 : Real)) *
                X ^ ((59 / 433 : Real) * (3 / 2 : Real))) /
            B ^ 2 / X ^ (1 / 2 : Real) *
          (B * X ^ (23 / 80 : Real)) ^ 2 := by gcongr
    _ = 10 ^ ((235 / 154 : Real) * (3 / 2 : Real)) *
        B ^ ((235 / 154 : Real) * (3 / 2 : Real)) *
          X ^ ((59 / 433 : Real) * (3 / 2 : Real) - 1 / 2 +
            2 * (23 / 80 : Real)) := by
      rw [show (B * X ^ (23 / 80 : Real)) ^ 2 =
          B ^ 2 * (X ^ (23 / 80 : Real)) ^ 2 by ring]
      rw [show
        (10 ^ ((235 / 154 : Real) * (3 / 2 : Real)) *
              B ^ ((235 / 154 : Real) * (3 / 2 : Real)) *
                X ^ ((59 / 433 : Real) * (3 / 2 : Real))) /
            B ^ 2 / X ^ (1 / 2 : Real) *
              (B ^ 2 * (X ^ (23 / 80 : Real)) ^ 2) =
          10 ^ ((235 / 154 : Real) * (3 / 2 : Real)) *
            B ^ ((235 / 154 : Real) * (3 / 2 : Real)) *
              (X ^ ((59 / 433 : Real) * (3 / 2 : Real)) /
                X ^ (1 / 2 : Real) *
                  (X ^ (23 / 80 : Real)) ^ 2) by field_simp]
      rw [hXpart]
    _ <= 10 ^ ((235 / 154 : Real) * (3 / 2 : Real)) *
        X ^ ((23 / 80 : Real) *
            ((235 / 154 : Real) * (3 / 2 : Real))) *
          X ^ ((59 / 433 : Real) * (3 / 2 : Real) - 1 / 2 +
            2 * (23 / 80 : Real)) := by gcongr
    _ = 10 ^ ((235 / 154 : Real) * (3 / 2 : Real)) *
        X ^ (15 / 16 - (3 / 2) * (127 / 5334560) : Real) := by
      calc
        10 ^ ((235 / 154 : Real) * (3 / 2 : Real)) *
              X ^ ((23 / 80 : Real) *
                ((235 / 154 : Real) * (3 / 2 : Real))) *
              X ^ ((59 / 433 : Real) * (3 / 2 : Real) - 1 / 2 +
                2 * (23 / 80 : Real)) =
            10 ^ ((235 / 154 : Real) * (3 / 2 : Real)) *
              (X ^ ((23 / 80 : Real) *
                  ((235 / 154 : Real) * (3 / 2 : Real))) *
                X ^ ((59 / 433 : Real) * (3 / 2 : Real) - 1 / 2 +
                  2 * (23 / 80 : Real))) := by ring
        _ = 10 ^ ((235 / 154 : Real) * (3 / 2 : Real)) *
            X ^ ((23 / 80 : Real) *
                  ((235 / 154 : Real) * (3 / 2 : Real)) +
                ((59 / 433 : Real) * (3 / 2 : Real) - 1 / 2 +
                  2 * (23 / 80 : Real))) := by
          rw [← Real.rpow_add hX]
        _ = 10 ^ ((235 / 154 : Real) * (3 / 2 : Real)) *
            X ^ (15 / 16 - (3 / 2) * (127 / 5334560) : Real) := by
          congr 2
          norm_num

/-- The second source power divided by `N^3` has the stronger saving. -/
theorem anglesGeneratingLines_second_N_factor_bound
    (X N : Real) (hX : 0 < X) (hN : X ^ (9 / 25 : Real) <= N) :
    X ^ (15 / 16 - (3 / 2) * (127 / 5334560) : Real) / N ^ 3 <=
      X ^ (-anglesGeneratingLinesSecondSaving) := by
  have hNpow : X ^ (27 / 25 : Real) <= N ^ 3 := by
    calc
      X ^ (27 / 25 : Real) = X ^ ((9 / 25 : Real) * 3) := by norm_num
      _ = (X ^ (9 / 25 : Real)) ^ (3 : Real) :=
        Real.rpow_mul hX.le _ _
      _ = (X ^ (9 / 25 : Real)) ^ 3 :=
        Real.rpow_natCast _ 3
      _ <= N ^ 3 := pow_le_pow_left₀ (Real.rpow_nonneg hX.le _) hN 3
  calc
    X ^ (15 / 16 - (3 / 2) * (127 / 5334560) : Real) / N ^ 3 <=
        X ^ (15 / 16 - (3 / 2) * (127 / 5334560) : Real) /
          X ^ (27 / 25 : Real) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hX.le _)
        (Real.rpow_pos_of_pos hX _) hNpow
    _ = X ^ ((15 / 16 - (3 / 2) * (127 / 5334560) : Real) -
        27 / 25) := (Real.rpow_sub hX _ _).symm
    _ = X ^ (-anglesGeneratingLinesSecondSaving) := by
      congr 1
      norm_num [anglesGeneratingLinesSecondSaving]

end PrimesRestrictedDigits
