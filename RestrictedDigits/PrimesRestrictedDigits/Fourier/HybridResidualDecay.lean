import PrimesRestrictedDigits.Fourier.RationalPowerCertificate

/-!
# Residual Denominator Decay

This file kernel-checks the scalar exponent conversion used in equation
(10.16) of Maynard's Lemma 10.7. See `MAYNARD-PRD-PUBLISHED`, pp. 184--185.
-/

namespace PrimesRestrictedDigits

/-- The denominator exponent used in the residual square sampler. -/
noncomputable def hybridResidualDecay : Real := 20 / 21

/-- The complementary growth exponent in the first residual branch. -/
noncomputable def hybridResidualGrowth : Real := 1 / 21

/-- Half the residual decay exponent, used after the square-scale bridge. -/
noncomputable def hybridResidualHalfDecay : Real := 10 / 21

theorem hybridResidualDecay_nonneg : 0 <= hybridResidualDecay := by
  norm_num [hybridResidualDecay]

theorem hybridResidualGrowth_eq_one_sub_decay :
    hybridResidualGrowth = 1 - hybridResidualDecay := by
  norm_num [hybridResidualGrowth, hybridResidualDecay]

theorem hybridResidualDecay_eq_two_mul_halfDecay :
    hybridResidualDecay = 2 * hybridResidualHalfDecay := by
  norm_num [hybridResidualDecay, hybridResidualHalfDecay]

theorem ten_rpow_hybridResidualDecay_le_nine :
    (10 : Real) ^ hybridResidualDecay <= 9 := by
  change (10 : Real) ^ ((20 : Real) / 21) <= 9
  apply (rpow_nat_div_nat_le_iff_pow_le (x := (10 : Real))
    (q := (9 : Real)) 20 21 (by norm_num) (by norm_num) (by norm_num)).2
  norm_num

theorem decimalPower_rpow_hybridResidualDecay_le_nine_pow (r : Nat) :
    (((10 ^ r : Nat) : Real) ^ hybridResidualDecay) <=
      (9 : Real) ^ r := by
  have hbase := ten_rpow_hybridResidualDecay_le_nine
  have hpow :
      ((10 : Real) ^ hybridResidualDecay) ^ r <= (9 : Real) ^ r :=
    pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _) hbase r
  calc
    (((10 ^ r : Nat) : Real) ^ hybridResidualDecay) =
        (((10 : Real) ^ r) ^ hybridResidualDecay) := by
      norm_num [Nat.cast_pow]
    _ = (10 : Real) ^ ((r : Real) * hybridResidualDecay) := by
      rw [Real.rpow_natCast_mul (by norm_num : (0 : Real) <= 10)]
    _ = (10 : Real) ^ (hybridResidualDecay * (r : Real)) := by
      rw [mul_comm]
    _ = ((10 : Real) ^ hybridResidualDecay) ^ (r : Real) :=
      Real.rpow_mul (by norm_num) _ _
    _ = ((10 : Real) ^ hybridResidualDecay) ^ r :=
      Real.rpow_natCast _ _
    _ <= (9 : Real) ^ r := hpow

private theorem rpow_neg_le_rpow_mul_of_le_mul
    {x y C a : Real} (hx : 0 < x) (_hy : 0 < y) (hC : 0 < C)
    (ha : 0 <= a) (hxy : x <= C * y) :
    y ^ (-a) <= C ^ a * x ^ (-a) := by
  have hdiv : x / C <= y := (div_le_iff₀ hC).2 (by simpa [mul_comm] using hxy)
  have hreverse : y ^ (-a) <= (x / C) ^ (-a) :=
    Real.rpow_le_rpow_of_nonpos (div_pos hx hC) hdiv (neg_nonpos.mpr ha)
  calc
    y ^ (-a) <= (x / C) ^ (-a) := hreverse
    _ = C ^ a * x ^ (-a) := by
      rw [Real.div_rpow hx.le hC.le]
      rw [Real.rpow_neg hx.le, Real.rpow_neg hC.le]
      rw [div_inv_eq_mul, mul_comm]

theorem hybridResidual_denominator_le_min_branches
    {P V C : Real} (hP : 0 < P) (hV : 0 < V) (hC : 0 < C)
    (r : Nat)
    (hprefix : min V P <= C * ((10 ^ r : Nat) : Real)) :
    P / (9 : Real) ^ r <=
      C ^ hybridResidualDecay *
        (P ^ hybridResidualGrowth + P * V ^ (-hybridResidualDecay)) := by
  let R : Real := ((10 ^ r : Nat) : Real)
  have hR : 0 < R := by dsimp [R]; positivity
  have hRpow : R ^ hybridResidualDecay <= (9 : Real) ^ r := by
    simpa [R] using decimalPower_rpow_hybridResidualDecay_le_nine_pow r
  have hdenR : 0 < R ^ hybridResidualDecay :=
    Real.rpow_pos_of_pos hR _
  have hfirst : P / (9 : Real) ^ r <= P / R ^ hybridResidualDecay :=
    div_le_div_of_nonneg_left hP.le hdenR hRpow
  have hdecay := hybridResidualDecay_nonneg
  have hCpow : 0 <= C ^ hybridResidualDecay :=
    Real.rpow_nonneg hC.le _
  have hPpower : 0 <= P ^ hybridResidualGrowth :=
    Real.rpow_nonneg hP.le _
  have hVpower : 0 <= V ^ (-hybridResidualDecay) :=
    Real.rpow_nonneg hV.le _
  rcases le_total P V with hPV | hVP
  · have hmin : min V P = P := min_eq_right hPV
    have hPR : P <= C * R := by simpa [hmin, R] using hprefix
    have hneg := rpow_neg_le_rpow_mul_of_le_mul hP hR hC hdecay hPR
    have hmul : P * R ^ (-hybridResidualDecay) <=
        P * (C ^ hybridResidualDecay * P ^ (-hybridResidualDecay)) :=
      mul_le_mul_of_nonneg_left hneg hP.le
    calc
      P / (9 : Real) ^ r <= P / R ^ hybridResidualDecay := hfirst
      _ = P * R ^ (-hybridResidualDecay) := by
        rw [Real.rpow_neg hR.le]
        rw [div_eq_mul_inv]
      _ <= P * (C ^ hybridResidualDecay * P ^ (-hybridResidualDecay)) := hmul
      _ = C ^ hybridResidualDecay * P ^ hybridResidualGrowth := by
        rw [show hybridResidualGrowth = 1 + (-hybridResidualDecay) by
          rw [hybridResidualGrowth_eq_one_sub_decay]
          ring_nf]
        rw [Real.rpow_add hP]
        rw [Real.rpow_one]
        ring_nf
      _ <= C ^ hybridResidualDecay *
          (P ^ hybridResidualGrowth + P * V ^ (-hybridResidualDecay)) := by
        exact mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right (mul_nonneg hP.le hVpower)) hCpow
  · have hmin : min V P = V := min_eq_left hVP
    have hVR : V <= C * R := by simpa [hmin, R] using hprefix
    have hneg := rpow_neg_le_rpow_mul_of_le_mul hV hR hC hdecay hVR
    have hmul : P * R ^ (-hybridResidualDecay) <=
        P * (C ^ hybridResidualDecay * V ^ (-hybridResidualDecay)) :=
      mul_le_mul_of_nonneg_left hneg hP.le
    calc
      P / (9 : Real) ^ r <= P / R ^ hybridResidualDecay := hfirst
      _ = P * R ^ (-hybridResidualDecay) := by
        rw [Real.rpow_neg hR.le]
        rw [div_eq_mul_inv]
      _ <= P * (C ^ hybridResidualDecay * V ^ (-hybridResidualDecay)) := hmul
      _ = C ^ hybridResidualDecay *
          (P * V ^ (-hybridResidualDecay)) := by ring_nf
      _ <= C ^ hybridResidualDecay *
          (P ^ hybridResidualGrowth + P * V ^ (-hybridResidualDecay)) := by
        exact mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_left hPpower) hCpow

theorem hybridResidual_squareScale_neg_decay_le
    {V Z : Real} (hV : 0 < V) (hZ : 0 < Z)
    (hscale : Z <= 10 * V ^ 2) :
    V ^ (-hybridResidualDecay) <=
      (10 : Real) ^ hybridResidualHalfDecay *
        Z ^ (-hybridResidualHalfDecay) := by
  have hhalf : 0 <= hybridResidualHalfDecay := by
    norm_num [hybridResidualHalfDecay]
  have hsquare : 0 < V ^ 2 := sq_pos_of_pos hV
  have hraw := rpow_neg_le_rpow_mul_of_le_mul
    hZ hsquare (by norm_num : (0 : Real) < 10) hhalf hscale
  calc
    V ^ (-hybridResidualDecay) =
        V ^ ((2 : Real) * (-hybridResidualHalfDecay)) := by
      rw [hybridResidualDecay_eq_two_mul_halfDecay]
      congr 1
      ring
    _ = (V ^ (2 : Real)) ^ (-hybridResidualHalfDecay) :=
      Real.rpow_mul hV.le _ _
    _ = (V ^ (2 : Nat)) ^ (-hybridResidualHalfDecay) := by
      congr 1
      exact Real.rpow_natCast V 2
    _ <= (10 : Real) ^ hybridResidualHalfDecay *
        Z ^ (-hybridResidualHalfDecay) := hraw

theorem hybridResidual_denominator_le_source_branches
    {P V Z C : Real} (hP : 0 < P) (hV : 0 < V) (hZ : 0 < Z)
    (hC : 0 < C) (r : Nat)
    (hprefix : min V P <= C * ((10 ^ r : Nat) : Real))
    (hscale : Z <= 10 * V ^ 2) :
    P / (9 : Real) ^ r <=
      C ^ hybridResidualDecay *
        (P ^ hybridResidualGrowth +
          (10 : Real) ^ hybridResidualHalfDecay *
            P * Z ^ (-hybridResidualHalfDecay)) := by
  have hfirst := hybridResidual_denominator_le_min_branches
    hP hV hC r hprefix
  have hsquare := hybridResidual_squareScale_neg_decay_le hV hZ hscale
  have hPmul :
      P * V ^ (-hybridResidualDecay) <=
        P * ((10 : Real) ^ hybridResidualHalfDecay *
          Z ^ (-hybridResidualHalfDecay)) :=
    mul_le_mul_of_nonneg_left hsquare hP.le
  have hinside :
      P ^ hybridResidualGrowth + P * V ^ (-hybridResidualDecay) <=
        P ^ hybridResidualGrowth +
          (10 : Real) ^ hybridResidualHalfDecay *
            P * Z ^ (-hybridResidualHalfDecay) := by
    calc
      P ^ hybridResidualGrowth + P * V ^ (-hybridResidualDecay) <=
          P ^ hybridResidualGrowth +
            P * ((10 : Real) ^ hybridResidualHalfDecay *
              Z ^ (-hybridResidualHalfDecay)) := add_le_add le_rfl hPmul
      _ = _ := by ring_nf
  exact hfirst.trans (mul_le_mul_of_nonneg_left hinside
    (Real.rpow_nonneg hC.le _))

theorem hybridResidual_denominator_le_source_branches_of_hundred
    {P V Z : Real} (hP : 0 < P) (hV : 0 < V) (hZ : 0 < Z)
    (r : Nat)
    (hprefix : min V P <= 100 * ((10 ^ r : Nat) : Real))
    (hscale : Z <= 10 * V ^ 2) :
    P / (9 : Real) ^ r <=
      1000 *
        (P ^ hybridResidualGrowth +
          P * Z ^ (-hybridResidualHalfDecay)) := by
  have hsharp := hybridResidual_denominator_le_source_branches
    hP hV hZ (by norm_num : (0 : Real) < 100) r hprefix hscale
  have hdecayLe : hybridResidualDecay <= 1 := by
    norm_num [hybridResidualDecay]
  have hhalfLe : hybridResidualHalfDecay <= 1 := by
    norm_num [hybridResidualHalfDecay]
  have hhundred : (100 : Real) ^ hybridResidualDecay <= 100 := by
    calc
      (100 : Real) ^ hybridResidualDecay <= (100 : Real) ^ (1 : Real) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hdecayLe
      _ = 100 := Real.rpow_one 100
  have hten : (10 : Real) ^ hybridResidualHalfDecay <= 10 := by
    calc
      (10 : Real) ^ hybridResidualHalfDecay <= (10 : Real) ^ (1 : Real) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hhalfLe
      _ = 10 := Real.rpow_one 10
  let first := P ^ hybridResidualGrowth
  let second := P * Z ^ (-hybridResidualHalfDecay)
  have hfirst : 0 <= first := by dsimp [first]; positivity
  have hsecond : 0 <= second := by dsimp [second]; positivity
  have hinside :
      first + (10 : Real) ^ hybridResidualHalfDecay * second <=
        first + 10 * second := add_le_add le_rfl
      (mul_le_mul_of_nonneg_right hten hsecond)
  calc
    P / (9 : Real) ^ r <=
        (100 : Real) ^ hybridResidualDecay *
          (first + (10 : Real) ^ hybridResidualHalfDecay * second) := by
      simpa [first, second, mul_assoc] using hsharp
    _ <= (100 : Real) *
        (first + (10 : Real) ^ hybridResidualHalfDecay * second) :=
      mul_le_mul_of_nonneg_right hhundred
        (add_nonneg hfirst (mul_nonneg (by positivity) hsecond))
    _ <= 100 * (first + 10 * second) :=
      mul_le_mul_of_nonneg_left hinside (by norm_num)
    _ <= 1000 * (first + second) := by nlinarith
    _ = _ := by rfl

end PrimesRestrictedDigits
