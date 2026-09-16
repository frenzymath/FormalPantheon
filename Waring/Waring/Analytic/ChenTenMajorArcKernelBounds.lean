import Waring.Analytic.ChenTenOscillatoryIntegral
import Waring.Analytic.ChenTenMajorArcIntegration

/-!
# Decay-weighted pointwise bounds on Chen's major arcs

This file combines the complete fifth-power sum estimate, the checked `6q`
residue approximation, and the oscillatory kernel bound.  It gives the two
pointwise envelopes used to integrate the central and outer portions of each
major arc.
-/

namespace Waring.Analytic

open Set

noncomputable section

/-- A bound `Z` for the perturbation integral gives the modeled Weyl sum the
bound `40 * q^(-1/5) * Z`. -/
theorem norm_chenTenMajorArcWeylModel_le_kernel
    {P : Nat} (i : ChenTenArcIndex P) (z Z : Real)
    (hpsi : ‖fifthPerturbationIntegral z P‖ <= Z) :
    ‖chenTenMajorArcWeylModel P i z‖ <=
      40 * (i.denominator : Real) ^ (-1 / 5 : Real) * Z := by
  have hq : (0 : Real) < i.denominator := by
    exact_mod_cast i.denominator_pos
  have hcomplete := chen_two_completePowerSum_bound
    (i.numerator : ZMod i.denominator) i.numerator_isUnit
  unfold chenTenMajorArcWeylModel
  calc
    ‖(i.denominator : Complex)⁻¹ *
          completePowerSum 5 (i.numerator : ZMod i.denominator) *
          fifthPerturbationIntegral z P‖ =
        (i.denominator : Real)⁻¹ *
          ‖completePowerSum 5 (i.numerator : ZMod i.denominator)‖ *
          ‖fifthPerturbationIntegral z P‖ := by
      rw [norm_mul, norm_mul, norm_inv, Complex.norm_natCast]
    _ <= (i.denominator : Real)⁻¹ *
          (40 * (i.denominator : Real) ^ (4 / 5 : Real)) * Z := by
      gcongr
    _ = 40 * (i.denominator : Real) ^ (-1 / 5 : Real) * Z := by
      rw [← Real.rpow_neg_one]
      rw [show (-1 / 5 : Real) = (-1 : Real) + 4 / 5 by norm_num]
      rw [Real.rpow_add hq]
      ring

/-- If the denominator error can be absorbed into the kernel scale, the
translated fifteenth-power error has the common `q^(-9/5) * Z^14` envelope. -/
theorem norm_chenTenRepresentationIntegrand_sub_model_le_of_kernel_bound
    {P : Nat} (hP : 1 <= P) (N : Nat) (i : ChenTenArcIndex P)
    (z Z : Real) (hZ : 0 <= Z)
    (hz : z ∈ Set.Icc (-chenTenMajorArcRadius P i)
      (chenTenMajorArcRadius P i))
    (hpsi : ‖fifthPerturbationIntegral z P‖ <= Z)
    (habsorb : (i.denominator : Real) <=
      (i.denominator : Real) ^ (-1 / 5 : Real) * Z) :
    ‖chenTenRepresentationIntegrand P N
          (chenTenMajorArcCenter i + z) -
        chenTenMajorArcModelIntegrand P N i z‖ <=
      (90 * 46 ^ 14 : Real) *
        (i.denominator : Real) ^ (-9 / 5 : Real) * Z ^ 14 := by
  let Q : Real := (i.denominator : Real) ^ (-1 / 5 : Real) * Z
  have hQ : 0 <= Q := mul_nonneg (Real.rpow_nonneg (by positivity) _) hZ
  have hmodel : ‖chenTenMajorArcWeylModel P i z‖ <= 40 * Q := by
    simpa [Q, mul_assoc] using
      norm_chenTenMajorArcWeylModel_le_kernel i z Z hpsi
  have happrox :=
    norm_fifthPowerExponentialSum_sub_chenTenMajorArcWeylModel_le
      (Nat.zero_lt_of_lt hP) i z hz
  have hactual :
      ‖fifthPowerExponentialSum P (chenTenMajorArcCenter i + z)‖ <=
        46 * Q := by
    calc
      ‖fifthPowerExponentialSum P (chenTenMajorArcCenter i + z)‖ <=
          ‖chenTenMajorArcWeylModel P i z‖ +
            ‖fifthPowerExponentialSum P (chenTenMajorArcCenter i + z) -
              chenTenMajorArcWeylModel P i z‖ :=
        norm_le_norm_add_norm_sub' _ _
      _ <= 40 * Q + 6 * (i.denominator : Real) :=
        add_le_add hmodel happrox
      _ <= 40 * Q + 6 * Q := by
        gcongr
      _ = 46 * Q := by ring
  have hmodel46 : ‖chenTenMajorArcWeylModel P i z‖ <= 46 * Q := by
    calc
      _ <= 40 * Q := hmodel
      _ <= 46 * Q := by
        gcongr
        norm_num
  have hfactor := norm_fifteenthPowerDifferenceFactor_le
    (fifthPowerExponentialSum P (chenTenMajorArcCenter i + z))
    (chenTenMajorArcWeylModel P i z) (46 * Q) (by positivity)
    hactual hmodel46
  calc
    ‖chenTenRepresentationIntegrand P N
          (chenTenMajorArcCenter i + z) -
        chenTenMajorArcModelIntegrand P N i z‖ <=
        (6 * (i.denominator : Real)) *
          ‖fifteenthPowerDifferenceFactor
            (fifthPowerExponentialSum P
              (chenTenMajorArcCenter i + z))
            (chenTenMajorArcWeylModel P i z)‖ :=
      norm_chenTenRepresentationIntegrand_sub_modelIntegrand_le
        hP N i z hz
    _ <= (6 * (i.denominator : Real)) *
          (15 * (46 * Q) ^ 14) := by gcongr
    _ = (90 * 46 ^ 14 : Real) *
        (i.denominator : Real) ^ (-9 / 5 : Real) * Z ^ 14 := by
      dsimp [Q]
      have hq : (0 : Real) < i.denominator := by
        exact_mod_cast i.denominator_pos
      have hqpow :
          ((i.denominator : Real) ^ (-1 / 5 : Real)) ^ (14 : Nat) =
            (i.denominator : Real) ^ (-14 / 5 : Real) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le]
        norm_num
      have hqcombine :
          (i.denominator : Real) *
              (i.denominator : Real) ^ (-14 / 5 : Real) =
            (i.denominator : Real) ^ (-9 / 5 : Real) := by
        conv_lhs =>
          lhs
          rw [← Real.rpow_one (i.denominator : Real)]
        rw [← Real.rpow_add hq]
        norm_num
      simp only [mul_pow]
      rw [hqpow]
      ring_nf
      rw [hqcombine]
      ring

private theorem denominator_rpow_six_fifths_le_P
    {P : Nat} (hP : 1 <= P) (i : ChenTenArcIndex P) :
    (i.denominator : Real) ^ (6 / 5 : Real) <= P := by
  have hq : (0 : Real) < i.denominator := by
    exact_mod_cast i.denominator_pos
  have hPR : (1 : Real) <= P := by exact_mod_cast hP
  calc
    (i.denominator : Real) ^ (6 / 5 : Real) =
        ((i.denominator : Real) ^ 2) ^ (3 / 5 : Real) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hq.le]
      norm_num
    _ <= (P : Real) ^ (3 / 5 : Real) := by
      exact Real.rpow_le_rpow (sq_nonneg _) i.denominator_sq_le_real
        (by norm_num)
    _ <= (P : Real) ^ (1 : Real) := by
      exact Real.rpow_le_rpow_of_exponent_le hPR (by norm_num)
    _ = P := Real.rpow_one _

private theorem inv_rpow_neg_one_fifth {x : Real} (hx : 0 < x) :
    x⁻¹ ^ (-1 / 5 : Real) = x ^ (1 / 5 : Real) := by
  rw [show (-1 / 5 : Real) = -(1 / 5) by ring,
    Real.rpow_neg (inv_nonneg.mpr hx.le), Real.inv_rpow hx.le]
  simp

private theorem denominator_rpow_six_fifths_le_P_three_fifths
    {P : Nat} (i : ChenTenArcIndex P) :
    (i.denominator : Real) ^ (6 / 5 : Real) <=
      (P : Real) ^ (3 / 5 : Real) := by
  have hq : (0 : Real) < i.denominator := by
    exact_mod_cast i.denominator_pos
  calc
    (i.denominator : Real) ^ (6 / 5 : Real) =
        ((i.denominator : Real) ^ 2) ^ (3 / 5 : Real) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hq.le]
      norm_num
    _ <= (P : Real) ^ (3 / 5 : Real) := by
      exact Real.rpow_le_rpow (sq_nonneg _) i.denominator_sq_le_real
        (by norm_num)

private theorem denominator_rpow_six_fifths_le_two_abs_rpow
    {P : Nat} (hP : 1 <= P) (i : ChenTenArcIndex P) (z : Real)
    (hz0 : z ≠ 0)
    (hz : z ∈ Set.Icc (-chenTenMajorArcRadius P i)
      (chenTenMajorArcRadius P i)) :
    (i.denominator : Real) ^ (6 / 5 : Real) <=
      2 * |z| ^ (-1 / 5 : Real) := by
  have hqOne : (1 : Real) <= i.denominator := by
    exact_mod_cast i.denominator_pos
  have hPR : (1 : Real) <= P := by exact_mod_cast hP
  have hzabs : |z| <= chenTenMajorArcRadius P i := (abs_le).2 hz
  rw [chenTenMajorArcRadius_eq_pointwiseRadius] at hzabs
  let D : Real := 10 * (i.denominator : Real) * (P : Real) ^ 4
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hzpos : 0 < |z| := abs_pos.mpr hz0
  have hzinv : |z| <= D⁻¹ := by
    simpa only [D, one_div] using hzabs
  have hdecay : D ^ (1 / 5 : Real) <= |z| ^ (-1 / 5 : Real) := by
    rw [← inv_rpow_neg_one_fifth hD]
    exact Real.rpow_le_rpow_of_nonpos hzpos hzinv (by norm_num)
  have hPfour :
      (P : Real) ^ (4 / 5 : Real) <= D ^ (1 / 5 : Real) := by
    have hPD : (P : Real) ^ 4 <= D := by
      dsimp [D]
      have hcoef : (1 : Real) <= 10 * (i.denominator : Real) := by
        nlinarith [hqOne]
      calc
        (P : Real) ^ 4 = 1 * (P : Real) ^ 4 := by ring
        _ <= (10 * (i.denominator : Real)) * (P : Real) ^ 4 := by
          gcongr
        _ = D := by ring
    calc
      (P : Real) ^ (4 / 5 : Real) =
          ((P : Real) ^ 4) ^ (1 / 5 : Real) := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul (by positivity : (0 : Real) <= P)]
        norm_num
      _ <= D ^ (1 / 5 : Real) :=
        Real.rpow_le_rpow (by positivity) hPD (by norm_num)
  calc
    (i.denominator : Real) ^ (6 / 5 : Real) <=
        (P : Real) ^ (3 / 5 : Real) :=
      denominator_rpow_six_fifths_le_P_three_fifths i
    _ <= (P : Real) ^ (4 / 5 : Real) :=
      Real.rpow_le_rpow_of_exponent_le hPR (by norm_num)
    _ <= D ^ (1 / 5 : Real) := hPfour
    _ <= |z| ^ (-1 / 5 : Real) := hdecay
    _ <= 2 * |z| ^ (-1 / 5 : Real) := by
      nlinarith [Real.rpow_nonneg (abs_nonneg z) (-1 / 5 : Real)]

private theorem denominator_le_rpow_neg_one_fifth_mul_decay
    {P : Nat} (hP : 1 <= P) (i : ChenTenArcIndex P) (z : Real)
    (hz0 : z ≠ 0)
    (hz : z ∈ Set.Icc (-chenTenMajorArcRadius P i)
      (chenTenMajorArcRadius P i)) :
    (i.denominator : Real) <=
      (i.denominator : Real) ^ (-1 / 5 : Real) *
        (2 * |z| ^ (-1 / 5 : Real)) := by
  have hq : (0 : Real) < i.denominator := by
    exact_mod_cast i.denominator_pos
  have hpow := denominator_rpow_six_fifths_le_two_abs_rpow
    hP i z hz0 hz
  calc
    (i.denominator : Real) =
        (i.denominator : Real) ^ (-1 / 5 : Real) *
          (i.denominator : Real) ^ (6 / 5 : Real) := by
      rw [← Real.rpow_add hq]
      norm_num
    _ <= (i.denominator : Real) ^ (-1 / 5 : Real) *
        (2 * |z| ^ (-1 / 5 : Real)) := by
      gcongr

private theorem denominator_le_rpow_neg_one_fifth_mul_P
    {P : Nat} (hP : 1 <= P) (i : ChenTenArcIndex P) :
    (i.denominator : Real) <=
      (i.denominator : Real) ^ (-1 / 5 : Real) * P := by
  have hq : (0 : Real) < i.denominator := by
    exact_mod_cast i.denominator_pos
  have hpow := denominator_rpow_six_fifths_le_P hP i
  calc
    (i.denominator : Real) =
        (i.denominator : Real) ^ (-1 / 5 : Real) *
          (i.denominator : Real) ^ (6 / 5 : Real) := by
      rw [← Real.rpow_add hq]
      norm_num
    _ <= (i.denominator : Real) ^ (-1 / 5 : Real) * P := by
      gcongr

/-- On the central scale, the translated integrand error is bounded by
`90 * 46^14 * q^(-9/5) * P^14`. -/
theorem norm_chenTenRepresentationIntegrand_sub_modelIntegrand_le_central
    {P : Nat} (hP : 1 <= P) (N : Nat) (i : ChenTenArcIndex P)
    (z : Real)
    (hz : z ∈ Set.Icc (-chenTenMajorArcRadius P i)
      (chenTenMajorArcRadius P i)) :
    ‖chenTenRepresentationIntegrand P N
          (chenTenMajorArcCenter i + z) -
        chenTenMajorArcModelIntegrand P N i z‖ <=
      (90 * 46 ^ 14 : Real) *
        (i.denominator : Real) ^ (-9 / 5 : Real) * (P : Real) ^ 14 := by
  apply norm_chenTenRepresentationIntegrand_sub_model_le_of_kernel_bound
    hP N i z P (by positivity) hz
  · exact norm_fifthPerturbationIntegral_le z P
  · exact denominator_le_rpow_neg_one_fifth_mul_P hP i

/-- Away from the center, oscillatory decay gives the translated integrand
error the envelope `90 * 46^14 * q^(-9/5) * (2|z|^(-1/5))^14`. -/
theorem norm_chenTenRepresentationIntegrand_sub_modelIntegrand_le_outer
    {P : Nat} (hP : 1 <= P) (N : Nat) (i : ChenTenArcIndex P)
    (z : Real) (hz0 : z ≠ 0)
    (hz : z ∈ Set.Icc (-chenTenMajorArcRadius P i)
      (chenTenMajorArcRadius P i)) :
    ‖chenTenRepresentationIntegrand P N
          (chenTenMajorArcCenter i + z) -
        chenTenMajorArcModelIntegrand P N i z‖ <=
      (90 * 46 ^ 14 : Real) *
        (i.denominator : Real) ^ (-9 / 5 : Real) *
          (2 * |z| ^ (-1 / 5 : Real)) ^ 14 := by
  apply norm_chenTenRepresentationIntegrand_sub_model_le_of_kernel_bound
    hP N i z (2 * |z| ^ (-1 / 5 : Real)) (by positivity) hz
  · exact norm_fifthPerturbationIntegral_le_two_mul_abs_rpow z P hz0
  · exact denominator_le_rpow_neg_one_fifth_mul_decay hP i z hz0 hz

end

end Waring.Analytic
