import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserBoundedModelAbsorption

/-!
# Scalars for the upper Rosser cube-root continuation

This retains an explicit part of the bounded plus contraction at coordinate three and pays the
density transport on `1 < s < 3`.
-/

namespace PrimesRestrictedDigits

/-- The explicit bounded seed share is at least one. -/
theorem one_le_dimensionOneRosserBoundedSeedShare :
    1 <= dimensionOneRosserBoundedSeedShare := by
  have hU0 : 0 <= dimensionOneRosserSecondSplice :=
    zero_le_one.trans one_le_dimensionOneRosserSecondSplice
  have hCeiling : 1 <= dimensionOneRosserBoundedSeedCeiling := by
    unfold dimensionOneRosserBoundedSeedCeiling
    exact Real.one_le_exp (mul_nonneg (by norm_num) hU0)
  have hfloor := dimensionOneRosserBoundedDelayFloor_pos
  unfold dimensionOneRosserBoundedSeedShare
    dimensionOneRosserBoundedSeedConstant
  rw [show 4 * dimensionOneRosserBoundedSeedCeiling /
      dimensionOneRosserBoundedDelayFloor / 4 =
        dimensionOneRosserBoundedSeedCeiling /
          dimensionOneRosserBoundedDelayFloor by ring]
  apply (le_div_iff₀ hfloor).2
  simpa only [one_mul] using
    dimensionOneRosserBoundedDelayFloor_le_one.trans hCeiling

/-- With the global comparison `c <= D`, the bounded upper profile retains a
fixed fraction of its plus-delay share. -/
theorem dimensionOneRosserPlusBoundedRetainedProfile_le
    (R : Nat) {c D K L s s0 : Real}
    (hc : 0 <= c) (hD : 0 <= D) (hK : 0 <= K)
    (hs : 3 <= s)
    (hsUpper : s <= dimensionOneRosserSecondSplice)
    (hsplice : 2 * dimensionOneRosserSecondSplice <= s0)
    (hcap : s0 ^ 50 <= L) (hdom : 13824 * K <= s0 ^ 46)
    (hcD : c <= D)
    (hmodel : dimensionOneRosserModelMinusPartialSum R (s - 1) <=
      c * dimensionOneDelayScaledMinus (s - 1)) :
    (2 * K * s0 / (L * (1 - 1 / s))) *
          dimensionOneRosserModelMinusPartialSum R (s - 1) +
        D * ((1 - 1 / (2 * s0)) *
          (L ^ (-1 / 3 : Real) *
            dimensionOneRosserArtificialFactor L 0 s) *
          dimensionOneDelayScaledPlus s) +
        D * dimensionOneRosserBoundedSeedShare *
          ((1 - 11 / (12 * dimensionOneRosserSecondSplice)) *
            dimensionOneDelayScaledPlus s) <=
      D * dimensionOneRosserBoundedPlusMajorant L s -
        D * (dimensionOneRosserBoundedSeedShare /
          (2 * dimensionOneRosserSecondSplice) *
            dimensionOneDelayScaledPlus s) := by
  have hU : 0 < dimensionOneRosserSecondSplice := by
    linarith [three_lt_dimensionOneRosserSecondSplice]
  have hs0 : 0 < s0 := by linarith
  have hUs0 : s <= s0 := by
    linarith [hsUpper, hsplice, one_le_dimensionOneRosserSecondSplice]
  have hbase : 0 < 1 - 1 / s := by
    have hinv : 1 / s <= (1 / 3 : Real) :=
      one_div_le_one_div_of_le (by norm_num) hs
    linarith
  have hL : 0 < L := (pow_pos hs0 50).trans_le hcap
  have hcoefficient :
      0 <= 2 * K * s0 / (L * (1 - 1 / s)) := by positivity
  have hendpoint := dimensionOneRosserPlusUnscaledDelayEndpoint_le hK
    (by linarith : 2 <= s) hUs0 hcap hdom
  have hmodelEndpoint :
      (2 * K * s0 / (L * (1 - 1 / s))) *
          dimensionOneRosserModelMinusPartialSum R (s - 1) <=
        (c / (12 * s0)) * dimensionOneDelayScaledPlus s := by
    calc
      _ <= (2 * K * s0 / (L * (1 - 1 / s))) *
          (c * dimensionOneDelayScaledMinus (s - 1)) :=
        mul_le_mul_of_nonneg_left hmodel hcoefficient
      _ = c * ((2 * K * s0 / (L * (1 - 1 / s))) *
          dimensionOneDelayScaledMinus (s - 1)) := by ring
      _ <= c * ((1 / (12 * s0)) *
          dimensionOneDelayScaledPlus s) :=
        mul_le_mul_of_nonneg_left hendpoint hc
      _ = (c / (12 * s0)) * dimensionOneDelayScaledPlus s := by ring
  have hcDB : c <= D * dimensionOneRosserBoundedSeedShare := by
    calc
      c <= D := hcD
      _ = D * 1 := by ring
      _ <= D * dimensionOneRosserBoundedSeedShare :=
        mul_le_mul_of_nonneg_left
          one_le_dimensionOneRosserBoundedSeedShare hD
  have hendpointCoefficient :
      c / (12 * s0) <=
        D * dimensionOneRosserBoundedSeedShare /
          (24 * dimensionOneRosserSecondSplice) := by
    rw [div_le_div_iff₀ (by positivity : 0 < 12 * s0)
      (by positivity : 0 < 24 * dimensionOneRosserSecondSplice)]
    calc
      c * (24 * dimensionOneRosserSecondSplice) <=
          (D * dimensionOneRosserBoundedSeedShare) *
            (24 * dimensionOneRosserSecondSplice) :=
        mul_le_mul_of_nonneg_right hcDB (by positivity)
      _ <= (D * dimensionOneRosserBoundedSeedShare) * (12 * s0) :=
        mul_le_mul_of_nonneg_left (by nlinarith)
          (mul_nonneg hD dimensionOneRosserBoundedSeedShare_pos.le)
  have hcurrent : 0 <= dimensionOneDelayScaledPlus s :=
    (dimensionOneDelayScaledPlus_pos (by linarith)).le
  have hendpointReserve :
      (2 * K * s0 / (L * (1 - 1 / s))) *
          dimensionOneRosserModelMinusPartialSum R (s - 1) <=
        (D * dimensionOneRosserBoundedSeedShare /
          (24 * dimensionOneRosserSecondSplice)) *
            dimensionOneDelayScaledPlus s :=
    hmodelEndpoint.trans
      (mul_le_mul_of_nonneg_right hendpointCoefficient hcurrent)
  have hnormalized : 0 <=
      L ^ (-1 / 3 : Real) *
        dimensionOneRosserArtificialFactor L 0 s :=
    mul_nonneg (Real.rpow_pos_of_pos hL _).le (Real.exp_pos _).le
  have hnormalizedProduct : 0 <= D *
      (L ^ (-1 / 3 : Real) *
        dimensionOneRosserArtificialFactor L 0 s) *
          dimensionOneDelayScaledPlus s := by positivity
  have hnormalizedContract :
      D * ((1 - 1 / (2 * s0)) *
          (L ^ (-1 / 3 : Real) *
            dimensionOneRosserArtificialFactor L 0 s) *
          dimensionOneDelayScaledPlus s) <=
        D * (L ^ (-1 / 3 : Real) *
          dimensionOneRosserArtificialFactor L 0 s) *
            dimensionOneDelayScaledPlus s := by
    calc
      _ = (1 - 1 / (2 * s0)) *
          (D * (L ^ (-1 / 3 : Real) *
            dimensionOneRosserArtificialFactor L 0 s) *
              dimensionOneDelayScaledPlus s) := by ring
      _ <= 1 * (D * (L ^ (-1 / 3 : Real) *
          dimensionOneRosserArtificialFactor L 0 s) *
            dimensionOneDelayScaledPlus s) :=
        mul_le_mul_of_nonneg_right (by
          have : 0 <= 1 / (2 * s0) := by positivity
          linarith) hnormalizedProduct
      _ = _ := by ring
  calc
    _ <= (D * dimensionOneRosserBoundedSeedShare /
          (24 * dimensionOneRosserSecondSplice)) *
            dimensionOneDelayScaledPlus s +
        D * (L ^ (-1 / 3 : Real) *
          dimensionOneRosserArtificialFactor L 0 s) *
            dimensionOneDelayScaledPlus s +
        D * dimensionOneRosserBoundedSeedShare *
          ((1 - 11 / (12 * dimensionOneRosserSecondSplice)) *
            dimensionOneDelayScaledPlus s) :=
      add_le_add (add_le_add hendpointReserve hnormalizedContract) le_rfl
    _ = D * dimensionOneRosserBoundedPlusMajorant L s -
        D * (dimensionOneRosserBoundedSeedShare /
          (2 * dimensionOneRosserSecondSplice) *
            dimensionOneDelayScaledPlus s) -
        3 * D * dimensionOneRosserBoundedSeedShare /
          (8 * dimensionOneRosserSecondSplice) *
            dimensionOneDelayScaledPlus s := by
      unfold dimensionOneRosserBoundedPlusMajorant
        dimensionOneRosserBoundedSeedShare
      field_simp [hU.ne']
      ring
    _ <= D * dimensionOneRosserBoundedPlusMajorant L s -
        D * (dimensionOneRosserBoundedSeedShare /
          (2 * dimensionOneRosserSecondSplice) *
            dimensionOneDelayScaledPlus s) := by
      have hgap : 0 <= 3 * D * dimensionOneRosserBoundedSeedShare /
          (8 * dimensionOneRosserSecondSplice) *
            dimensionOneDelayScaledPlus s := by
        exact mul_nonneg (div_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) hD)
            dimensionOneRosserBoundedSeedShare_pos.le)
          (mul_nonneg (by norm_num) hU.le)) hcurrent
      linarith

/-- The factor-48 splice hypothesis gives the density coefficient needed at
the cube-root cutoff. -/
theorem dimensionOneRosserFixedSplice_K_div_level_le
    {K L : Real} (hL : 0 < L)
    (hfixed : 48 * K * dimensionOneRosserSecondSplice ^ 2 <=
      L * dimensionOneRosserBoundedDelayFloor) :
    K / L <= 1 / (48 * dimensionOneRosserSecondSplice ^ 2) := by
  have hU : 0 < dimensionOneRosserSecondSplice := by
    linarith [three_lt_dimensionOneRosserSecondSplice]
  have hLfloor : L * dimensionOneRosserBoundedDelayFloor <= L := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      dimensionOneRosserBoundedDelayFloor_le_one hL.le
  rw [div_le_div_iff₀ hL
    (by positivity : 0 < 48 * dimensionOneRosserSecondSplice ^ 2)]
  nlinarith [hfixed.trans hLfloor]

private theorem one_le_level_of_secondGrowth
    {L : Real} (hgrowth : dimensionOneRosserSecondLevelThreshold <= L) :
    1 <= L := by
  have hpow : 1 <= dimensionOneRosserSecondSplice ^ 52 :=
    one_le_pow₀ one_le_dimensionOneRosserSecondSplice
  have hthreshold : 1 <= dimensionOneRosserSecondLevelThreshold := by
    unfold dimensionOneRosserSecondLevelThreshold
    nlinarith
  exact hthreshold.trans hgrowth

private theorem boundedPlus_three_sub_le
    {L s : Real} (hL : 0 < L) (hs0 : 0 <= s) (hs3 : s <= 3)
    (hgrowth : dimensionOneRosserSecondLevelThreshold <= L) :
    dimensionOneRosserBoundedPlusMajorant L 3 -
        dimensionOneRosserBoundedPlusMajorant L s <=
      dimensionOneRosserBoundedSeedShare /
        (24 * dimensionOneRosserSecondSplice) := by
  have hU : 0 < dimensionOneRosserSecondSplice := by
    linarith [three_lt_dimensionOneRosserSecondSplice]
  have hlocalGrowth :
      9792 * dimensionOneRosserSecondSplice ^ 52 <= L := by
    simpa [dimensionOneRosserSecondLevelThreshold] using hgrowth
  have hthreeArtificial := dimensionOneRosserArtificialFactor_zero_le_one_add
    one_le_dimensionOneRosserSecondSplice (by norm_num : (0 : Real) <= 3)
      three_lt_dimensionOneRosserSecondSplice.le hlocalGrowth
  have hsArtificial :=
    one_le_dimensionOneRosserArtificialFactor_zero hL hs0
  have hfactor : L ^ (-1 / 3 : Real) <= 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos
      (one_le_level_of_secondGrowth hgrowth) (by norm_num)
  have hfactor0 : 0 <= L ^ (-1 / 3 : Real) :=
    (Real.rpow_pos_of_pos hL _).le
  have hdiff :
      dimensionOneRosserArtificialFactor L 0 3 -
          dimensionOneRosserArtificialFactor L 0 s <=
        1 / (12 * dimensionOneRosserSecondSplice) := by linarith
  have hscaledDiff :
      L ^ (-1 / 3 : Real) *
          (dimensionOneRosserArtificialFactor L 0 3 -
            dimensionOneRosserArtificialFactor L 0 s) <=
        1 / (12 * dimensionOneRosserSecondSplice) := by
    calc
      _ <= L ^ (-1 / 3 : Real) *
          (1 / (12 * dimensionOneRosserSecondSplice)) :=
        mul_le_mul_of_nonneg_left hdiff hfactor0
      _ <= 1 * (1 / (12 * dimensionOneRosserSecondSplice)) :=
        mul_le_mul_of_nonneg_right hfactor (by positivity)
      _ = _ := by ring
  have hshare :
      1 / (24 * dimensionOneRosserSecondSplice) <=
        dimensionOneRosserBoundedSeedShare /
          (24 * dimensionOneRosserSecondSplice) :=
    div_le_div_of_nonneg_right one_le_dimensionOneRosserBoundedSeedShare
      (by positivity)
  rw [dimensionOneRosserBoundedPlusMajorant_eq_scalar_mul,
    dimensionOneRosserBoundedPlusMajorant_eq_scalar_mul,
    dimensionOneDelayScaledPlus_eq_half_of_le (by norm_num : (3 : Real) <= 3),
    dimensionOneDelayScaledPlus_eq_half_of_le hs3]
  rw [show dimensionOneRosserBoundedProfileScalar L 3 * (1 / 2 : Real) -
      dimensionOneRosserBoundedProfileScalar L s * (1 / 2 : Real) =
        (L ^ (-1 / 3 : Real) *
          (dimensionOneRosserArtificialFactor L 0 3 -
            dimensionOneRosserArtificialFactor L 0 s)) / 2 by
      unfold dimensionOneRosserBoundedProfileScalar
      ring]
  calc
    (L ^ (-1 / 3 : Real) *
        (dimensionOneRosserArtificialFactor L 0 3 -
          dimensionOneRosserArtificialFactor L 0 s)) / 2 <=
        (1 / (12 * dimensionOneRosserSecondSplice)) / 2 :=
      div_le_div_of_nonneg_right hscaledDiff (by norm_num)
    _ = 1 / (24 * dimensionOneRosserSecondSplice) := by ring
    _ <= _ := hshare

private theorem boundedPlus_three_le_three_halves
    {L : Real} (hL : 0 < L)
    (hgrowth : dimensionOneRosserSecondLevelThreshold <= L) :
    dimensionOneRosserBoundedPlusMajorant L 3 <=
      3 * dimensionOneRosserBoundedSeedShare / 2 := by
  have hU : 0 < dimensionOneRosserSecondSplice := by
    linarith [three_lt_dimensionOneRosserSecondSplice]
  have hlocalGrowth :
      9792 * dimensionOneRosserSecondSplice ^ 52 <= L := by
    simpa [dimensionOneRosserSecondLevelThreshold] using hgrowth
  have hArtificial := dimensionOneRosserArtificialFactor_zero_le_one_add
    one_le_dimensionOneRosserSecondSplice (by norm_num : (0 : Real) <= 3)
      three_lt_dimensionOneRosserSecondSplice.le hlocalGrowth
  have hfactor : L ^ (-1 / 3 : Real) <= 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos
      (one_le_level_of_secondGrowth hgrowth) (by norm_num)
  have hfactor0 : 0 <= L ^ (-1 / 3 : Real) :=
    (Real.rpow_pos_of_pos hL _).le
  have hArtificial0 :
      0 <= dimensionOneRosserArtificialFactor L 0 3 :=
    (Real.exp_pos _).le
  have hUInv : 1 / (12 * dimensionOneRosserSecondSplice) <= 1 := by
    rw [div_le_one (by positivity : 0 < 12 * dimensionOneRosserSecondSplice)]
    nlinarith [one_le_dimensionOneRosserSecondSplice]
  have hnormalized : L ^ (-1 / 3 : Real) *
      dimensionOneRosserArtificialFactor L 0 3 <= 2 := by
    calc
      _ <= 1 * dimensionOneRosserArtificialFactor L 0 3 :=
        mul_le_mul_of_nonneg_right hfactor hArtificial0
      _ <= 1 + 1 / (12 * dimensionOneRosserSecondSplice) := by
        simpa using hArtificial
      _ <= 2 := by linarith
  have hnormalizedShare : L ^ (-1 / 3 : Real) *
      dimensionOneRosserArtificialFactor L 0 3 <=
        2 * dimensionOneRosserBoundedSeedShare :=
    hnormalized.trans (by nlinarith [one_le_dimensionOneRosserBoundedSeedShare])
  rw [dimensionOneRosserBoundedPlusMajorant_eq_scalar_mul,
    dimensionOneDelayScaledPlus_eq_half_of_le (by norm_num : (3 : Real) <= 3)]
  unfold dimensionOneRosserBoundedProfileScalar
  nlinarith

/-- The retained coordinate-three reserve absorbs the rank-zero error,
density transport, and bounded-profile change on the initial upper strip. -/
theorem dimensionOneRosserUpperSmallCoordinateBudget_le
    (R : Nat) {c D K L s : Real}
    (hD : 1 <= D) (hK : 0 <= K) (hL : 0 < L)
    (hsLower : 1 < s) (hsUpper : s <= 3)
    (hgrowth : dimensionOneRosserSecondLevelThreshold <= L)
    (hfixed : 48 * K * dimensionOneRosserSecondSplice ^ 2 <=
      L * dimensionOneRosserBoundedDelayFloor)
    (hcD : c <= D)
    (hmodel : dimensionOneRosserModelPlusPartialSum R 3 <=
      c * dimensionOneDelayScaledPlus 3) :
    9 * K / L + (1 + 3 * K / L) *
        (dimensionOneRosserModelPlusPartialSum R 3 +
          D * dimensionOneRosserBoundedPlusMajorant L 3 -
          D * dimensionOneRosserBoundedSeedShare /
            (4 * dimensionOneRosserSecondSplice)) <=
      dimensionOneRosserModelPlusPartialSum R 3 +
        D * dimensionOneRosserBoundedPlusMajorant L s := by
  have hU : 0 < dimensionOneRosserSecondSplice := by
    linarith [three_lt_dimensionOneRosserSecondSplice]
  have hUThree : 3 <= dimensionOneRosserSecondSplice :=
    three_lt_dimensionOneRosserSecondSplice.le
  have hD0 : 0 <= D := zero_le_one.trans hD
  have hDBOne : 1 <= D * dimensionOneRosserBoundedSeedShare := by
    nlinarith [one_le_dimensionOneRosserBoundedSeedShare,
      mul_nonneg hD0 dimensionOneRosserBoundedSeedShare_pos.le]
  have hmodelHalf : dimensionOneRosserModelPlusPartialSum R 3 <= c / 2 := by
    rw [dimensionOneDelayScaledPlus_eq_half_of_le
      (by norm_num : (3 : Real) <= 3)] at hmodel
    linarith
  have hmodelDB : dimensionOneRosserModelPlusPartialSum R 3 <=
      D * dimensionOneRosserBoundedSeedShare / 2 := by
    have hcDB : c <= D * dimensionOneRosserBoundedSeedShare := by
      calc
        c <= D := hcD
        _ = D * 1 := by ring
        _ <= D * dimensionOneRosserBoundedSeedShare :=
          mul_le_mul_of_nonneg_left
            one_le_dimensionOneRosserBoundedSeedShare hD0
    linarith
  have hplusThree := boundedPlus_three_le_three_halves hL hgrowth
  have hmodelProfile :
      dimensionOneRosserModelPlusPartialSum R 3 +
          D * dimensionOneRosserBoundedPlusMajorant L 3 <=
        2 * (D * dimensionOneRosserBoundedSeedShare) := by
    have hscaled := mul_le_mul_of_nonneg_left hplusThree hD0
    nlinarith
  have hprofileDiff := boundedPlus_three_sub_le hL
    (by linarith : 0 <= s) hsUpper hgrowth
  have hKdiv := dimensionOneRosserFixedSplice_K_div_level_le hL hfixed
  have hratio : 0 <= 3 * K / L := by positivity
  have hratioUpper :
      3 * K / L <= 1 / (16 * dimensionOneRosserSecondSplice ^ 2) := by
    calc
      3 * K / L = 3 * (K / L) := by ring
      _ <= 3 * (1 / (48 * dimensionOneRosserSecondSplice ^ 2)) :=
        mul_le_mul_of_nonneg_left hKdiv (by norm_num)
      _ = _ := by ring
  have hrankZero :
      9 * K / L <=
        D * dimensionOneRosserBoundedSeedShare /
          (16 * dimensionOneRosserSecondSplice) := by
    have hfirst : 9 * K / L <=
        3 / (16 * dimensionOneRosserSecondSplice ^ 2) := by
      calc
        9 * K / L = 9 * (K / L) := by ring
        _ <= 9 * (1 / (48 * dimensionOneRosserSecondSplice ^ 2)) :=
          mul_le_mul_of_nonneg_left hKdiv (by norm_num)
        _ = _ := by ring
    have hmiddle : 3 / (16 * dimensionOneRosserSecondSplice ^ 2) <=
        1 / (16 * dimensionOneRosserSecondSplice) := by
      rw [div_le_div_iff₀ (by positivity :
        0 < 16 * dimensionOneRosserSecondSplice ^ 2)
        (by positivity : 0 < 16 * dimensionOneRosserSecondSplice)]
      nlinarith
    exact hfirst.trans (hmiddle.trans
      (div_le_div_of_nonneg_right hDBOne (by positivity)))
  have hdensity :
      (3 * K / L) *
          (dimensionOneRosserModelPlusPartialSum R 3 +
            D * dimensionOneRosserBoundedPlusMajorant L 3 -
            D * dimensionOneRosserBoundedSeedShare /
              (4 * dimensionOneRosserSecondSplice)) <=
        D * dimensionOneRosserBoundedSeedShare /
          (24 * dimensionOneRosserSecondSplice) := by
    have hbracket :
        dimensionOneRosserModelPlusPartialSum R 3 +
            D * dimensionOneRosserBoundedPlusMajorant L 3 -
            D * dimensionOneRosserBoundedSeedShare /
              (4 * dimensionOneRosserSecondSplice) <=
          2 * (D * dimensionOneRosserBoundedSeedShare) := by
      have hreserve0 : 0 <= D * dimensionOneRosserBoundedSeedShare /
          (4 * dimensionOneRosserSecondSplice) := by positivity
      linarith
    calc
      _ <= (3 * K / L) *
          (2 * (D * dimensionOneRosserBoundedSeedShare)) :=
        mul_le_mul_of_nonneg_left hbracket hratio
      _ <= (1 / (16 * dimensionOneRosserSecondSplice ^ 2)) *
          (2 * (D * dimensionOneRosserBoundedSeedShare)) :=
        mul_le_mul_of_nonneg_right hratioUpper (by positivity)
      _ <= D * dimensionOneRosserBoundedSeedShare /
          (24 * dimensionOneRosserSecondSplice) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        field_simp [hU.ne']
        nlinarith [mul_nonneg hD0 dimensionOneRosserBoundedSeedShare_pos.le]
  have hprofile :
      D * (dimensionOneRosserBoundedPlusMajorant L 3 -
          dimensionOneRosserBoundedPlusMajorant L s) <=
        D * dimensionOneRosserBoundedSeedShare /
          (24 * dimensionOneRosserSecondSplice) := by
    calc
      _ <= D * (dimensionOneRosserBoundedSeedShare /
          (24 * dimensionOneRosserSecondSplice)) :=
        mul_le_mul_of_nonneg_left hprofileDiff hD0
      _ = _ := by ring
  have hcost : 9 * K / L +
      (3 * K / L) *
        (dimensionOneRosserModelPlusPartialSum R 3 +
          D * dimensionOneRosserBoundedPlusMajorant L 3 -
          D * dimensionOneRosserBoundedSeedShare /
            (4 * dimensionOneRosserSecondSplice)) +
      D * (dimensionOneRosserBoundedPlusMajorant L 3 -
        dimensionOneRosserBoundedPlusMajorant L s) <=
      D * dimensionOneRosserBoundedSeedShare /
        (4 * dimensionOneRosserSecondSplice) := by
    calc
      _ <= D * dimensionOneRosserBoundedSeedShare /
            (16 * dimensionOneRosserSecondSplice) +
          D * dimensionOneRosserBoundedSeedShare /
            (24 * dimensionOneRosserSecondSplice) +
          D * dimensionOneRosserBoundedSeedShare /
            (24 * dimensionOneRosserSecondSplice) :=
        add_le_add (add_le_add hrankZero hdensity) hprofile
      _ <= _ := by
        field_simp [hU.ne']
        nlinarith [mul_nonneg hD0 dimensionOneRosserBoundedSeedShare_pos.le]
  nlinarith

end PrimesRestrictedDigits
