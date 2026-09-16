import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceRankZero
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceEndpoint
/-! # DimensionOneRosserSourceSmallCoordinateScalar -/

set_option maxHeartbeats 800000

/-!
# Source low-coordinate scalar reserve

This proves the scalar budget that combines the coordinate-three reserve with the
low-coordinate collector.
-/

namespace PrimesRestrictedDigits

private theorem sourceScalar_pow_two_le_pow_twentyFour
    {q : Real} (hq : 1 <= q) : q ^ (2 : Nat) <= q ^ (24 : Nat) := by
  calc
    q ^ 2 = q ^ 2 * 1 := by ring
    _ <= q ^ 2 * q ^ 22 :=
      mul_le_mul_of_nonneg_left (one_le_pow₀ hq) (by positivity)
    _ = q ^ 24 := by ring

private theorem sourceScalar_pow_two_div_le {q : Real} (hq : 0 <= q) :
    q ^ (2 : Nat) / 576 <= q ^ 2 := by
  have hq2nonneg : 0 <= q ^ 2 := pow_nonneg hq 2
  calc
    q ^ 2 / 576 = (1 / 576 : Real) * q ^ 2 := by ring
    _ <= 1 * q ^ 2 :=
      mul_le_mul_of_nonneg_right (by norm_num) hq2nonneg
    _ = q ^ 2 := by ring

/-- The literal source cutoff is below the twenty-fourth root of the
logarithmic level. -/
theorem dimensionOneRosserSourceCutoff_le_twentyFourthRoot
    {L s0 : Real} (hs0 : 1 <= s0)
    (hsource : s0 ^ 50 = L * (Real.log L) ^ 3)
    (hLExp : Real.exp 1 <= L)
    (hgate : 124800 + 14400 * Real.log (Real.log L) <= Real.log L) :
    s0 <= L ^ (1 / 24 : Real) := by
  have hLPos : 0 < L := (Real.exp_pos 1).trans_le hLExp
  have hs0Nonneg : 0 <= s0 := zero_le_one.trans hs0
  have hlogCube := dimensionOneRosserSourceGate_log_cube_le hLExp hgate
  have hsourceLe : s0 ^ 50 <= L ^ 2 := by
    calc
      s0 ^ 50 = L * (Real.log L) ^ 3 := hsource
      _ <= L * L := mul_le_mul_of_nonneg_left hlogCube hLPos.le
      _ = L ^ 2 := by ring
  have hpow48 : s0 ^ 48 <= s0 ^ 50 := by
    calc
      s0 ^ 48 = s0 ^ 48 * 1 := by ring
      _ <= s0 ^ 48 * s0 ^ 2 :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hs0) (pow_nonneg hs0Nonneg 48)
      _ = s0 ^ 50 := by ring
  have hpow24 : s0 ^ 24 <= L := by
    apply (sq_le_sq₀ (pow_nonneg hs0Nonneg 24) hLPos.le).mp
    calc
      (s0 ^ 24) ^ 2 = s0 ^ 48 := by ring
      _ <= s0 ^ 50 := hpow48
      _ <= L ^ 2 := hsourceLe
  have hrootNonneg : 0 <= L ^ (1 / 24 : Real) :=
    Real.rpow_nonneg hLPos.le _
  have hrootPow : (L ^ (1 / 24 : Real)) ^ (24 : Nat) = L := by
    convert Real.rpow_inv_natCast_pow (n := 24) hLPos.le
      (by norm_num : (24 : Nat) ≠ 0) using 1; norm_num
  apply (pow_le_pow_iff_left₀ hs0Nonneg hrootNonneg
    (by norm_num : (24 : Nat) ≠ 0)).mp
  rwa [hrootPow]

private theorem sourceArtificialFactor_three_sub_le
    {L s s0 : Real} (hs0Large : Real.exp 5000 + 1 <= s0)
    (hsNonneg : 0 <= s)
    (hsource : s0 ^ 50 = L * (Real.log L) ^ 3)
    (hLExp : Real.exp 1 <= L)
    (hgate : 124800 + 14400 * Real.log (Real.log L) <= Real.log L) :
    dimensionOneRosserArtificialFactor L 0 3 -
        dimensionOneRosserArtificialFactor L 0 s <=
      dimensionOneRosserArtificialFactor L 0 3 / (8 * s0) := by
  have hLPos : 0 < L := (Real.exp_pos 1).trans_le hLExp
  have hs0One : 1 <= s0 := by
    have hExpPos := Real.exp_pos (5000 : Real)
    linarith
  have hs0Pos : 0 < s0 := zero_lt_one.trans_le hs0One
  let q : Real := L ^ (1 / 24 : Real)
  have hqNonneg : 0 <= q := by
    dsimp only [q]
    exact Real.rpow_nonneg hLPos.le _
  have hqPow : q ^ (24 : Nat) = L := by
    dsimp only [q]
    convert Real.rpow_inv_natCast_pow (n := 24) hLPos.le
      (by norm_num : (24 : Nat) ≠ 0) using 1; norm_num
  have hs0q : s0 <= q := by
    dsimp only [q]
    exact dimensionOneRosserSourceCutoff_le_twentyFourthRoot hs0One hsource
      hLExp hgate
  have hfiveThousandTwo : (5002 : Real) <= s0 := by
    have hExp := Real.add_one_le_exp (5000 : Real)
    linarith
  have hqLarge : (5002 : Real) <= q := hfiveThousandTwo.trans hs0q
  have hconstant : (56 : Real) * 3 ^ (50 : Nat) <= q ^ (23 : Nat) := by
    have hnumeric : (56 : Real) * 3 ^ (50 : Nat) <= 5002 ^ (23 : Nat) := by
      norm_num
    exact hnumeric.trans (pow_le_pow_left₀ (by norm_num) hqLarge 23)
  have hcutoffScale : (56 : Real) * 3 ^ (50 : Nat) * s0 <= L := by
    calc
      (56 : Real) * 3 ^ (50 : Nat) * s0 <= q ^ 23 * q :=
        mul_le_mul hconstant hs0q (zero_le_one.trans hs0One)
          (pow_nonneg hqNonneg 23)
      _ = q ^ 24 := by ring
      _ = L := by simpa only [q] using hqPow
  let x : Real := 3 ^ (50 : Nat) / L
  have hxNonneg : 0 <= x := by
    dsimp only [x]
    positivity
  have hxBound : x <= 1 / (56 * s0) := by
    dsimp only [x]
    rw [div_le_div_iff₀ hLPos (by positivity : 0 < 56 * s0)]
    nlinarith [hcutoffScale]
  have hunitBound : 1 / (56 * s0) <= (1 : Real) := by
    apply (div_le_one (by positivity : 0 < 56 * s0)).2
    nlinarith
  have hxOne : x <= 1 := hxBound.trans hunitBound
  have hxSq : x ^ 2 <= x := by nlinarith [mul_nonneg hxNonneg (sub_nonneg.mpr hxOne)]
  have hxCube : x ^ 3 <= x := by
    calc
      x ^ 3 = x ^ 2 * x := by ring
      _ <= x * x := mul_le_mul_of_nonneg_right hxSq hxNonneg
      _ = x ^ 2 := by ring
      _ <= x := hxSq
  have hpoly : (1 + x) ^ 3 <= 1 + 7 * x := by
    nlinarith
  have hpolyBound : (1 + x) ^ 3 <= 1 + 1 / (8 * s0) := by
    have hseven : 7 * x <= 1 / (8 * s0) := by
      calc
        7 * x <= 7 * (1 / (56 * s0)) :=
          mul_le_mul_of_nonneg_left hxBound (by norm_num)
        _ = 1 / (8 * s0) := by ring
    linarith
  have hfactorThree : dimensionOneRosserArtificialFactor L 0 3 =
      (1 + x) ^ 3 := by
    rw [dimensionOneRosserArtificialFactor_eq_rpow hLPos]
    unfold dimensionOneRosserArtificialBase
    dsimp only [x]
    norm_num [Real.rpow_natCast]
  have hfactorS : 1 <= dimensionOneRosserArtificialFactor L 0 s :=
    one_le_dimensionOneRosserArtificialFactor_zero hLPos hsNonneg
  have hdiff : dimensionOneRosserArtificialFactor L 0 3 -
      dimensionOneRosserArtificialFactor L 0 s <= 1 / (8 * s0) := by
    rw [hfactorThree]
    linarith
  have hfactorThreeOne : 1 <=
      dimensionOneRosserArtificialFactor L 0 3 := by
    exact one_le_dimensionOneRosserArtificialFactor_zero hLPos (by norm_num)
  have hscaled : 1 / (8 * s0) <=
      dimensionOneRosserArtificialFactor L 0 3 / (8 * s0) := by
    exact (div_le_div_iff_of_pos_right (by positivity : 0 < 8 * s0)).2
      hfactorThreeOne
  exact hdiff.trans hscaled

/--
On the low strip, the increase from the current source profile to its coordinate-three value
consumes at most one eighth of the source share.
-/
theorem dimensionOneRosserSourcePlusProfile_three_sub_le_eighth
    {L s s0 : Real} (hs0Large : Real.exp 5000 + 1 <= s0)
    (hsNonneg : 0 <= s) (hsUpper : s <= 3)
    (hsource : s0 ^ 50 = L * (Real.log L) ^ 3)
    (hLExp : Real.exp 1 <= L)
    (hgate : 124800 + 14400 * Real.log (Real.log L) <= Real.log L) :
    dimensionOneRosserSourcePlusProfile L 3 -
        dimensionOneRosserSourcePlusProfile L s <=
      dimensionOneRosserSourcePlusProfile L 3 / (8 * s0) := by
  have hLPos : 0 < L := (Real.exp_pos 1).trans_le hLExp
  have hdecay : 0 <= L ^ (-1 / 3 : Real) :=
    (Real.rpow_pos_of_pos hLPos _).le
  have hfactor := sourceArtificialFactor_three_sub_le hs0Large hsNonneg
    hsource hLExp hgate
  unfold dimensionOneRosserSourcePlusProfile
    dimensionOneRosserPlusArtificialAux
  rw [dimensionOneDelayScaledPlus_eq_half_of_le
      (by norm_num : (3 : Real) <= 3),
    dimensionOneDelayScaledPlus_eq_half_of_le hsUpper]
  have hscaled := mul_le_mul_of_nonneg_left hfactor hdecay
  calc
    L ^ (-1 / 3 : Real) *
          (dimensionOneRosserArtificialFactor L 0 3 * (1 / 2)) -
        L ^ (-1 / 3 : Real) *
          (dimensionOneRosserArtificialFactor L 0 s * (1 / 2)) =
      L ^ (-1 / 3 : Real) *
          (dimensionOneRosserArtificialFactor L 0 3 * (1 / 2) -
            dimensionOneRosserArtificialFactor L 0 s * (1 / 2)) := by ring
    _ =
        (L ^ (-1 / 3 : Real) *
          (dimensionOneRosserArtificialFactor L 0 3 -
            dimensionOneRosserArtificialFactor L 0 s) * (1 / 2)) := by ring
    _ <= (L ^ (-1 / 3 : Real) *
          (dimensionOneRosserArtificialFactor L 0 3 / (8 * s0))) * (1 / 2) :=
      mul_le_mul_of_nonneg_right hscaled (by norm_num)
    _ = L ^ (-1 / 3 : Real) *
          (dimensionOneRosserArtificialFactor L 0 3 * (1 / 2)) /
            (8 * s0) := by ring

/-
The coordinate-three reserve pays the four low-coordinate scalar costs in the assembly.
-/
set_option maxHeartbeats 2000000 in
theorem dimensionOneRosserSourceUpperSmallCoordinateBudget_le
    (R : Nat) {c D K L s s0 : Real}
    (hc : 0 <= c) (hD : 1 <= D) (hK : 0 <= K)
    (hs0Large : Real.exp 5000 + 1 <= s0)
    (hsNonneg : 0 <= s) (hsUpper : s <= 3)
    (hsource : s0 ^ 50 = L * (Real.log L) ^ 3)
    (hLExp : Real.exp 1 <= L)
    (hgate : 124800 + 14400 * Real.log (Real.log L) <= Real.log L)
    (hsmall : 6 * (1 + 2304 * K) <= L ^ (1 / 24 : Real))
    (hDdom : 2 * (1 + K) + 2304 * c * K <= D)
    (hmodel : dimensionOneRosserModelPlusPartialSum (R + 1) 3 <=
      c * dimensionOneDelayScaledPlus 3) :
    9 * K / L + (1 + 3 * K / L) *
        (dimensionOneRosserModelPlusPartialSum (R + 1) 3 +
          D * dimensionOneRosserSourcePlusProfile L 3 -
          (dimensionOneRosserModelPlusPartialSum (R + 1) s0 +
            D * dimensionOneRosserSourcePlusProfile L 3 / (2 * s0))) <=
      dimensionOneRosserModelPlusPartialSum (R + 1) 3 +
        D * dimensionOneRosserSourcePlusProfile L s := by
  have hLPos : 0 < L := (Real.exp_pos 1).trans_le hLExp
  have hs0One : 1 <= s0 := by
    have hExpPos := Real.exp_pos (5000 : Real)
    linarith
  have hs0Pos : 0 < s0 := zero_lt_one.trans_le hs0One
  have hD0 : 0 <= D := zero_le_one.trans hD
  have hcK : 0 <= c * K := mul_nonneg hc hK
  have hDge2K : 2 * K <= D := by
    nlinarith [mul_nonneg (by norm_num : (0 : Real) <= 2) hK, hcK]
  have hDgeCK : 2304 * c * K <= D := by
    have honeK : 0 <= 1 + K := by linarith
    have htwo : 0 <= 2 * (1 + K) := mul_nonneg (by norm_num) honeK
    nlinarith [htwo, hcK]
  let q : Real := L ^ (1 / 24 : Real)
  have hqNonneg : 0 <= q := by
    dsimp only [q]
    exact Real.rpow_nonneg hLPos.le _
  have hqPow : q ^ (24 : Nat) = L := by
    dsimp only [q]
    convert Real.rpow_inv_natCast_pow (n := 24) hLPos.le
      (by norm_num : (24 : Nat) ≠ 0) using 1; norm_num
  have hs0q : s0 <= q := by
    dsimp only [q]
    exact dimensionOneRosserSourceCutoff_le_twentyFourthRoot hs0One hsource
      hLExp hgate
  have hqLarge : (5002 : Real) <= q := by
    have hExp := Real.add_one_le_exp (5000 : Real)
    linarith [hs0Large, hs0q]
  have hqOne : 1 <= q := by linarith
  have hq15 : (72 : Real) <= q ^ (15 : Nat) := by
    have hnumeric : (72 : Real) <= 5002 ^ (15 : Nat) := by norm_num
    exact hnumeric.trans (pow_le_pow_left₀ (by norm_num) hqLarge 15)
  have hq16 : q ^ (16 : Nat) = L ^ (2 / 3 : Real) := by
    dsimp only [q]
    rw [← Real.rpow_mul_natCast hLPos.le]
    congr 1
    norm_num
  have hLpow : L ^ (-1 / 3 : Real) * L = L ^ (2 / 3 : Real) := by
    calc
      L ^ (-1 / 3 : Real) * L =
          L ^ (-1 / 3 : Real) * L ^ (1 : Real) := by rw [Real.rpow_one]
      _ = L ^ ((-1 / 3 : Real) + 1) :=
        (Real.rpow_add hLPos _ _).symm
      _ = L ^ (2 / 3 : Real) := by congr 1; norm_num
  have hq72 : 72 * s0 <= q ^ (16 : Nat) := by
    calc
      72 * s0 <= 72 * q := mul_le_mul_of_nonneg_left hs0q (by norm_num)
      _ <= q ^ 15 * q := mul_le_mul_of_nonneg_right hq15 hqNonneg
      _ = q ^ 16 := by ring
  have hN3Lower : L ^ (-1 / 3 : Real) / 2 <=
      dimensionOneRosserSourcePlusProfile L 3 :=
    dimensionOneRosserSourcePlusProfile_half_le hLPos (by norm_num) (by norm_num)
  have hN3Nonneg : 0 <= dimensionOneRosserSourcePlusProfile L 3 :=
    (by positivity : 0 <= L ^ (-1 / 3 : Real) / 2).trans hN3Lower
  have hFNonneg : 0 <=
      dimensionOneRosserModelPlusPartialSum (R + 1) s0 :=
    dimensionOneRosserModelPlusPartialSum_nonneg (R + 1) s0
  have hmodel' : dimensionOneRosserModelPlusPartialSum (R + 1) 3 <= c / 2 := by
    rw [dimensionOneDelayScaledPlus_eq_half_of_le
      (by norm_num : (3 : Real) <= 3)] at hmodel
    simpa [div_eq_mul_inv] using hmodel
  have hcostError : 9 * K / L <=
      D * dimensionOneRosserSourcePlusProfile L 3 / (8 * s0) := by
    have hleft : 9 * K / L <=
        D * L ^ (-1 / 3 : Real) / (16 * s0) := by
      rw [div_le_div_iff₀ hLPos (by positivity : 0 < 16 * s0)]
      calc
        9 * K * (16 * s0) = 144 * K * s0 := by ring
        _ <= 72 * D * s0 := by nlinarith [hDge2K, hs0Pos]
        _ <= D * q ^ 16 := by
          have hmul := mul_le_mul_of_nonneg_left hq72 hD0
          nlinarith
        _ = D * L ^ (2 / 3 : Real) := by rw [hq16]
        _ = D * (L ^ (-1 / 3 : Real) * L) := by rw [hLpow]
        _ = D * L ^ (-1 / 3 : Real) * L := by ring
    have hright : D * L ^ (-1 / 3 : Real) / (16 * s0) <=
        D * dimensionOneRosserSourcePlusProfile L 3 / (8 * s0) := by
      have hmul := mul_le_mul_of_nonneg_left hN3Lower
        (by positivity : 0 <= D / (8 * s0))
      calc
        D * L ^ (-1 / 3 : Real) / (16 * s0) =
            (D / (8 * s0)) * (L ^ (-1 / 3 : Real) / 2) := by ring
        _ <= (D / (8 * s0)) *
            dimensionOneRosserSourcePlusProfile L 3 := hmul
        _ = _ := by ring
    exact hleft.trans hright
  have hcostModel : (3 * K / L) *
      dimensionOneRosserModelPlusPartialSum (R + 1) 3 <=
        D * dimensionOneRosserSourcePlusProfile L 3 / (8 * s0) := by
    have hraw : (3 * K / L) *
        dimensionOneRosserModelPlusPartialSum (R + 1) 3 <=
        D / (1536 * L) := by
      have hmul := mul_le_mul_of_nonneg_left hmodel' (by positivity : 0 <= 3 * K / L)
      have hcoef : (3 * K / L) * (c / 2) <= D / (1536 * L) := by
        calc
          (3 * K / L) * (c / 2) = (3 * c * K / 2) / L := by ring
          _ <= (D / 1536) / L := by
            apply div_le_div_of_nonneg_right _ hLPos.le
            nlinarith [hDgeCK]
          _ = D / (1536 * L) := by ring
      exact hmul.trans hcoef
    have hscale : D / (1536 * L) <=
        D * L ^ (-1 / 3 : Real) / (16 * s0) := by
      have hscalar : (1 : Real) / (1536 * L) <=
          L ^ (-1 / 3 : Real) / (16 * s0) := by
        have hs0Scale : 16 * s0 <= 1536 * L ^ (2 / 3 : Real) := by
          rw [← hq16]
          have hq16large : 1 <= q ^ 16 := one_le_pow₀ hqOne
          have hmul := mul_le_mul_of_nonneg_left hs0q (by norm_num : 0 <= (16 : Real))
          nlinarith
        rw [show (1 : Real) / (1536 * L) = (1 / 1536) / L by ring,
          show L ^ (-1 / 3 : Real) / (16 * s0) =
            (L ^ (-1 / 3 : Real) / 16) / s0 by ring]
        rw [div_le_div_iff₀ hLPos hs0Pos]
        calc
          (1 / 1536) * s0 <= L ^ (2 / 3 : Real) / 16 := by
            nlinarith [hs0Scale]
          _ = (L ^ (-1 / 3 : Real) * L) / 16 := by rw [hLpow]
          _ = (L ^ (-1 / 3 : Real) / 16) * L := by ring
      have hscaledD := mul_le_mul_of_nonneg_left hscalar hD0
      calc
        D / (1536 * L) = D * (1 / (1536 * L)) := by ring
        _ <= D * (L ^ (-1 / 3 : Real) / (16 * s0)) := hscaledD
        _ = D * L ^ (-1 / 3 : Real) / (16 * s0) := by ring
    have hmulProfile : D * L ^ (-1 / 3 : Real) / (16 * s0) <=
        D * dimensionOneRosserSourcePlusProfile L 3 / (8 * s0) := by
      have hmul := mul_le_mul_of_nonneg_left hN3Lower
        (by positivity : 0 <= D / (8 * s0))
      calc
        D * L ^ (-1 / 3 : Real) / (16 * s0) =
            (D / (8 * s0)) * (L ^ (-1 / 3 : Real) / 2) := by ring
        _ <= (D / (8 * s0)) *
            dimensionOneRosserSourcePlusProfile L 3 := hmul
        _ = _ := by ring
    exact hraw.trans (hscale.trans hmulProfile)
  have hsmallK : 13824 * K <= q := by
    dsimp only [q] at hs0q ⊢
    have := hsmall
    nlinarith
  have hKs0 : 24 * K * s0 <= L := by
    calc
      24 * K * s0 <= 24 * (q / 13824) * q := by
        have hKq : K <= q / 13824 := by
          apply (le_div_iff₀ (by norm_num : (0 : Real) < 13824)).2
          calc
            K * 13824 = 13824 * K := by ring
            _ <= q := hsmallK
        calc
          24 * K * s0 <= 24 * (q / 13824) * s0 := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hKq (by norm_num)) (by positivity)
          _ <= 24 * (q / 13824) * q := by
            exact mul_le_mul_of_nonneg_left hs0q (by positivity)
      _ = q ^ 2 / 576 := by ring
      _ <= q ^ 2 := sourceScalar_pow_two_div_le hqNonneg
      _ <= q ^ 24 := by
        exact sourceScalar_pow_two_le_pow_twentyFour hqOne
      _ = L := hqPow
  have hdeltaSmall : 3 * K / L <= 1 / (8 * s0) := by
    rw [div_le_iff₀ hLPos]
    calc
      3 * K <= L / (8 * s0) := by
        apply (le_div_iff₀ (by positivity : 0 < (8 : Real) * s0)).2
        calc
          3 * K * (8 * s0) = 24 * K * s0 := by ring
          _ <= L := hKs0
      _ = 1 / (8 * s0) * L := by ring
  have hcostDensity : (3 * K / L) *
      (D * dimensionOneRosserSourcePlusProfile L 3) <=
        D * dimensionOneRosserSourcePlusProfile L 3 / (8 * s0) := by
    have hnonneg : 0 <= D * dimensionOneRosserSourcePlusProfile L 3 :=
      mul_nonneg hD0 hN3Nonneg
    have hmul := mul_le_mul_of_nonneg_right hdeltaSmall hnonneg
    exact hmul.trans_eq (by ring)
  have hprofileDiff :=
    dimensionOneRosserSourcePlusProfile_three_sub_le_eighth hs0Large hsNonneg
      hsUpper hsource hLExp hgate
  have hcostProfile : D *
      (dimensionOneRosserSourcePlusProfile L 3 -
        dimensionOneRosserSourcePlusProfile L s) <=
      D * dimensionOneRosserSourcePlusProfile L 3 / (8 * s0) := by
    exact (mul_le_mul_of_nonneg_left hprofileDiff hD0).trans_eq (by ring)
  have hcosts : 9 * K / L +
      (3 * K / L) * dimensionOneRosserModelPlusPartialSum (R + 1) 3 +
      (3 * K / L) * (D * dimensionOneRosserSourcePlusProfile L 3) +
      D * (dimensionOneRosserSourcePlusProfile L 3 -
        dimensionOneRosserSourcePlusProfile L s) <=
      D * dimensionOneRosserSourcePlusProfile L 3 / (2 * s0) := by
    calc
      _ <= D * dimensionOneRosserSourcePlusProfile L 3 / (8 * s0) +
          D * dimensionOneRosserSourcePlusProfile L 3 / (8 * s0) +
          D * dimensionOneRosserSourcePlusProfile L 3 / (8 * s0) +
          D * dimensionOneRosserSourcePlusProfile L 3 / (8 * s0) := by
        exact add_le_add (add_le_add (add_le_add hcostError hcostModel)
          hcostDensity) hcostProfile
      _ = _ := by ring
  let B : Real :=
    dimensionOneRosserModelPlusPartialSum (R + 1) 3 +
      D * dimensionOneRosserSourcePlusProfile L 3 -
      (dimensionOneRosserModelPlusPartialSum (R + 1) s0 +
        D * dimensionOneRosserSourcePlusProfile L 3 / (2 * s0))
  have hB : B <= dimensionOneRosserModelPlusPartialSum (R + 1) 3 +
      D * dimensionOneRosserSourcePlusProfile L 3 := by
    dsimp only [B]
    have hshare : 0 <= D * dimensionOneRosserSourcePlusProfile L 3 /
        (2 * s0) := by positivity
    linarith
  have hdeltaNonneg : 0 <= 3 * K / L := by positivity
  have hdeltaB : (3 * K / L) * B <=
      (3 * K / L) * dimensionOneRosserModelPlusPartialSum (R + 1) 3 +
        (3 * K / L) *
          (D * dimensionOneRosserSourcePlusProfile L 3) := by
    calc
      (3 * K / L) * B <=
          (3 * K / L) *
            (dimensionOneRosserModelPlusPartialSum (R + 1) 3 +
              D * dimensionOneRosserSourcePlusProfile L 3) :=
        mul_le_mul_of_nonneg_left hB hdeltaNonneg
      _ = _ := by ring
  have hbound : 9 * K / L + (3 * K / L) * B +
      D * (dimensionOneRosserSourcePlusProfile L 3 -
        dimensionOneRosserSourcePlusProfile L s) <=
      D * dimensionOneRosserSourcePlusProfile L 3 / (2 * s0) := by
    calc
      _ <= 9 * K / L +
          (3 * K / L) * dimensionOneRosserModelPlusPartialSum (R + 1) 3 +
          (3 * K / L) *
            (D * dimensionOneRosserSourcePlusProfile L 3) +
          D * (dimensionOneRosserSourcePlusProfile L 3 -
            dimensionOneRosserSourcePlusProfile L s) := by linarith [hdeltaB]
      _ <= _ := hcosts
  dsimp only [B] at hbound ⊢
  nlinarith [hbound, hFNonneg]

end PrimesRestrictedDigits
