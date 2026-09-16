import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserArithmeticBase
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceTargets
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserBoundedScalars

/-!
# Source-normalized rank-zero Rosser targets

This module absorbs the dimension-one rank-zero error from Iwaniec's Eq. (8.3) into the source
profile below coordinate three and uses exact cubic support at and above three.
-/

namespace PrimesRestrictedDigits

/-- On the rank-zero strip, the source plus profile contains at least one half
of the normalized logarithmic factor. -/
theorem dimensionOneRosserSourcePlusProfile_half_le
    {L s : Real} (hL : 0 < L) (hsNonneg : 0 <= s) (hsUpper : s <= 3) :
    L ^ (-1 / 3 : Real) / 2 <=
      dimensionOneRosserSourcePlusProfile L s := by
  have hdecay : 0 <= L ^ (-1 / 3 : Real) :=
    (Real.rpow_pos_of_pos hL _).le
  have hfactor : 1 <= dimensionOneRosserArtificialFactor L 0 s :=
    one_le_dimensionOneRosserArtificialFactor_zero hL hsNonneg
  have hmul := mul_le_mul_of_nonneg_left hfactor hdecay
  unfold dimensionOneRosserSourcePlusProfile
    dimensionOneRosserPlusArtificialAux
  rw [dimensionOneDelayScaledPlus_eq_half_of_le hsUpper]
  nlinarith

/-- The factor-18 gate absorbs the arithmetic rank-zero error into the source
plus profile. -/
theorem dimensionOneRosserRankZeroError_le_sourcePlusProfile
    {K D L s : Real} (hD : 0 <= D) (hL : 0 < L)
    (hsNonneg : 0 <= s) (hsUpper : s <= 3)
    (hbudget : 18 * K <= D * L ^ (2 / 3 : Real)) :
    9 * K / L <= D * dimensionOneRosserSourcePlusProfile L s := by
  have hrpow : L ^ (2 / 3 : Real) / L = L ^ (-1 / 3 : Real) := by
    calc
      L ^ (2 / 3 : Real) / L =
          L ^ (2 / 3 : Real) / L ^ (1 : Real) := by rw [Real.rpow_one]
      _ = L ^ ((2 / 3 : Real) - 1) :=
        (Real.rpow_sub hL (2 / 3 : Real) 1).symm
      _ = L ^ (-1 / 3 : Real) := by norm_num
  have hdiv : 18 * K / L <= D * L ^ (2 / 3 : Real) / L :=
    (div_le_div_iff_of_pos_right hL).2 hbudget
  have hhalf : 9 * K / L <= D * (L ^ (-1 / 3 : Real) / 2) := by
    calc
      9 * K / L = (18 * K / L) / 2 := by ring
      _ <= (D * L ^ (2 / 3 : Real) / L) / 2 := by gcongr
      _ = D * ((L ^ (2 / 3 : Real) / L) / 2) := by ring
      _ = D * (L ^ (-1 / 3 : Real) / 2) := by rw [hrpow]
  exact hhalf.trans
    (mul_le_mul_of_nonneg_left
      (dimensionOneRosserSourcePlusProfile_half_le hL hsNonneg hsUpper) hD)

/--
On `1 < s <= 3`, Eq. (8.3) and the factor-18 gate imply the source-normalized upper target at
rank zero.
-/
theorem dimensionOneRosserSourceUpperTarget_rankZero_of_ratio
    (P : Finset Nat) {K D level z s : Real}
    (hK : 0 < K) (hD : 0 <= D)
    (hprime : forall p, p ∈ P -> p.Prime)
    (hlevel : 8 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsLower : 1 < s) (hsUpper : s <= 3)
    (hbudget : 18 * K <= D * (Real.log level) ^ (2 / 3 : Real))
    (hRatio : forall u : Real, 2 <= u -> u < z ->
      sieveDensityBelow P (fun p => (p : Real)⁻¹) u /
          sieveDensityBelow P (fun p => (p : Real)⁻¹) z <
        (Real.log z / Real.log u) * (1 + K / Real.log u)) :
    dimensionOneRosserSourceUpperTarget P D 0 level z s := by
  have hL : 0 < Real.log level := Real.log_pos (by linarith)
  have herror := dimensionOneRosserRankZeroError_le_sourcePlusProfile hD hL
    (by linarith : 0 <= s) hsUpper hbudget
  have hraw := dimensionOneRosserRankZero_lt_model_add_error_of_ratio
    P hK hprime (by linarith : 2 <= level) hz
      (two_le_iwaniecBaseCutoff_of_eight_le hlevel) hs hsLower hsUpper hRatio
  have hV : 0 <= sieveDensityBelow P (fun p => (p : Real)⁻¹) z :=
    (sieveDensityBelow_reciprocal_pos P z hprime).le
  have hsNonneg : 0 <= s := by linarith
  have hinside :
      dimensionOneRosserModelPlusPartialSum 0 s +
          9 * K / Real.log level <=
        dimensionOneRosserModelPlusPartialSum 0 s +
          D * dimensionOneRosserSourcePlusProfile (Real.log level) s := by
    linarith
  unfold dimensionOneRosserSourceUpperTarget
  calc
    upperRosserFailurePartialSum P (fun p => (p : Real)⁻¹) level z 0 <
        sieveDensityBelow P (fun p => (p : Real)⁻¹) z * s⁻¹ *
          (dimensionOneRosserModelPlusPartialSum 0 s +
            9 * K / Real.log level) := hraw
    _ <= sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
          (dimensionOneRosserModelPlusPartialSum 0 s +
            D * dimensionOneRosserSourcePlusProfile (Real.log level) s) := by
      simpa only [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_left hinside
          (mul_nonneg hV (inv_nonneg.mpr hsNonneg))

/--
At and above coordinate three, exact cubic support gives the upper target at rank zero without
a density-ratio estimate.
-/
theorem dimensionOneRosserSourceUpperTarget_rankZero_of_three_le
    (P : Finset Nat) {D level z s : Real}
    (hD : 0 < D) (hprime : forall p, p ∈ P -> p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z) (hsThree : 3 <= s) :
    dimensionOneRosserSourceUpperTarget P D 0 level z s := by
  have hsPos : 0 < s := by linarith
  have hL : 0 < Real.log level := Real.log_pos (by linarith)
  have hratio : (3 : Real) <= Real.log level / Real.log z := by
    rwa [<- hs]
  have hcube : z ^ (3 : Nat) <= level :=
    power_le_of_natCast_le_log_div_log hlevel hz hratio
  have hzero : upperRosserFailurePartialSum P
      (fun p => (p : Real)⁻¹) level z 0 = 0 := by
    apply upperRosserFailurePartialSum_eq_zero_of_cutoffPow_le
      P (fun p => (p : Real)⁻¹) level z 0 hprime (by linarith)
    simpa using hcube
  have hV : 0 < sieveDensityBelow P (fun p => (p : Real)⁻¹) z :=
    sieveDensityBelow_reciprocal_pos P z hprime
  have hprofile : 0 < dimensionOneRosserSourcePlusProfile
      (Real.log level) s := by
    unfold dimensionOneRosserSourcePlusProfile
    exact mul_pos (Real.rpow_pos_of_pos hL _)
      (dimensionOneRosserPlusArtificialAux_pos hL hsPos)
  unfold dimensionOneRosserSourceUpperTarget
  rw [hzero]
  exact mul_pos (div_pos hV hsPos)
    (add_pos_of_nonneg_of_pos
      (dimensionOneRosserModelPlusPartialSum_nonneg 0 s)
      (mul_pos hD hprofile))

/--
The lower rank-zero target is a trivial positive boundary statement. staggered induction
instead starts its lower branch at rank one.
-/
theorem dimensionOneRosserSourceLowerTarget_rankZero
    (P : Finset Nat) {D level z s : Real}
    (hD : 0 < D) (hprime : forall p, p ∈ P -> p.Prime)
    (hlevel : 2 <= level) (_hz : 2 <= z) (hsPos : 0 < s) :
    dimensionOneRosserSourceLowerTarget P D 0 level z s := by
  have hL : 0 < Real.log level := Real.log_pos (by linarith)
  have hV : 0 < sieveDensityBelow P (fun p => (p : Real)⁻¹) z :=
    sieveDensityBelow_reciprocal_pos P z hprime
  have hprofile : 0 < dimensionOneRosserSourceMinusProfile
      (Real.log level) s := by
    unfold dimensionOneRosserSourceMinusProfile
    exact mul_pos (Real.rpow_pos_of_pos hL _)
      (dimensionOneRosserMinusArtificialAux_pos hL hsPos)
  unfold dimensionOneRosserSourceLowerTarget
  rw [lowerRosserFailurePartialSum_zero,
    dimensionOneRosserModelMinusPartialSum_zero]
  exact mul_pos (div_pos hV hsPos)
    (by simpa only [zero_add] using mul_pos hD hprofile)

end PrimesRestrictedDigits
