import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserBoundedProfileScalars
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserFirstWeightedSum
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSecondRawPrimeSum
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserHighSeedPrimeSum
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserUnscaledDelayPrimeSum

/-!
# Pointwise Rosser profiles at the fixed splice

These identities expand the high and bounded inner induction profiles into the literal
summands used by the first, raw-second, seed, and unscaled prime sums.
-/

namespace PrimesRestrictedDigits

private theorem buchstabArgument_inv_eq_log_ratio
    {level x : Real} (hlevel : 0 < level) (hx : 1 < x)
    (hxLevel : x < level) :
    (buchstabArgument level x)⁻¹ =
      Real.log x / Real.log (level / x) := by
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hlogDiv : 0 < Real.log (level / x) :=
    Real.log_pos ((one_lt_div (by linarith)).2 hxLevel)
  rw [<- log_div_log_eq_buchstabArgument hlevel hx]
  field_simp [hlogx.ne', hlogDiv.ne']

/-- A high-shell lower inner profile expands into the three plus-target
summands. -/
theorem dimensionOneRosserPlusHighProfileSummand_eq
    (P : Finset Nat) (R : Nat) {D level x : Real}
    (hlevel : 0 < level) (hx : 1 < x) (hxLevel : x < level) :
    x⁻¹ *
        (sieveDensityBelow P (fun q => (q : Real)⁻¹) x /
          buchstabArgument level x *
          (dimensionOneRosserModelMinusPartialSum R
              (buchstabArgument level x) +
            D * dimensionOneRosserFirstRegimeMinusMajorant
              (Real.log (level / x)) (buchstabArgument level x))) =
      x⁻¹ * sieveDensityBelow P (fun q => (q : Real)⁻¹) x *
          (Real.log x / Real.log (level / x)) *
          dimensionOneRosserModelMinusPartialSum R
            (buchstabArgument level x) +
        D * (x⁻¹ * sieveDensityBelow P
            (fun q => (q : Real)⁻¹) x *
          (Real.log x / Real.log (level / x)) *
          (1 + buchstabArgument level x ^ 50 /
            Real.log (level / x)) ^ buchstabArgument level x *
          dimensionOneDelayScaledMinus (buchstabArgument level x) *
          (Real.log (level / x)) ^ (-1 / 3 : Real)) +
        D * (x⁻¹ * sieveDensityBelow P
            (fun q => (q : Real)⁻¹) x *
          (Real.log x / Real.log (level / x)) *
          dimensionOneRosserSeedEnvelope (buchstabArgument level x)) := by
  have hL : 0 < Real.log (level / x) :=
    Real.log_pos ((one_lt_div (by linarith)).2 hxLevel)
  have hVcoord :
      sieveDensityBelow P (fun q => (q : Real)⁻¹) x /
          buchstabArgument level x =
        sieveDensityBelow P (fun q => (q : Real)⁻¹) x *
          (Real.log x / Real.log (level / x)) := by
    rw [div_eq_mul_inv, buchstabArgument_inv_eq_log_ratio hlevel hx hxLevel]
  rw [hVcoord, dimensionOneRosserFirstRegimeMinusMajorant_eq hL]
  ring

/-- A bounded-shell lower inner profile expands into the plus-target first and
raw summands and the bounded plus-named outer delay summand. -/
theorem dimensionOneRosserPlusBoundedProfileSummand_eq
    (P : Finset Nat) (R : Nat) {D level x : Real}
    (hlevel : 0 < level) (hx : 1 < x) (hxLevel : x < level) :
    x⁻¹ *
        (sieveDensityBelow P (fun q => (q : Real)⁻¹) x /
          buchstabArgument level x *
          (dimensionOneRosserModelMinusPartialSum R
              (buchstabArgument level x) +
            D * dimensionOneRosserBoundedMinusMajorant
              (Real.log (level / x)) (buchstabArgument level x))) =
      x⁻¹ * sieveDensityBelow P (fun q => (q : Real)⁻¹) x *
          (Real.log x / Real.log (level / x)) *
          dimensionOneRosserModelMinusPartialSum R
            (buchstabArgument level x) +
        D * (x⁻¹ * sieveDensityBelow P
            (fun q => (q : Real)⁻¹) x *
          (Real.log x / Real.log (level / x)) *
          (1 + buchstabArgument level x ^ 50 /
            Real.log (level / x)) ^ buchstabArgument level x *
          dimensionOneDelayScaledMinus (buchstabArgument level x) *
          (Real.log (level / x)) ^ (-1 / 3 : Real)) +
        D * dimensionOneRosserBoundedSeedShare *
          (x⁻¹ * sieveDensityBelow P (fun q => (q : Real)⁻¹) x *
            (Real.log x / Real.log (level / x)) *
            dimensionOneDelayScaledMinus (buchstabArgument level x)) := by
  have hL : 0 < Real.log (level / x) :=
    Real.log_pos ((one_lt_div (by linarith)).2 hxLevel)
  have hVcoord :
      sieveDensityBelow P (fun q => (q : Real)⁻¹) x /
          buchstabArgument level x =
        sieveDensityBelow P (fun q => (q : Real)⁻¹) x *
          (Real.log x / Real.log (level / x)) := by
    rw [div_eq_mul_inv, buchstabArgument_inv_eq_log_ratio hlevel hx hxLevel]
  rw [hVcoord]
  unfold dimensionOneRosserBoundedMinusMajorant
    dimensionOneRosserBoundedSeedShare
  rw [dimensionOneRosserArtificialFactor_eq_rpow hL]
  unfold dimensionOneRosserArtificialBase
  norm_num
  ring

/-- A high-shell upper inner profile expands into the three minus-target
summands. -/
theorem dimensionOneRosserMinusHighProfileSummand_eq
    (P : Finset Nat) (R : Nat) {D level x : Real}
    (hlevel : 0 < level) (hx : 1 < x) (hxLevel : x < level) :
    x⁻¹ *
        (sieveDensityBelow P (fun q => (q : Real)⁻¹) x /
          buchstabArgument level x *
          (dimensionOneRosserModelPlusPartialSum R
              (buchstabArgument level x) +
            D * dimensionOneRosserFirstRegimePlusMajorant
              (Real.log (level / x)) (buchstabArgument level x))) =
      x⁻¹ * sieveDensityBelow P (fun q => (q : Real)⁻¹) x *
          (Real.log x / Real.log (level / x)) *
          dimensionOneRosserModelPlusPartialSum R
            (buchstabArgument level x) +
        D * (x⁻¹ * sieveDensityBelow P
            (fun q => (q : Real)⁻¹) x *
          (Real.log x / Real.log (level / x)) *
          (1 + buchstabArgument level x ^ 50 /
            Real.log (level / x)) ^ buchstabArgument level x *
          dimensionOneDelayScaledPlus (buchstabArgument level x) *
          (Real.log (level / x)) ^ (-1 / 3 : Real)) +
        D * (x⁻¹ * sieveDensityBelow P
            (fun q => (q : Real)⁻¹) x *
          (Real.log x / Real.log (level / x)) *
          dimensionOneRosserSeedEnvelope (buchstabArgument level x)) := by
  have hL : 0 < Real.log (level / x) :=
    Real.log_pos ((one_lt_div (by linarith)).2 hxLevel)
  have hVcoord :
      sieveDensityBelow P (fun q => (q : Real)⁻¹) x /
          buchstabArgument level x =
        sieveDensityBelow P (fun q => (q : Real)⁻¹) x *
          (Real.log x / Real.log (level / x)) := by
    rw [div_eq_mul_inv, buchstabArgument_inv_eq_log_ratio hlevel hx hxLevel]
  rw [hVcoord, dimensionOneRosserFirstRegimePlusMajorant_eq hL]
  ring

/-- A bounded-shell upper inner profile expands into the minus-target first
and raw summands and the bounded minus-named outer delay summand. -/
theorem dimensionOneRosserMinusBoundedProfileSummand_eq
    (P : Finset Nat) (R : Nat) {D level x : Real}
    (hlevel : 0 < level) (hx : 1 < x) (hxLevel : x < level) :
    x⁻¹ *
        (sieveDensityBelow P (fun q => (q : Real)⁻¹) x /
          buchstabArgument level x *
          (dimensionOneRosserModelPlusPartialSum R
              (buchstabArgument level x) +
            D * dimensionOneRosserBoundedPlusMajorant
              (Real.log (level / x)) (buchstabArgument level x))) =
      x⁻¹ * sieveDensityBelow P (fun q => (q : Real)⁻¹) x *
          (Real.log x / Real.log (level / x)) *
          dimensionOneRosserModelPlusPartialSum R
            (buchstabArgument level x) +
        D * (x⁻¹ * sieveDensityBelow P
            (fun q => (q : Real)⁻¹) x *
          (Real.log x / Real.log (level / x)) *
          (1 + buchstabArgument level x ^ 50 /
            Real.log (level / x)) ^ buchstabArgument level x *
          dimensionOneDelayScaledPlus (buchstabArgument level x) *
          (Real.log (level / x)) ^ (-1 / 3 : Real)) +
        D * dimensionOneRosserBoundedSeedShare *
          (x⁻¹ * sieveDensityBelow P (fun q => (q : Real)⁻¹) x *
            (Real.log x / Real.log (level / x)) *
            dimensionOneDelayScaledPlus (buchstabArgument level x)) := by
  have hL : 0 < Real.log (level / x) :=
    Real.log_pos ((one_lt_div (by linarith)).2 hxLevel)
  have hVcoord :
      sieveDensityBelow P (fun q => (q : Real)⁻¹) x /
          buchstabArgument level x =
        sieveDensityBelow P (fun q => (q : Real)⁻¹) x *
          (Real.log x / Real.log (level / x)) := by
    rw [div_eq_mul_inv, buchstabArgument_inv_eq_log_ratio hlevel hx hxLevel]
  rw [hVcoord]
  unfold dimensionOneRosserBoundedPlusMajorant
    dimensionOneRosserBoundedSeedShare
  rw [dimensionOneRosserArtificialFactor_eq_rpow hL]
  unfold dimensionOneRosserArtificialBase
  norm_num
  ring

end PrimesRestrictedDigits
