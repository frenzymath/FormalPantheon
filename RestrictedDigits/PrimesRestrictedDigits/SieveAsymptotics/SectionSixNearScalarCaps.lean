import PrimesRestrictedDigits.SieveAsymptotics.SectionSixOuterRangePartition
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIRegionSupport

/-!
# Shared scalar caps for the Section 6 near adapters

The direct strict and canonical terminal-`V` branches use the same two-gap power estimate.
This file records only that scalar calculation, the common band-cutoff bound, and the
sign-free near-product lower endpoint.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- A source modulus below `X^(1-thetaOne)` remains strictly below `X` after
two factors of size at most `X^thetaGap` are attached.

The continuation factor is a natural because that is the exact Section 6
interface; its nonnegativity is needed when multiplying the real bounds.
-/
theorem sectionSix_sourceCap_mul_sq_lt_decimalScale
    {epsilon X D : Real} {q : Nat}
    (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hX : 1 < X)
    (hD : D <= X ^ (1 - sectionSixThetaOne epsilon))
    (hq : (q : Real) <= X ^ sectionSixThetaGap epsilon) :
    D * (q : Real) * (q : Real) < X := by
  have hXPos : 0 < X := zero_lt_one.trans hX
  have hqNonneg : (0 : Real) <= (q : Real) := by positivity
  have hsourcePowerNonneg :
      0 <= X ^ (1 - sectionSixThetaOne epsilon) := by positivity
  have hgapPowerNonneg : 0 <= X ^ sectionSixThetaGap epsilon := by positivity
  have hfirst :
      D * (q : Real) <=
        X ^ (1 - sectionSixThetaOne epsilon) *
          X ^ sectionSixThetaGap epsilon :=
    mul_le_mul hD hq hqNonneg hsourcePowerNonneg
  have hsecond :
      D * (q : Real) * (q : Real) <=
        (X ^ (1 - sectionSixThetaOne epsilon) *
          X ^ sectionSixThetaGap epsilon) *
            X ^ sectionSixThetaGap epsilon :=
    mul_le_mul hfirst hq hqNonneg
      (mul_nonneg hsourcePowerNonneg hgapPowerNonneg)
  have hexponent :
      1 - sectionSixThetaOne epsilon +
          sectionSixThetaGap epsilon + sectionSixThetaGap epsilon < 1 := by
    linarith [(sectionSix_outerRange_exponent_order
      hepsilon hepsilonSmall).2.2.2.2]
  have hpower :
      (X ^ (1 - sectionSixThetaOne epsilon) *
          X ^ sectionSixThetaGap epsilon) *
            X ^ sectionSixThetaGap epsilon < X := by
    calc
      (X ^ (1 - sectionSixThetaOne epsilon) *
          X ^ sectionSixThetaGap epsilon) *
            X ^ sectionSixThetaGap epsilon =
          X ^ (1 - sectionSixThetaOne epsilon +
            sectionSixThetaGap epsilon + sectionSixThetaGap epsilon) := by
              rw [Real.rpow_add hXPos, Real.rpow_add hXPos]
      _ < X ^ (1 : Real) :=
        Real.rpow_lt_rpow_of_exponent_lt hX hexponent
      _ = X := Real.rpow_one X
  exact hsecond.trans_lt hpower

/-- Both source-band cutoffs are below the common source cap
`X^(1-thetaOne)`. -/
theorem sectionSixStateBandCutoff_le_sourceCap
    {epsilon X : Real}
    (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hX : 1 < X) (band : SectionSixStateBand) :
    sectionSixStateBandCutoff band X
        (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) <=
      X ^ (1 - sectionSixThetaOne epsilon) := by
  have hthetaLow :
      sectionSixThetaOne epsilon <= 1 - sectionSixThetaOne epsilon := by
    simp only [sectionSixThetaOne]
    linarith
  have hthetaHigh :
      1 - sectionSixThetaTwo epsilon <=
        1 - sectionSixThetaOne epsilon := by
    have hgap := (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
    unfold sectionSixThetaGap at hgap
    linarith
  cases band with
  | low =>
      exact Real.rpow_le_rpow_of_exponent_le hX.le hthetaLow
  | high =>
      exact Real.rpow_le_rpow_of_exponent_le hX.le hthetaHigh

/-- The strict near carrier contains only products greater than one when its
square width is below the fixed Section 6 roughness scale.  Only `rho^2`
occurs, so no sign or half-width hypothesis on `rho` is needed. -/
theorem one_lt_of_mem_typeIINearXCarrier_of_sq_lt_sectionSixThetaGap
    {epsilon delta rho : Real} {X N : Nat}
    (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hX : 1 < X)
    (hrhoDelta : rho ^ 2 < delta)
    (hdeltaGap : delta < sectionSixThetaGap epsilon)
    (hnear : N ∈ typeIINearXCarrier X rho) :
    1 < N := by
  have hgapOne : sectionSixThetaGap epsilon < 1 := by
    rw [sectionSixThetaGap_eq]
    linarith
  have hexponent : 0 < 1 - rho ^ 2 := by
    linarith
  have hXReal : (1 : Real) < (X : Real) := by exact_mod_cast hX
  have hpower : (1 : Real) < (X : Real) ^ (1 - rho ^ 2) :=
    Real.one_lt_rpow hXReal hexponent
  have hNReal : (1 : Real) < (N : Real) :=
    hpower.trans (mem_typeIINearXCarrier.mp hnear).2
  exact_mod_cast hNReal

end

end PrimesRestrictedDigits
