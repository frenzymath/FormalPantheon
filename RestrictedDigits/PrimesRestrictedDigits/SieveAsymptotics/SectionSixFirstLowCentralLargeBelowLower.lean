import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeBelowBridges
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeBelowSourceIntegrals
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeContinuationFiniteLower

/-!
# Eventual lower bound for the low central-large below continuation

The finite continuation estimate is combined with normalized prime-log triple convergence and
the cubic log-prime error bound. This is Maynard's `I_3` contribution, with the full
unit-containing strict sifted term retained.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 141--142, Eq. (6.10).
-/

open Filter MeasureTheory Set
open scoped Topology

namespace PrimesRestrictedDigits

noncomputable section

private theorem sectionSixFirstLowCentralLargeBelow_lower_of_bounds
    {C epsilon rho normalized : Real}
    (hC : 0 <= C) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length) (digit : Fin 10)
    (hmain :
      sectionSixFirstLowCentralLargeContinuationBuchstabMainSum
          epsilon length .below =
        normalized / Real.log ((10 ^ length : Nat) : Real))
    (hnormalized : normalized <=
      sectionSixFirstLowCentralLargeBelowIntegral epsilon + rho / 2)
    (herrorSmall :
      C * (2 * Real.log 4) ^ 3 /
          (sectionSixThetaGap epsilon ^ 5 *
            Real.log ((10 ^ length : Nat) : Real)) <= rho / 2)
    (hfinite :
      let densityMass : Real :=
        (restrictedDigitDensity digit : Real) *
          ((paddedRestrictedNumbers digit length).card : Real)
      (-densityMass *
          (sectionSixFirstLowCentralLargeContinuationBuchstabMainSum
              epsilon length .below +
            C * sectionSixFirstLowCentralLargeContinuationRoughErrorSum
              epsilon length .below)) <=
        sectionSixFirstLowCentralLargeStrictPieceSum
          epsilon digit length .below) :
    let X : Real := ((10 ^ length : Nat) : Real)
    let scale : Real :=
      (restrictedDigitDensity digit : Real) *
        ((paddedRestrictedNumbers digit length).card : Real) / Real.log X
    (-scale *
      (sectionSixFirstLowCentralLargeBelowIntegral epsilon + rho)) <=
      sectionSixFirstLowCentralLargeStrictPieceSum
        epsilon digit length .below := by
  let X : Real := ((10 ^ length : Nat) : Real)
  let densityMass : Real := (restrictedDigitDensity digit : Real) *
    ((paddedRestrictedNumbers digit length).card : Real)
  have hX : (1 : Real) < X := by
    dsimp only [X]
    exact_mod_cast sectionSixFirst_direct_hXNat hlength
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hgap : 0 < sectionSixThetaGap epsilon :=
    (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
  have hdensity : (0 : Real) <= (restrictedDigitDensity digit : Real) := by
    rw [restrictedDigitDensity_eq]
    split <;> norm_num
  have hdensityMass : 0 <= densityMass := by
    dsimp only [densityMass]
    exact mul_nonneg hdensity (by positivity)
  have herror :=
    sectionSixFirstLowCentralLargeContinuationRoughErrorSum_le
      epsilon hepsilon hepsilonSmall hlength .below
  have herrorScaled :
      C * sectionSixFirstLowCentralLargeContinuationRoughErrorSum
          epsilon length .below <=
        (rho / 2) / Real.log X := by
    calc
      C * sectionSixFirstLowCentralLargeContinuationRoughErrorSum
          epsilon length .below <=
          C * ((2 * Real.log 4) ^ 3 /
            (sectionSixThetaGap epsilon ^ 5 * Real.log X ^ 2)) :=
        mul_le_mul_of_nonneg_left (by simpa only [X] using herror) hC
      _ = (C * (2 * Real.log 4) ^ 3 /
          (sectionSixThetaGap epsilon ^ 5 * Real.log X)) /
            Real.log X := by
        field_simp [hgap.ne', hlogX.ne']
      _ <= (rho / 2) / Real.log X :=
        div_le_div_of_nonneg_right
          (by simpa only [X] using herrorSmall) hlogX.le
  have hbracket :
      sectionSixFirstLowCentralLargeContinuationBuchstabMainSum
          epsilon length .below +
          C * sectionSixFirstLowCentralLargeContinuationRoughErrorSum
            epsilon length .below <=
        (sectionSixFirstLowCentralLargeBelowIntegral epsilon + rho) /
          Real.log X := by
    rw [hmain]
    calc
      normalized / Real.log X +
          C * sectionSixFirstLowCentralLargeContinuationRoughErrorSum
            epsilon length .below <=
        (sectionSixFirstLowCentralLargeBelowIntegral epsilon + rho / 2) /
            Real.log X +
          (rho / 2) / Real.log X :=
        add_le_add (div_le_div_of_nonneg_right hnormalized hlogX.le)
          herrorScaled
      _ = (sectionSixFirstLowCentralLargeBelowIntegral epsilon + rho) /
          Real.log X := by ring
  dsimp only
  change -(densityMass / Real.log X) *
    (sectionSixFirstLowCentralLargeBelowIntegral epsilon + rho) <= _
  calc
    -(densityMass / Real.log X) *
        (sectionSixFirstLowCentralLargeBelowIntegral epsilon + rho) =
      -densityMass *
        ((sectionSixFirstLowCentralLargeBelowIntegral epsilon + rho) /
          Real.log X) := by ring
    _ <= -densityMass *
        (sectionSixFirstLowCentralLargeContinuationBuchstabMainSum
            epsilon length .below +
          C * sectionSixFirstLowCentralLargeContinuationRoughErrorSum
            epsilon length .below) := by
      simpa only [neg_mul] using
        neg_le_neg (mul_le_mul_of_nonneg_left hbracket hdensityMass)
    _ <= sectionSixFirstLowCentralLargeStrictPieceSum
          epsilon digit length .below := by
      simpa only [densityMass] using hfinite

theorem exists_sectionSixFirstLowCentralLargeBelow_lower
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (rho : Real) (hrho : 0 < rho) :
    ∃ length0 : Nat, 1 <= length0 ∧
      ∀ length : Nat, length0 <= length -> ∀ digit : Fin 10,
        let X : Real := ((10 ^ length : Nat) : Real)
        let scale : Real :=
          (restrictedDigitDensity digit : Real) *
            ((paddedRestrictedNumbers digit length).card : Real) /
              Real.log X
        (-scale *
          (sectionSixFirstLowCentralLargeBelowIntegral epsilon + rho)) <=
          sectionSixFirstLowCentralLargeStrictPieceSum
            epsilon digit length .below := by
  obtain ⟨C, hC, hfinite⟩ :=
    exists_sectionSixFirstLowCentralLargeContinuationFiniteLowerConstant
  let normalizedSum : Nat -> Real := fun length =>
    normalizedPrimeLogTripleSum
      (sectionSixThetaGap epsilon) (1 / 2) (10 ^ length)
      (sectionSixFirstLowCentralLargeBelowRegion epsilon)
      sectionSixFirstLowCentralLargeBelowKernel
  have hsumTendsto : Tendsto normalizedSum atTop
      (nhds (sectionSixFirstLowCentralLargeBelowIntegral epsilon)) := by
    simpa only [normalizedSum] using
      tendsto_sectionSixFirstLowCentralLargeBelowKernelSum
        epsilon hepsilon hepsilonSmall
  have hsum : ∀ᶠ length : Nat in atTop,
      normalizedSum length <=
        sectionSixFirstLowCentralLargeBelowIntegral epsilon + rho / 2 :=
    (hsumTendsto.eventually_lt_const (by linarith)).mono fun _ h => h.le
  let X : Nat -> Real := fun length => ((10 ^ length : Nat) : Real)
  let errorCoefficient : Real :=
    C * (2 * Real.log 4) ^ 3 / sectionSixThetaGap epsilon ^ 5
  have hXTendsto : Tendsto X atTop atTop := by
    simpa only [X, Nat.cast_pow, Nat.cast_ofNat] using
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : Real) < 10)
  have herrorTendsto : Tendsto
      (fun length : Nat => errorCoefficient / Real.log (X length))
      atTop (nhds 0) :=
    (Real.tendsto_log_atTop.comp hXTendsto).const_div_atTop errorCoefficient
  have herror : ∀ᶠ length : Nat in atTop,
      errorCoefficient / Real.log (X length) <= rho / 2 :=
    (herrorTendsto.eventually_lt_const (by positivity)).mono fun _ h => h.le
  have hevent : ∀ᶠ length : Nat in atTop,
      normalizedSum length <=
          sectionSixFirstLowCentralLargeBelowIntegral epsilon + rho / 2 ∧
        errorCoefficient / Real.log (X length) <= rho / 2 := by
    filter_upwards [hsum, herror] with length hsumAt herrorAt
    exact ⟨hsumAt, herrorAt⟩
  obtain ⟨length1, hlength1⟩ := eventually_atTop.mp hevent
  refine ⟨max 1 length1, le_max_left _ _, ?_⟩
  intro length hlength digit
  have hAt := hlength1 length ((le_max_right 1 length1).trans hlength)
  rcases hAt with ⟨hsumAt, herrorAt⟩
  have hlengthOne : 1 <= length := (le_max_left 1 length1).trans hlength
  have herrorAt' :
      C * (2 * Real.log 4) ^ 3 /
          (sectionSixThetaGap epsilon ^ 5 *
            Real.log ((10 ^ length : Nat) : Real)) <= rho / 2 := by
    convert herrorAt using 1
    simp only [errorCoefficient, X, div_eq_mul_inv, mul_inv_rev]
    ring
  dsimp only
  exact sectionSixFirstLowCentralLargeBelow_lower_of_bounds hC.le
    hepsilon hepsilonSmall hlengthOne digit
    (sectionSixFirstLowCentralLargeBelowBuchstabMainSum_eq_normalized
      epsilon hepsilon hepsilonSmall hlengthOne)
    hsumAt herrorAt'
    (hfinite epsilon hepsilon hepsilonSmall hlengthOne digit .below)

end

end PrimesRestrictedDigits
