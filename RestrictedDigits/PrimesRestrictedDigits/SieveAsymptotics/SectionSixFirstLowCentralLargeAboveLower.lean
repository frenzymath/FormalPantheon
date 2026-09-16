import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveBridges
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveSourceIntegrals
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeContinuationFiniteLower

/-!
# Eventual lower bound for the low central-large above continuation

The finite continuation estimate is combined with normalized prime-log triple convergence and
the cubic log-prime error bound. This is Maynard's `I_4` contribution, with the role-labelled
prime coordinates and full strict sifted term retained.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 141--142, Eq. (6.11).
-/

open Filter
open scoped Topology

namespace PrimesRestrictedDigits

noncomputable section

theorem exists_sectionSixFirstLowCentralLargeAbove_lower
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
          (sectionSixFirstLowCentralLargeAboveIntegral epsilon + rho)) <=
          sectionSixFirstLowCentralLargeStrictPieceSum
            epsilon digit length .above := by
  obtain ⟨C, hC, hfinite⟩ :=
    exists_sectionSixFirstLowCentralLargeContinuationFiniteLowerConstant
  let normalizedSum : Nat -> Real := fun length =>
    normalizedPrimeLogTripleSum
      (sectionSixThetaGap epsilon) (1 / 2) (10 ^ length)
      (sectionSixFirstLowCentralLargeAboveRegion epsilon)
      sectionSixFirstLowCentralLargeAboveKernel
  have hsumTendsto : Tendsto normalizedSum atTop
      (nhds (sectionSixFirstLowCentralLargeAboveIntegral epsilon)) := by
    simpa only [normalizedSum] using
      tendsto_sectionSixFirstLowCentralLargeAboveKernelSum
        epsilon hepsilon hepsilonSmall
  have hsum : ∀ᶠ length : Nat in atTop,
      normalizedSum length <=
        sectionSixFirstLowCentralLargeAboveIntegral epsilon + rho / 2 :=
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
          sectionSixFirstLowCentralLargeAboveIntegral epsilon + rho / 2 ∧
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
  exact sectionSixFirstLowCentralLargeContinuation_lower_of_bounds hC.le
    hepsilon hepsilonSmall hlengthOne digit .above
    (sectionSixFirstLowCentralLargeAboveBuchstabMainSum_eq_normalized
      epsilon hepsilon hepsilonSmall hlengthOne)
    hsumAt herrorAt'
    (hfinite epsilon hepsilon hepsilonSmall hlengthOne digit .above)

end

end PrimesRestrictedDigits
