import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowQuadrupleConvergence
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowQuadrupleSourceIntegrals
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowQuadrupleBridges
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowQuadrupleRoughError
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowQuadrupleFiniteLower

/-!
# Eventual lower bound for the low-below clean quadruple term

The finite strict-rough estimate is combined with normalized prime-log fourfold convergence
and the fourfold log-prime error bound. This is the clean `I_6` low-below quadruple
contribution, with coefficient one and the full strict term.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 143--144, Eq. (6.13), region `R_4`.
-/

open Filter
open scoped Topology

namespace PrimesRestrictedDigits

noncomputable section

private theorem sectionSixFirstLowBelowQuadruple_lower_of_bounds
    {C epsilon rho normalized : Real}
    (hC : 0 <= C) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length) (digit : Fin 10)
    (hmain :
      sectionSixFirstLowBelowQuadrupleBuchstabMainSum
          epsilon length =
        normalized / Real.log ((10 ^ length : Nat) : Real))
    (hnormalized : normalized <=
      sectionSixFirstLowBelowQuadrupleIntegral epsilon + rho / 2)
    (herrorSmall :
      C * (2 * Real.log 4) ^ 4 /
          (sectionSixThetaGap epsilon ^ 6 *
            Real.log ((10 ^ length : Nat) : Real)) <= rho / 2)
    (hfinite :
      let densityMass : Real :=
        (restrictedDigitDensity digit : Real) *
          ((paddedRestrictedNumbers digit length).card : Real)
      (-densityMass *
          (sectionSixFirstLowBelowQuadrupleBuchstabMainSum
              epsilon length +
            C * sectionSixFirstLowBelowQuadrupleRoughErrorSum
              epsilon length) <=
        sectionSixFirstLowBelowStrictQuadrupleSum
          epsilon digit length)) :
    let X : Real := ((10 ^ length : Nat) : Real)
    let scale : Real :=
      (restrictedDigitDensity digit : Real) *
        ((paddedRestrictedNumbers digit length).card : Real) / Real.log X
    (-scale *
        (sectionSixFirstLowBelowQuadrupleIntegral epsilon + rho) <=
      sectionSixFirstLowBelowStrictQuadrupleSum
        epsilon digit length) := by
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
    sectionSixFirstLowBelowQuadrupleRoughErrorSum_le
      epsilon hepsilon hepsilonSmall hlength
  have herrorScaled :
      C * sectionSixFirstLowBelowQuadrupleRoughErrorSum
          epsilon length <=
        (rho / 2) / Real.log X := by
    calc
      C * sectionSixFirstLowBelowQuadrupleRoughErrorSum
          epsilon length <=
          C * ((2 * Real.log 4) ^ 4 /
            (sectionSixThetaGap epsilon ^ 6 * Real.log X ^ 2)) :=
        mul_le_mul_of_nonneg_left (by simpa only [X] using herror) hC
      _ = (C * (2 * Real.log 4) ^ 4 /
          (sectionSixThetaGap epsilon ^ 6 * Real.log X)) /
            Real.log X := by
        field_simp [hgap.ne', hlogX.ne']
      _ <= (rho / 2) / Real.log X :=
        div_le_div_of_nonneg_right
          (by simpa only [X] using herrorSmall) hlogX.le
  have hbracket :
      sectionSixFirstLowBelowQuadrupleBuchstabMainSum
          epsilon length +
          C * sectionSixFirstLowBelowQuadrupleRoughErrorSum
            epsilon length <=
        (sectionSixFirstLowBelowQuadrupleIntegral epsilon + rho) /
          Real.log X := by
    rw [hmain]
    calc
      normalized / Real.log X +
          C * sectionSixFirstLowBelowQuadrupleRoughErrorSum
            epsilon length <=
        (sectionSixFirstLowBelowQuadrupleIntegral epsilon + rho / 2) /
            Real.log X +
          (rho / 2) / Real.log X :=
        add_le_add (div_le_div_of_nonneg_right hnormalized hlogX.le)
          herrorScaled
      _ = (sectionSixFirstLowBelowQuadrupleIntegral epsilon + rho) /
          Real.log X := by ring
  dsimp only
  change -(densityMass / Real.log X) *
    (sectionSixFirstLowBelowQuadrupleIntegral epsilon + rho) <= _
  calc
    -(densityMass / Real.log X) *
        (sectionSixFirstLowBelowQuadrupleIntegral epsilon + rho) =
      -densityMass *
        ((sectionSixFirstLowBelowQuadrupleIntegral epsilon + rho) /
          Real.log X) := by ring
    _ <= -densityMass *
        (sectionSixFirstLowBelowQuadrupleBuchstabMainSum
            epsilon length +
          C * sectionSixFirstLowBelowQuadrupleRoughErrorSum
            epsilon length) := by
      simpa only [neg_mul] using
        neg_le_neg (mul_le_mul_of_nonneg_left hbracket hdensityMass)
    _ <= sectionSixFirstLowBelowStrictQuadrupleSum
          epsilon digit length := by
      simpa only [densityMass] using hfinite

theorem exists_sectionSixFirstLowBelowStrictQuadrupleSum_lower
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (rho : Real) (hrho : 0 < rho) :
    ∃ length0 : Nat, 1 <= length0 ∧
      ∀ length : Nat, length0 <= length ->
        ∀ digit : Fin 10,
          let X : Real := ((10 ^ length : Nat) : Real)
          let scale : Real :=
            (restrictedDigitDensity digit : Real) *
              ((paddedRestrictedNumbers digit length).card : Real) /
                Real.log X
          (-scale *
                (sectionSixFirstLowBelowQuadrupleIntegral epsilon + rho) <=
            sectionSixFirstLowBelowStrictQuadrupleSum
              epsilon digit length) := by
  obtain ⟨C, hC, hfinite⟩ :=
    exists_sectionSixFirstLowBelowQuadrupleFiniteLowerConstant
  let normalizedSum : Nat -> Real := fun length =>
    normalizedPrimeLogFourfoldSum
      (sectionSixThetaGap epsilon) (sectionSixThetaOne epsilon) (10 ^ length)
      (sectionSixFirstLowBelowQuadrupleRegion epsilon)
      sectionSixFirstLowBelowQuadrupleKernel
  have hsumTendsto : Tendsto normalizedSum atTop
      (nhds (sectionSixFirstLowBelowQuadrupleIntegral epsilon)) := by
    simpa only [normalizedSum] using
      tendsto_sectionSixFirstLowBelowQuadrupleKernelSum
        epsilon hepsilon hepsilonSmall
  have hsum : ∀ᶠ length : Nat in atTop,
      normalizedSum length <=
        sectionSixFirstLowBelowQuadrupleIntegral epsilon + rho / 2 :=
    (hsumTendsto.eventually_lt_const (by linarith)).mono fun _ h => h.le
  let X : Nat -> Real := fun length => ((10 ^ length : Nat) : Real)
  let errorCoefficient : Real :=
    C * (2 * Real.log 4) ^ 4 / sectionSixThetaGap epsilon ^ 6
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
          sectionSixFirstLowBelowQuadrupleIntegral epsilon + rho / 2 ∧
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
      C * (2 * Real.log 4) ^ 4 /
          (sectionSixThetaGap epsilon ^ 6 *
            Real.log ((10 ^ length : Nat) : Real)) <= rho / 2 := by
    convert herrorAt using 1
    simp only [errorCoefficient, X, div_eq_mul_inv, mul_inv_rev]
    ring
  dsimp only
  exact sectionSixFirstLowBelowQuadruple_lower_of_bounds hC.le
    hepsilon hepsilonSmall hlengthOne digit
    (sectionSixFirstLowBelowQuadrupleBuchstabMainSum_eq_normalized
      epsilon hepsilon hepsilonSmall hlengthOne)
    hsumAt herrorAt'
    (hfinite epsilon hepsilon hepsilonSmall hlengthOne digit)

end

end PrimesRestrictedDigits
