import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeTerminalFiniteLower
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeTerminalSourceIntegrals

/-!
# Eventual lower bound for the low central-large terminal term

The finite parameter-two estimate is combined with normalized prime-log pair convergence and
the pair-generic log-square error bound.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, p. 141, Eqs. (6.8)--(6.9).
-/

open Filter MeasureTheory Set
open scoped Topology

namespace PrimesRestrictedDigits

noncomputable section

private theorem sectionSixFirstLowCentralLargeTerminal_lower_of_bounds
    {C epsilon rho normalized : Real}
    (hC : 0 <= C) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length) (digit : Fin 10)
    (hmain : sectionSixFirstLowCentralLargeTerminalMainSum epsilon length =
      normalized / Real.log ((10 ^ length : Nat) : Real))
    (hnormalized : normalized <=
      sectionSixFirstLowCentralLargeTerminalIntegral epsilon + rho / 2)
    (herrorSmall :
      C * (2 * Real.log 4) ^ 2 /
          (sectionSixThetaGap epsilon ^ 4 *
            Real.log ((10 ^ length : Nat) : Real)) <= rho / 2)
    (hfinite :
      let densityMass : Real :=
        (restrictedDigitDensity digit : Real) *
          ((paddedRestrictedNumbers digit length).card : Real);
      (-densityMass *
          (sectionSixFirstLowCentralLargeTerminalMainSum epsilon length +
            C * sectionSixFirstPairRoughErrorSum epsilon length
              .lowCentralLarge)) <=
        sectionSixFirstLowCentralLargeTerminalSum epsilon digit length) :
    let X : Real := ((10 ^ length : Nat) : Real);
    let scale : Real :=
      (restrictedDigitDensity digit : Real) *
        ((paddedRestrictedNumbers digit length).card : Real) / Real.log X;
    (-scale *
      (sectionSixFirstLowCentralLargeTerminalIntegral epsilon + rho)) <=
      sectionSixFirstLowCentralLargeTerminalSum epsilon digit length := by
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
  have herror := sectionSixFirstPairRoughErrorSum_le epsilon hepsilon
    hepsilonSmall hlength .lowCentralLarge
  have herrorScaled :
      C * sectionSixFirstPairRoughErrorSum epsilon length .lowCentralLarge <=
        (rho / 2) / Real.log X := by
    calc
      C * sectionSixFirstPairRoughErrorSum epsilon length .lowCentralLarge <=
          C * ((2 * Real.log 4) ^ 2 /
            (sectionSixThetaGap epsilon ^ 4 * Real.log X ^ 2)) :=
        mul_le_mul_of_nonneg_left (by simpa only [X] using herror) hC
      _ = (C * (2 * Real.log 4) ^ 2 /
          (sectionSixThetaGap epsilon ^ 4 * Real.log X)) /
            Real.log X := by
        field_simp [hgap.ne', hlogX.ne']
      _ <= (rho / 2) / Real.log X :=
        div_le_div_of_nonneg_right
          (by simpa only [X] using herrorSmall) hlogX.le
  have hbracket :
      sectionSixFirstLowCentralLargeTerminalMainSum epsilon length +
          C * sectionSixFirstPairRoughErrorSum epsilon length
            .lowCentralLarge <=
        (sectionSixFirstLowCentralLargeTerminalIntegral epsilon + rho) /
          Real.log X := by
    rw [hmain]
    calc
      normalized / Real.log X +
          C * sectionSixFirstPairRoughErrorSum epsilon length
            .lowCentralLarge <=
        (sectionSixFirstLowCentralLargeTerminalIntegral epsilon + rho / 2) /
            Real.log X +
          (rho / 2) / Real.log X :=
        add_le_add (div_le_div_of_nonneg_right hnormalized hlogX.le)
          herrorScaled
      _ = (sectionSixFirstLowCentralLargeTerminalIntegral epsilon + rho) /
          Real.log X := by ring
  dsimp only
  change -(densityMass / Real.log X) *
    (sectionSixFirstLowCentralLargeTerminalIntegral epsilon + rho) <= _
  calc
    -(densityMass / Real.log X) *
        (sectionSixFirstLowCentralLargeTerminalIntegral epsilon + rho) =
      -densityMass *
        ((sectionSixFirstLowCentralLargeTerminalIntegral epsilon + rho) /
          Real.log X) := by ring
    _ <= -densityMass *
        (sectionSixFirstLowCentralLargeTerminalMainSum epsilon length +
          C * sectionSixFirstPairRoughErrorSum epsilon length
            .lowCentralLarge) := by
      simpa only [neg_mul] using
        neg_le_neg (mul_le_mul_of_nonneg_left hbracket hdensityMass)
    _ <= sectionSixFirstLowCentralLargeTerminalSum epsilon digit length := by
      simpa only [densityMass] using hfinite

theorem exists_sectionSixFirstLowCentralLargeTerminal_lower
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
            (sectionSixFirstLowCentralLargeTerminalIntegral epsilon +
              rho)) <=
            sectionSixFirstLowCentralLargeTerminalSum
              epsilon digit length := by
  obtain ⟨C, hC, hfinite⟩ :=
    exists_sectionSixFirstLowCentralLargeTerminalFiniteLowerConstant
  let normalizedSum : Nat -> Real := fun length =>
    normalizedPrimeLogPairSum
      (sectionSixThetaGap epsilon) (1 / 2) (10 ^ length)
      (sectionSixFirstLowCentralLargeTerminalRegion epsilon)
      sectionSixFirstLowCentralLargeTerminalKernel
  have hsumTendsto : Tendsto normalizedSum atTop
      (nhds (sectionSixFirstLowCentralLargeTerminalIntegral epsilon)) := by
    simpa only [normalizedSum] using
      tendsto_sectionSixFirstLowCentralLargeTerminalKernelSum
        epsilon hepsilon hepsilonSmall
  have hsum : ∀ᶠ length : Nat in atTop,
      normalizedSum length <=
        sectionSixFirstLowCentralLargeTerminalIntegral epsilon + rho / 2 :=
    (hsumTendsto.eventually_lt_const (by linarith)).mono fun _ h => h.le
  let X : Nat -> Real := fun length => ((10 ^ length : Nat) : Real)
  let errorCoefficient : Real :=
    C * (2 * Real.log 4) ^ 2 / sectionSixThetaGap epsilon ^ 4
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
  let gap : Real := sectionSixThetaGap epsilon
  have hgap : 0 < gap := by
    simpa only [gap] using
      (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
  obtain ⟨endpointLength, hendpoint⟩ :=
    exists_decimalEndpointThreshold gap hgap
  have hevent : ∀ᶠ length : Nat in atTop,
      normalizedSum length <=
          sectionSixFirstLowCentralLargeTerminalIntegral epsilon + rho / 2 ∧
        errorCoefficient / Real.log (X length) <= rho / 2 ∧
        endpointLength <= length := by
    filter_upwards [hsum, herror, eventually_ge_atTop endpointLength] with
      length hsumAt herrorAt hendpointAt
    exact ⟨hsumAt, herrorAt, hendpointAt⟩
  obtain ⟨length1, hlength1⟩ := eventually_atTop.mp hevent
  refine ⟨max 1 length1, le_max_left _ _, ?_⟩
  intro length hlength digit
  have hAt := hlength1 length ((le_max_right 1 length1).trans hlength)
  rcases hAt with ⟨hsumAt, herrorAt, hendpointAt⟩
  have hendpointAt' := hendpoint length hendpointAt
  have hlengthOne : 1 <= length := hendpointAt'.1
  have hfour : (4 : Real) <= sectionSixZOne epsilon (X length) := by
    have hfive : (5 : Real) <= (X length) ^ gap := by
      simpa only [X] using hendpointAt'.2.1
    simpa only [sectionSixZOne, gap] using
      (show (4 : Real) <= (X length) ^ gap by linarith)
  have herrorAt' :
      C * (2 * Real.log 4) ^ 2 /
          (sectionSixThetaGap epsilon ^ 4 *
            Real.log ((10 ^ length : Nat) : Real)) <= rho / 2 := by
    convert herrorAt using 1
    simp only [errorCoefficient, X, div_eq_mul_inv, mul_inv_rev]
    ring
  dsimp only
  exact sectionSixFirstLowCentralLargeTerminal_lower_of_bounds hC.le
    hepsilon hepsilonSmall hlengthOne digit
    (sectionSixFirstLowCentralLargeTerminalMainSum_eq_normalized
      epsilon hepsilon hepsilonSmall hlengthOne)
    hsumAt herrorAt'
    (hfinite epsilon digit length (by simpa only [X] using hfour))

end

end PrimesRestrictedDigits
