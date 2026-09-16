import PrimesRestrictedDigits.SieveAsymptotics.DecimalDensityLowerReserve
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSmallLogProfileFloor
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceTargets

/-!
# Small-log all-rank source absorption

The finite estimates choose one explicit multiplier before the carrier, rank, and
source state, and close both source targets in the bounded log regime. This is a project-local
finite base, not Iwaniec's factorial tail estimate.
-/

namespace PrimesRestrictedDigits

noncomputable def dimensionOneRosserSmallLogAbsorptionConstant
    (Lambda : Real) : Real :=
  2 * (2 : Real) ^ Nat.ceil (Real.exp Lambda) *
      dimensionOneRosserSmallLogCoordinateCap Lambda /
    ((1 / 2 : Real) ^ Nat.ceil (Real.exp Lambda) *
      dimensionOneRosserSmallLogProfileFloor Lambda)

theorem dimensionOneRosserSmallLogAbsorptionConstant_pos
    {Lambda : Real} (hLambda : 0 < Lambda) :
    0 < dimensionOneRosserSmallLogAbsorptionConstant Lambda := by
  have hF : 0 < (2 : Real) ^ Nat.ceil (Real.exp Lambda) :=
    pow_pos (by norm_num) _
  have hv : 0 < (1 / 2 : Real) ^ Nat.ceil (Real.exp Lambda) :=
    pow_pos (by norm_num) _
  have hU : 0 < dimensionOneRosserSmallLogCoordinateCap Lambda := by
    exact (by norm_num : (0 : Real) < 2).trans_le (le_max_left _ _)
  have hP : 0 < dimensionOneRosserSmallLogProfileFloor Lambda :=
    dimensionOneRosserSmallLogProfileFloor_pos hLambda
  unfold dimensionOneRosserSmallLogAbsorptionConstant
  exact div_pos
    (mul_pos (mul_pos (by norm_num) hF) hU)
    (mul_pos hv hP)

private theorem smallLog_density_ge_fixed_power
    (P : Finset Nat) {level z s Lambda : Real}
    (hprime : forall p, p ∈ P -> p.Prime)
    (hlevel : 2 <= level) (hz : 2 <= z)
    (hs : s = Real.log level / Real.log z)
    (hsOne : 1 < s) (hlog : Real.log level <= Lambda) :
    (1 / 2 : Real) ^ Nat.ceil (Real.exp Lambda) <=
      sieveDensityBelow P (fun p => (p : Real)⁻¹) z := by
  have hlength := sieveFactorsBelow_length_le_ceil_exp_of_log_cap
    P hlevel hz hs hsOne hlog
  have hpow : (1 / 2 : Real) ^ Nat.ceil (Real.exp Lambda) <=
      (1 / 2 : Real) ^ (sieveFactorsBelow P z).length :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hlength
  exact hpow.trans (sieveDensityBelow_reciprocal_ge_half_pow_length
    P z hprime)

private theorem smallLog_absorption_identity
    {F v U Q : Real} (hF : 0 < F) (hv : 0 < v)
    (hU : 0 < U) (hQ : 0 < Q) :
    (v / U) * ((2 * F * U / (v * Q)) * Q) = 2 * F := by
  field_simp [ne_of_gt hv, ne_of_gt hU, ne_of_gt hQ]

private theorem smallLog_failure_lt_source_expression
    {failure F V v s U Q profile model D : Real}
    (hfailure : failure <= F) (hF : 0 < F)
    (hvV : v <= V) (hV : 0 <= V)
    (hs : 0 < s) (hsU : s <= U)
    (hQ : 0 < Q) (hQprofile : Q <= profile) (hD : 0 <= D)
    (hmodel : 0 <= model)
    (hidentity : (v / U) * (D * Q) = 2 * F) :
    failure < V / s * (model + D * profile) := by
  have hscale : v / U <= V / s :=
    div_le_div₀ hV hvV hs hsU
  have hDQ : D * Q <= D * profile :=
    mul_le_mul_of_nonneg_left hQprofile hD
  have hprod : (v / U) * (D * Q) <=
      (V / s) * (D * profile) := by
    exact mul_le_mul hscale hDQ
      (mul_nonneg hD hQ.le) (div_nonneg hV hs.le)
  have hstrict : F < V / s * (D * profile) := by
    calc
      F < 2 * F := by nlinarith
      _ = (v / U) * (D * Q) := hidentity.symm
      _ <= V / s * (D * profile) := hprod
  have hmodelAdd : D * profile <= model + D * profile := by
    linarith
  exact (hfailure.trans_lt hstrict).trans_le
    (mul_le_mul_of_nonneg_left hmodelAdd (div_nonneg hV hs.le))

theorem dimensionOneRosserSmallLogSourceTargets
    (Lambda : Real) (hLambda : 0 < Lambda) :
    (forall (P : Finset Nat) (R : Nat) {level z s : Real},
      (forall p, p ∈ P -> p.Prime) ->
      2 <= level -> 2 <= z ->
      s = Real.log level / Real.log z ->
      1 < s -> Real.log level <= Lambda ->
      dimensionOneRosserSourceUpperTarget P
        (dimensionOneRosserSmallLogAbsorptionConstant Lambda)
        R level z s) ∧
    (forall (P : Finset Nat) (R : Nat) {level z s : Real},
      (forall p, p ∈ P -> p.Prime) ->
      2 <= level -> 2 <= z ->
      s = Real.log level / Real.log z ->
      2 <= s -> Real.log level <= Lambda ->
      dimensionOneRosserSourceLowerTarget P
        (dimensionOneRosserSmallLogAbsorptionConstant Lambda)
        R level z s) := by
  have hD : 0 < dimensionOneRosserSmallLogAbsorptionConstant Lambda :=
    dimensionOneRosserSmallLogAbsorptionConstant_pos hLambda
  have hF : 0 < (2 : Real) ^ Nat.ceil (Real.exp Lambda) :=
    pow_pos (by norm_num) _
  have hv : 0 < (1 / 2 : Real) ^ Nat.ceil (Real.exp Lambda) :=
    pow_pos (by norm_num) _
  have hU : 0 < dimensionOneRosserSmallLogCoordinateCap Lambda := by
    exact (by norm_num : (0 : Real) < 2).trans_le (le_max_left _ _)
  have hQ : 0 < dimensionOneRosserSmallLogProfileFloor Lambda :=
    dimensionOneRosserSmallLogProfileFloor_pos hLambda
  have hidentity :
      ((1 / 2 : Real) ^ Nat.ceil (Real.exp Lambda) /
        dimensionOneRosserSmallLogCoordinateCap Lambda) *
        (dimensionOneRosserSmallLogAbsorptionConstant Lambda *
          dimensionOneRosserSmallLogProfileFloor Lambda) =
      2 * (2 : Real) ^ Nat.ceil (Real.exp Lambda) := by
    unfold dimensionOneRosserSmallLogAbsorptionConstant
    exact smallLog_absorption_identity hF hv hU hQ
  constructor
  · intro P R level z s hprime hlevel hz hs hsUpper hlog
    have hsOne : 1 <= s := le_of_lt hsUpper
    have hsPos : 0 < s := by linarith
    have hVpos := sieveDensityBelow_reciprocal_pos P z hprime
    have hVlower := smallLog_density_ge_fixed_power P hprime
      hlevel hz hs hsUpper hlog
    have hpartial := upperRosserFailurePartialSum_le_failureSum
      P level z R hprime
    have hcomplete :=
      upperRosserFailureSum_reciprocal_le_two_pow_ceil_exp_of_log_cap
        P hprime hlevel hz hs hsUpper hlog
    have hfailure := hpartial.trans hcomplete
    have hprofile :=
      dimensionOneRosserSmallLogProfileFloor_le_sourcePlusProfile
        hlevel hz hs hsOne hlog
    have hsCap := dimensionOneRosserSourceCoordinate_le_smallLogCoordinateCap
      hlevel hz hs hlog
    have hmodel := dimensionOneRosserModelPlusPartialSum_nonneg R s
    unfold dimensionOneRosserSourceUpperTarget
    exact smallLog_failure_lt_source_expression hfailure hF hVlower
      hVpos.le hsPos hsCap hQ hprofile hD.le hmodel hidentity
  · intro P R level z s hprime hlevel hz hs hsLower hlog
    have hsOne : 1 < s := by linarith
    have hsPos : 0 < s := by linarith
    have hVpos := sieveDensityBelow_reciprocal_pos P z hprime
    have hVlower := smallLog_density_ge_fixed_power P hprime
      hlevel hz hs hsOne hlog
    have hpartial := lowerRosserFailurePartialSum_le_failureSum
      P level z R hprime
    have hcomplete :=
      lowerRosserFailureSum_reciprocal_le_two_pow_ceil_exp_of_log_cap
        P hprime hlevel hz hs hsOne hlog
    have hfailure := hpartial.trans hcomplete
    have hprofile :=
      dimensionOneRosserSmallLogProfileFloor_le_sourceMinusProfile
        hlevel hz hs hsLower hlog
    have hsCap := dimensionOneRosserSourceCoordinate_le_smallLogCoordinateCap
      hlevel hz hs hlog
    have hmodel := dimensionOneRosserModelMinusPartialSum_nonneg R s
    unfold dimensionOneRosserSourceLowerTarget
    exact smallLog_failure_lt_source_expression hfailure hF hVlower
      hVpos.le hsPos hsCap hQ hprofile hD.le hmodel hidentity

theorem exists_dimensionOneRosserSmallLogSourceTargets
    (Lambda : Real) (hLambda : 0 < Lambda) :
    ∃ D : Real, 0 < D ∧
      (forall (P : Finset Nat) (R : Nat) {level z s : Real},
        (forall p, p ∈ P -> p.Prime) ->
        2 <= level -> 2 <= z ->
        s = Real.log level / Real.log z ->
        1 < s -> Real.log level <= Lambda ->
        dimensionOneRosserSourceUpperTarget P D R level z s) ∧
      (forall (P : Finset Nat) (R : Nat) {level z s : Real},
        (forall p, p ∈ P -> p.Prime) ->
        2 <= level -> 2 <= z ->
        s = Real.log level / Real.log z ->
        2 <= s -> Real.log level <= Lambda ->
        dimensionOneRosserSourceLowerTarget P D R level z s) := by
  refine ⟨dimensionOneRosserSmallLogAbsorptionConstant Lambda,
    dimensionOneRosserSmallLogAbsorptionConstant_pos hLambda, ?_⟩
  exact dimensionOneRosserSmallLogSourceTargets Lambda hLambda

end PrimesRestrictedDigits
