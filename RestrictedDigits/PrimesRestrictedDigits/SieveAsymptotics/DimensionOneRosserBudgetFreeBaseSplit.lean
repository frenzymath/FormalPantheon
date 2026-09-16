import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSmallLogSourceAbsorption
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserSourceDirectTargets

/-!
# Budget-free source base split

This composes the bounded-log all-rank base with the independent high-seed direct branch. The
direct state is deliberately a separate predicate, so its witness is fixed before the carrier
and rank. The intermediate high-log ready strip remains outside this adapter.
-/

namespace PrimesRestrictedDigits

/- The source-cutoff witness is independent of the prime carrier and rank. -/
def dimensionOneRosserBudgetFreeDirectState
    (S level s : Real) : Prop :=
  ∃ s0 : Real, S <= s0 ∧ s0 <= s ∧
    Real.exp 1 <= Real.log level ∧
    s0 ^ (50 : Nat) = Real.log level *
      (Real.log (Real.log level)) ^ (3 : Nat)

/-- The shared multiplier used by the two rank-uniform base branches. -/
noncomputable def dimensionOneRosserBudgetFreeBaseMultiplier
    (Lambda : Real) : Real :=
  max 1 (dimensionOneRosserSmallLogAbsorptionConstant Lambda)

private theorem upperTarget_mono_in_multiplier
    (P : Finset Nat) (R : Nat) {D₁ D₂ level z s : Real}
    (hD : D₁ <= D₂) (hprime : forall p, p ∈ P -> p.Prime)
    (hlevel : 2 <= level) (hsOne : 1 < s)
    (hTarget : dimensionOneRosserSourceUpperTarget P D₁ R level z s) :
    dimensionOneRosserSourceUpperTarget P D₂ R level z s := by
  have hsPos : 0 < s := by linarith
  have hL : 0 < Real.log level := Real.log_pos (by linarith)
  have hV : 0 <= sieveDensityBelow P (fun p => (p : Real)⁻¹) z :=
    (sieveDensityBelow_reciprocal_pos P z hprime).le
  have hprofile :
      0 <= dimensionOneRosserSourcePlusProfile (Real.log level) s := by
    unfold dimensionOneRosserSourcePlusProfile
    exact mul_nonneg (Real.rpow_pos_of_pos hL _).le
      (dimensionOneRosserPlusArtificialAux_pos hL hsPos).le
  have hscale :
      0 <= sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s :=
    div_nonneg hV hsPos.le
  unfold dimensionOneRosserSourceUpperTarget at hTarget ⊢
  have hmul := mul_le_mul_of_nonneg_right hD hprofile
  have hcoef :
      dimensionOneRosserModelPlusPartialSum R s +
          D₁ * dimensionOneRosserSourcePlusProfile (Real.log level) s <=
        dimensionOneRosserModelPlusPartialSum R s +
          D₂ * dimensionOneRosserSourcePlusProfile (Real.log level) s := by
    simpa [add_comm] using add_le_add_left hmul
      (dimensionOneRosserModelPlusPartialSum R s)
  exact hTarget.trans_le (mul_le_mul_of_nonneg_left hcoef hscale)

private theorem lowerTarget_mono_in_multiplier
    (P : Finset Nat) (R : Nat) {D₁ D₂ level z s : Real}
    (hD : D₁ <= D₂) (hprime : forall p, p ∈ P -> p.Prime)
    (hlevel : 2 <= level) (hsTwo : 2 <= s)
    (hTarget : dimensionOneRosserSourceLowerTarget P D₁ R level z s) :
    dimensionOneRosserSourceLowerTarget P D₂ R level z s := by
  have hsPos : 0 < s := by linarith
  have hL : 0 < Real.log level := Real.log_pos (by linarith)
  have hV : 0 <= sieveDensityBelow P (fun p => (p : Real)⁻¹) z :=
    (sieveDensityBelow_reciprocal_pos P z hprime).le
  have hprofile :
      0 <= dimensionOneRosserSourceMinusProfile (Real.log level) s := by
    unfold dimensionOneRosserSourceMinusProfile
    exact mul_nonneg (Real.rpow_pos_of_pos hL _).le
      (dimensionOneRosserMinusArtificialAux_pos hL hsPos).le
  have hscale :
      0 <= sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s :=
    div_nonneg hV hsPos.le
  unfold dimensionOneRosserSourceLowerTarget at hTarget ⊢
  have hmul := mul_le_mul_of_nonneg_right hD hprofile
  have hcoef :
      dimensionOneRosserModelMinusPartialSum R s +
          D₁ * dimensionOneRosserSourceMinusProfile (Real.log level) s <=
        dimensionOneRosserModelMinusPartialSum R s +
          D₂ * dimensionOneRosserSourceMinusProfile (Real.log level) s := by
    simpa [add_comm] using add_le_add_left hmul
      (dimensionOneRosserModelMinusPartialSum R s)
  exact hTarget.trans_le (mul_le_mul_of_nonneg_left hcoef hscale)

/-- One multiplier supports the bounded-log and direct high-seed branches.

The state predicate is quantified before `P` and `R`.  No assertion is made
for a high-log state lacking a direct witness.
-/
theorem exists_dimensionOneRosserBudgetFreeBaseSplit
    (Lambda : Real) (hLambda : 0 < Lambda) :
    ∃ D S : Real, 1 <= D ∧ Real.exp 5000 + 1 <= S ∧
      (forall {level z s : Real},
        2 <= level -> 2 <= z ->
        s = Real.log level / Real.log z -> 1 < s ->
        (Real.log level <= Lambda ∨
          dimensionOneRosserBudgetFreeDirectState S level s) ->
        forall (P : Finset Nat) (R : Nat),
          (forall p, p ∈ P -> p.Prime) ->
          dimensionOneRosserSourceUpperTarget P D R level z s) ∧
      (forall {level z s : Real},
        2 <= level -> 2 <= z ->
        s = Real.log level / Real.log z -> 2 <= s ->
        (Real.log level <= Lambda ∨
          dimensionOneRosserBudgetFreeDirectState S level s) ->
        forall (P : Finset Nat) (R : Nat),
          (forall p, p ∈ P -> p.Prime) ->
          dimensionOneRosserSourceLowerTarget P D R level z s) := by
  obtain ⟨S, hS, hDirect⟩ := exists_dimensionOneRosserSourceDirectTargets_ge
  let D : Real := dimensionOneRosserBudgetFreeBaseMultiplier Lambda
  have hD : 1 <= D := by
    dsimp [D, dimensionOneRosserBudgetFreeBaseMultiplier]
    exact le_max_left _ _
  have hDsmall :
      dimensionOneRosserSmallLogAbsorptionConstant Lambda <= D := by
    dsimp [D, dimensionOneRosserBudgetFreeBaseMultiplier]
    exact le_max_right _ _
  refine ⟨D, S, hD, hS, ?_, ?_⟩
  · intro level z s hlevel hz hs hsOne hbranch P R hprime
    rcases hbranch with hlog | hdirectState
    · have hsmall :=
        (dimensionOneRosserSmallLogSourceTargets Lambda hLambda).1
          P R hprime hlevel hz hs hsOne hlog
      exact upperTarget_mono_in_multiplier P R hDsmall hprime hlevel
        hsOne hsmall
    · rcases hdirectState with ⟨s0, hs0S, hs0s, hLExp, hsource⟩
      exact (hDirect P R hD hprime hlevel hz hs hs0S hs0s hLExp hsource).1
  · intro level z s hlevel hz hs hsTwo hbranch P R hprime
    rcases hbranch with hlog | hdirectState
    · have hsmall :=
        (dimensionOneRosserSmallLogSourceTargets Lambda hLambda).2
          P R hprime hlevel hz hs hsTwo hlog
      exact lowerTarget_mono_in_multiplier P R hDsmall hprime hlevel
        hsTwo hsmall
    · rcases hdirectState with ⟨s0, hs0S, hs0s, hLExp, hsource⟩
      exact (hDirect P R hD hprime hlevel hz hs hs0S hs0s hLExp hsource).2

end PrimesRestrictedDigits
