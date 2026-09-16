import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserBudgetFreeBaseSplit
import PrimesRestrictedDigits.SieveAsymptotics.DimensionOneRosserModelPlusEndpoint
import PrimesRestrictedDigits.SieveAsymptotics.RosserFailureRankTail

/-!
# Full source targets and finite base saturation

Finite source targets become complete raw-model targets once their rank covers the finite
Rosser carrier. This imports bounded-log/direct bases into the complete target interface
needed by the later recursion, without claiming that recursion or its outer ledger.
-/

namespace PrimesRestrictedDigits

/-- A finite upper model sum is bounded by its raw series on the strict source
domain. -/
theorem dimensionOneRosserModelPlusPartialSum_le_raw
    (R : Nat) {s : Real} (hs : 1 < s) :
    dimensionOneRosserModelPlusPartialSum R s <=
      dimensionOneRosserModelPlusRaw s := by
  unfold dimensionOneRosserModelPlusRaw
  apply Summable.sum_le_tsum (Finset.range (R + 1))
  · intro r hr
    exact dimensionOneRosserModelPlusTerm_nonneg r s
  · exact summable_dimensionOneRosserModelPlusTerm hs

/-- Endpoint form of the upper finite-to-raw comparison. This
does not enlarge the paper's source-facing domain beyond `1 < s`. -/
theorem dimensionOneRosserModelPlusPartialSum_le_raw_of_one_le
    (R : Nat) {s : Real} (hs : 1 <= s) :
    dimensionOneRosserModelPlusPartialSum R s <=
      dimensionOneRosserModelPlusRaw s := by
  unfold dimensionOneRosserModelPlusRaw
  apply Summable.sum_le_tsum (Finset.range (R + 1))
  · intro r hr
    exact dimensionOneRosserModelPlusTerm_nonneg r s
  · exact summable_dimensionOneRosserModelPlusTerm_of_one_le hs

/-- A finite lower model sum is bounded by its raw series, including the
natural endpoint `s = 2`. -/
theorem dimensionOneRosserModelMinusPartialSum_le_raw
    (R : Nat) {s : Real} (hs : 2 <= s) :
    dimensionOneRosserModelMinusPartialSum R s <=
      dimensionOneRosserModelMinusRaw s := by
  unfold dimensionOneRosserModelMinusRaw
  apply Summable.sum_le_tsum (Finset.Icc 1 R)
  · intro r hr
    exact dimensionOneRosserModelMinusTerm_nonneg r s
  · exact summable_dimensionOneRosserModelMinusTerm hs

/-- Sharp upper finite-carrier saturation.  The weight is arbitrary and no
primality or sign assumption is needed. -/
theorem upperRosserFailurePartialSum_eq_full_of_rankCount_le
    (P : Finset Nat) (nu : Nat → Real) (level z : Real) (R : Nat)
    (hR : ((sieveFactorsBelow P z).length + 1) / 2 <= R + 1) :
    upperRosserFailurePartialSum P nu level z R =
      upperRosserFailureSum P nu level z := by
  have htail : upperRosserFailureRankTail P nu level z R = 0 := by
    unfold upperRosserFailureRankTail
    have hEmpty : Finset.Ico (R + 1)
        (((sieveFactorsBelow P z).length + 1) / 2) = ∅ :=
      Finset.Ico_eq_empty_of_le hR
    rw [hEmpty]
    simp
  have hfull := upperRosserFailureSum_eq_partial_add_rankTail
    P nu level z R
  simpa [htail] using hfull.symm

/-- Sharp lower finite-carrier saturation.  The weight is arbitrary and no
primality or sign assumption is needed. -/
theorem lowerRosserFailurePartialSum_eq_full_of_rankCount_le
    (P : Finset Nat) (nu : Nat → Real) (level z : Real) (R : Nat)
    (hR : (sieveFactorsBelow P z).length / 2 <= R) :
    lowerRosserFailurePartialSum P nu level z R =
      lowerRosserFailureSum P nu level z := by
  have htail : lowerRosserFailureRankTail P nu level z R = 0 := by
    unfold lowerRosserFailureRankTail
    have hEmpty : Finset.Icc (R + 1)
        ((sieveFactorsBelow P z).length / 2) = ∅ := by
      apply Finset.Icc_eq_empty_of_lt
      omega
    rw [hEmpty]
    simp
  have hfull := lowerRosserFailureSum_eq_partial_add_rankTail
    P nu level z R
  simpa [htail] using hfull.symm

/-- Complete upper source target with the full failure sum and raw model. -/
def dimensionOneRosserFullSourceUpperTarget
    (P : Finset Nat) (D level z s : Real) : Prop :=
  upperRosserFailureSum P (fun p => (p : Real)⁻¹) level z <
    sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
      (dimensionOneRosserModelPlusRaw s +
        D * dimensionOneRosserSourcePlusProfile (Real.log level) s)

/-- Complete lower source target with the full failure sum and raw model. -/
def dimensionOneRosserFullSourceLowerTarget
    (P : Finset Nat) (D level z s : Real) : Prop :=
  lowerRosserFailureSum P (fun p => (p : Real)⁻¹) level z <
    sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s *
      (dimensionOneRosserModelMinusRaw s +
        D * dimensionOneRosserSourceMinusProfile (Real.log level) s)

/-- A saturated partial upper source target implies the complete raw target.
The source coefficient `D` remains arbitrary. -/
theorem dimensionOneRosserFullSourceUpperTarget_of_sourceTarget
    (P : Finset Nat) (D : Real) (R : Nat) {level z s : Real}
    (hprime : ∀ p ∈ P, p.Prime) (hs : 1 < s)
    (hR : ((sieveFactorsBelow P z).length + 1) / 2 <= R + 1)
    (hTarget : dimensionOneRosserSourceUpperTarget P D R level z s) :
    dimensionOneRosserFullSourceUpperTarget P D level z s := by
  unfold dimensionOneRosserSourceUpperTarget at hTarget
  unfold dimensionOneRosserFullSourceUpperTarget
  rw [upperRosserFailurePartialSum_eq_full_of_rankCount_le
    P (fun p => (p : Real)⁻¹) level z R hR] at hTarget
  have hscale : 0 <=
      sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s :=
    div_nonneg (sieveDensityBelow_reciprocal_pos P z hprime).le (by linarith)
  have hmodel := dimensionOneRosserModelPlusPartialSum_le_raw R hs
  exact hTarget.trans_le (mul_le_mul_of_nonneg_left
    (add_le_add_left hmodel
      (D * dimensionOneRosserSourcePlusProfile (Real.log level) s)) hscale)

/-- A saturated partial lower source target implies the complete raw target.
The source coefficient `D` remains arbitrary. -/
theorem dimensionOneRosserFullSourceLowerTarget_of_sourceTarget
    (P : Finset Nat) (D : Real) (R : Nat) {level z s : Real}
    (hprime : ∀ p ∈ P, p.Prime) (hs : 2 <= s)
    (hR : (sieveFactorsBelow P z).length / 2 <= R)
    (hTarget : dimensionOneRosserSourceLowerTarget P D R level z s) :
    dimensionOneRosserFullSourceLowerTarget P D level z s := by
  unfold dimensionOneRosserSourceLowerTarget at hTarget
  unfold dimensionOneRosserFullSourceLowerTarget
  rw [lowerRosserFailurePartialSum_eq_full_of_rankCount_le
    P (fun p => (p : Real)⁻¹) level z R hR] at hTarget
  have hscale : 0 <=
      sieveDensityBelow P (fun p => (p : Real)⁻¹) z / s :=
    div_nonneg (sieveDensityBelow_reciprocal_pos P z hprime).le (by linarith)
  have hmodel := dimensionOneRosserModelMinusPartialSum_le_raw R hs
  exact hTarget.trans_le (mul_le_mul_of_nonneg_left
    (add_le_add_left hmodel
      (D * dimensionOneRosserSourceMinusProfile (Real.log level) s)) hscale)

/-- Carrier length is an automatic saturating rank for the upper target. -/
theorem dimensionOneRosserFullSourceUpperTarget_of_sourceTarget_at_carrierLength
    (P : Finset Nat) (D : Real) {level z s : Real}
    (hprime : ∀ p ∈ P, p.Prime) (hs : 1 < s)
    (hTarget : dimensionOneRosserSourceUpperTarget P D
      (sieveFactorsBelow P z).length level z s) :
    dimensionOneRosserFullSourceUpperTarget P D level z s := by
  apply dimensionOneRosserFullSourceUpperTarget_of_sourceTarget P D
    (sieveFactorsBelow P z).length hprime hs (by omega)
  exact hTarget

/-- Carrier length is an automatic saturating rank for the lower target. -/
theorem dimensionOneRosserFullSourceLowerTarget_of_sourceTarget_at_carrierLength
    (P : Finset Nat) (D : Real) {level z s : Real}
    (hprime : ∀ p ∈ P, p.Prime) (hs : 2 <= s)
    (hTarget : dimensionOneRosserSourceLowerTarget P D
      (sieveFactorsBelow P z).length level z s) :
    dimensionOneRosserFullSourceLowerTarget P D level z s := by
  apply dimensionOneRosserFullSourceLowerTarget_of_sourceTarget P D
    (sieveFactorsBelow P z).length hprime hs (by omega)
  exact hTarget

/--
one bounded-log/direct multiplier supplies both complete raw source targets. The high-log
state without a direct witness remains uncovered.
-/
theorem exists_dimensionOneRosserBudgetFreeFullBaseSplit
    (Lambda : Real) (hLambda : 0 < Lambda) :
    ∃ D S : Real, 1 <= D ∧ Real.exp 5000 + 1 <= S ∧
      (∀ {level z s : Real},
        2 <= level -> 2 <= z ->
        s = Real.log level / Real.log z -> 1 < s ->
        (Real.log level <= Lambda ∨
          dimensionOneRosserBudgetFreeDirectState S level s) ->
        ∀ (P : Finset Nat),
          (∀ p, p ∈ P -> p.Prime) ->
          dimensionOneRosserFullSourceUpperTarget P D level z s) ∧
      (∀ {level z s : Real},
        2 <= level -> 2 <= z ->
        s = Real.log level / Real.log z -> 2 <= s ->
        (Real.log level <= Lambda ∨
          dimensionOneRosserBudgetFreeDirectState S level s) ->
        ∀ (P : Finset Nat),
          (∀ p, p ∈ P -> p.Prime) ->
          dimensionOneRosserFullSourceLowerTarget P D level z s) := by
  obtain ⟨D, S, hD, hS, hUpper, hLower⟩ :=
    exists_dimensionOneRosserBudgetFreeBaseSplit Lambda hLambda
  refine ⟨D, S, hD, hS, ?_, ?_⟩
  · intro level z s hlevel hz hs hsOne hbranch P hprime
    apply
      dimensionOneRosserFullSourceUpperTarget_of_sourceTarget_at_carrierLength
        P D hprime hsOne
    exact hUpper hlevel hz hs hsOne hbranch P
      (sieveFactorsBelow P z).length hprime
  · intro level z s hlevel hz hs hsTwo hbranch P hprime
    apply
      dimensionOneRosserFullSourceLowerTarget_of_sourceTarget_at_carrierLength
        P D hprime hsTwo
    exact hLower hlevel hz hs hsTwo hbranch P
      (sieveFactorsBelow P z).length hprime

end PrimesRestrictedDigits
