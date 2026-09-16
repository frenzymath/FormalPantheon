import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectQuarterTieAbsorption
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstRepeatedFiniteBound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# First-ledger repeated-prime residual

The finite three-family quarter-tie bound is absorbed into every positive logarithmic budget,
uniformly in the excluded decimal digit.

Source: MAYNARD-PRD-PUBLISHED, Section 6, pp. 139--140, Eq. (6.5).
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- The sum of the absolute values of the three repeated corrections is
eventually below every positive logarithmic budget. -/
theorem exists_sectionSixFirstRepeatedErrors_budget_upper
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (budget : Real) (hbudget : 0 < budget) :
    ∃ length0 : Nat, 1 <= length0 ∧
      ∀ length : Nat, length0 <= length ->
        ∀ digit : Fin 10,
          let X : Real := ((10 ^ length : Nat) : Real)
          let z1 : Real := sectionSixZOne epsilon X
          let z2 : Real := sectionSixZTwo epsilon X
          let z3 : Real := sectionSixZThree epsilon X
          let z4 : Real := sectionSixZFour X
          abs (sectionSixFirstOuterRepeatedSum digit length z1 z4) +
              abs (sectionSixFirstSecondRepeatedSum digit length z1 z1 z2) +
              abs (sectionSixFirstSecondRepeatedSum digit length z1 z3 z4) <=
            budget *
              ((paddedRestrictedNumbers digit length).card : Real) /
                Real.log X := by
  let gap : Real := sectionSixThetaGap epsilon
  let K : Nat := 2 ^ Nat.ceil (1 / gap)
  have hgap : 0 < gap :=
    (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
  obtain ⟨chargeLength, hchargeLength, hchargeAt⟩ :=
    exists_sectionSixDirectQuarterTieChargeAbsorptionThreshold
      epsilon hepsilon hepsilonSmall (3 * K) budget hbudget gap hgap
  obtain ⟨endpointLength, hendpointAt⟩ :=
    exists_decimalEndpointThreshold (gap / 2) (by positivity)
  let length0 : Nat := max chargeLength endpointLength
  have hlength0 : 1 <= length0 :=
    hchargeLength.trans (by dsimp only [length0]; omega)
  refine ⟨length0, hlength0, ?_⟩
  intro length hlength digit
  dsimp only
  have hchargeLengthAt : chargeLength <= length :=
    (by dsimp only [length0]; omega : chargeLength <= length0).trans hlength
  have hendpointLengthAt : endpointLength <= length :=
    (by dsimp only [length0]; omega : endpointLength <= length0).trans hlength
  let X : Real := ((10 ^ length : Nat) : Real)
  have hendpoint := hendpointAt length hendpointLengthAt
  have hlengthOne : 1 <= length := hendpoint.1
  have hX : 1 < X := by
    dsimp only [X]
    exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < (10 : Nat))
  have hhalf : 5 <= X ^ (gap / 2) := by
    simpa only [X] using hendpoint.2.1
  have hfive : 5 < X ^ gap := by
    exact hhalf.trans_lt
      (Real.rpow_lt_rpow_of_exponent_lt hX (by linarith))
  have hfinite :=
    sectionSixFirstRepeatedErrors_abs_le_quarterTieCharge
      epsilon hepsilon hepsilonSmall digit hlengthOne
      (by simpa only [X, gap] using hfive)
  have hcharge := hchargeAt length hchargeLengthAt digit
  exact hfinite.trans
    (by simpa only [X, gap, K] using hcharge)

/-- The literal signed repeated residual of the corrected first ledger is
eventually below every positive logarithmic budget. -/
theorem exists_sectionSixFirstRepeatedResidual_budget_upper
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (budget : Real) (hbudget : 0 < budget) :
    ∃ length0 : Nat, 1 <= length0 ∧
      ∀ length : Nat, length0 <= length ->
        ∀ digit : Fin 10,
          let X : Real := ((10 ^ length : Nat) : Real)
          let z1 : Real := sectionSixZOne epsilon X
          let z2 : Real := sectionSixZTwo epsilon X
          let z3 : Real := sectionSixZThree epsilon X
          let z4 : Real := sectionSixZFour X
          abs (-sectionSixFirstOuterRepeatedSum digit length z1 z4 +
              sectionSixFirstSecondRepeatedSum digit length z1 z1 z2 +
              sectionSixFirstSecondRepeatedSum digit length z1 z3 z4) <=
            budget *
              ((paddedRestrictedNumbers digit length).card : Real) /
                Real.log X := by
  obtain ⟨length0, hlength0, habsAt⟩ :=
    exists_sectionSixFirstRepeatedErrors_budget_upper
      epsilon hepsilon hepsilonSmall budget hbudget
  refine ⟨length0, hlength0, ?_⟩
  intro length hlength digit
  let X : Real := ((10 ^ length : Nat) : Real)
  let z1 : Real := sectionSixZOne epsilon X
  let z2 : Real := sectionSixZTwo epsilon X
  let z3 : Real := sectionSixZThree epsilon X
  let z4 : Real := sectionSixZFour X
  let outer : Real := sectionSixFirstOuterRepeatedSum digit length z1 z4
  let low : Real :=
    sectionSixFirstSecondRepeatedSum digit length z1 z1 z2
  let high : Real :=
    sectionSixFirstSecondRepeatedSum digit length z1 z3 z4
  have habs :
      abs outer + abs low + abs high <=
        budget *
          ((paddedRestrictedNumbers digit length).card : Real) /
            Real.log X := by
    simpa only [X, z1, z2, z3, z4, outer, low, high] using
      habsAt length hlength digit
  dsimp only
  change abs (-outer + low + high) <=
    budget *
      ((paddedRestrictedNumbers digit length).card : Real) /
        Real.log X
  calc
    abs (-outer + low + high) <= abs (-outer + low) + abs high :=
      abs_add_le _ _
    _ <= (abs (-outer) + abs low) + abs high :=
      add_le_add (abs_add_le _ _) le_rfl
    _ = abs outer + abs low + abs high := by rw [abs_neg]
    _ <= _ := habs

end

end PrimesRestrictedDigits
