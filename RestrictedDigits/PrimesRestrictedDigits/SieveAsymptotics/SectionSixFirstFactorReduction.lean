import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectNearGeometryThreshold
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstFactorReductionScalars
import PrimesRestrictedDigits.SieveAsymptotics.TypeIILogLogWidthAbsorption
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIWeakSmallProductTail

/-!
# First factor-reduction residual

One fixed budget-dependent split combines the weak small-product tail, two fixed-region
Proposition 6.1 estimates, the ambient pointwise sieve bound, and a reciprocal-prime window.
The result controls both signed ledger errors.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 139--140, Eq. (6.4).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private theorem sectionSixFirstFactor_ambientBaseCountSum_le
    (epsilon K : Real) {length : Nat} (hlength : 1 <= length)
    (hpoint : ∀ p : Nat, p.Prime ->
      (p : Real) <= sectionSixZFour ((10 ^ length : Nat) : Real) ->
      ((strictSiftedCarrier
          (sieveDilation
            (maynardAmbientCarrier ((10 ^ length : Nat) : Real))
            p.toPNat')
          (sectionSixZOne epsilon
            ((10 ^ length : Nat) : Real))).card : Real) <=
        K * ((10 ^ length : Nat) : Real) /
          ((p : Real) * Real.log ((10 ^ length : Nat) : Real)))
    (tau : Real) :
    let X : Real := ((10 ^ length : Nat) : Real)
    let z1 : Real := sectionSixZOne epsilon X
    let z4 : Real := sectionSixZFour X
    let split : Real := X ^ (1 / 2 - tau)
    let B : Finset Nat := maynardAmbientCarrier X
    sectionSixFirstFactorBaseCountSum B length z1 split z4 <=
      (K * X / Real.log X) *
        ∑ p ∈ sievePrimeInterval split z4, (p : Real)⁻¹ := by
  let X : Real := ((10 ^ length : Nat) : Real)
  let z1 : Real := sectionSixZOne epsilon X
  let z4 : Real := sectionSixZFour X
  let split : Real := X ^ (1 / 2 - tau)
  let B : Finset Nat := maynardAmbientCarrier X
  have hX : 1 < X := by
    dsimp only [X]
    exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < (10 : Nat))
  have hlog : 0 < Real.log X := Real.log_pos hX
  unfold sectionSixFirstFactorBaseCountSum
  calc
    (∑ p ∈ sievePrimeInterval split z4,
      ((strictSiftedCarrier (sieveDilation B p.toPNat') z1).card : Real)) <=
        ∑ p ∈ sievePrimeInterval split z4,
          K * X / ((p : Real) * Real.log X) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpData := mem_sievePrimeInterval.mp hp
      simpa only [X, z1, z4, B] using hpoint p hpData.1 hpData.2.2
    _ = (K * X / Real.log X) *
        ∑ p ∈ sievePrimeInterval split z4, (p : Real)⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      have hpPrime := (mem_sievePrimeInterval.mp hp).1
      have hpNe : (p : Real) ≠ 0 := by exact_mod_cast hpPrime.ne_zero
      field_simp [hpNe, hlog.ne']

/-- Both factor-reduction errors in the corrected Eq. (6.5) ledger are
eventually below every positive logarithmic budget, uniformly in the digit. -/
theorem exists_sectionSixFirstFactorErrors_budget_upper
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hepsilonRosser :
      2 * (Real.exp 5000 + 2) * epsilon ^ (3 : Nat) <= 1)
    (budget : Real) (hbudget : 0 < budget) :
    ∃ length0 : Nat, 1 <= length0 ∧
      ∀ length : Nat, length0 <= length ->
        ∀ digit : Fin 10,
          abs (sectionSixFirstFactorError digit length
              (sectionSixZOne epsilon ((10 ^ length : Nat) : Real))
              (sectionSixZTwo epsilon ((10 ^ length : Nat) : Real))) +
            abs (sectionSixFirstFactorError digit length
              (sectionSixZThree epsilon ((10 ^ length : Nat) : Real))
              (sectionSixZFour ((10 ^ length : Nat) : Real))) <=
            budget *
              ((paddedRestrictedNumbers digit length).card : Real) /
                Real.log ((10 ^ length : Nat) : Real) := by
  obtain ⟨K, hK, ambientLength, hambientLength, hambient⟩ :=
    exists_sectionSixFirstAmbientZOne_upper epsilon hepsilon hepsilonSmall
      hepsilonRosser
  let tau : Real := min (1 / 128) (budget / (80 * (K + 1)))
  have hKone : 0 < K + 1 := by linarith
  have htau : 0 < tau := by
    dsimp only [tau]
    exact lt_min (by norm_num) (div_pos hbudget (mul_pos (by norm_num) hKone))
  have htauSmall : tau <= 1 / 64 := by
    calc
      tau <= 1 / 128 := min_le_left _ _
      _ <= 1 / 64 := by norm_num
  have htauBudget : 80 * (K + 1) * tau <= budget := by
    have hle : tau <= budget / (80 * (K + 1)) := min_le_right _ _
    have hden : 0 < 80 * (K + 1) := mul_pos (by norm_num) hKone
    have hmul := (le_div_iff₀ hden).mp hle
    nlinarith
  let piece : Real := budget / 3
  have hpiece : 0 < piece := by
    dsimp only [piece]
    positivity
  obtain ⟨Ctail, hCtail, tailLength, htailLength, htail⟩ :=
    exists_typeIIWeakSmallProductTail_upper
  obtain ⟨widthLength, hwidthLength, hwidth⟩ :=
    exists_mul_majorArcM2LogLogDelta_powTen_le Ctail piece hCtail.le hpiece
  obtain ⟨geometryLength, hgeometryLength, hgeometry⟩ :=
    exists_sectionSixDirectNearGeometryThreshold (2 * tau) tau
      (by positivity) htau 0
  obtain ⟨baseLength, hbaseLength, hbase⟩ :=
    exists_sectionSixFirstNearBase_budget_upper epsilon hepsilon
      hepsilonSmall hepsilonRosser tau htau htauSmall piece hpiece
  obtain ⟨reciprocalLength, hreciprocalLength, hreciprocal⟩ :=
    exists_sectionSixFirstNearPrimeReciprocal_upper tau htau htauSmall
  let length0 : Nat := max 2
    (max ambientLength (max tailLength (max widthLength
      (max geometryLength (max baseLength reciprocalLength)))))
  have hlength0 : 1 <= length0 := by
    dsimp only [length0]
    omega
  refine ⟨length0, hlength0, ?_⟩
  intro length hlength digit
  have hlengthTwo : 2 <= length := by
    dsimp only [length0] at hlength
    omega
  have hAmbientAt : ambientLength <= length := by
    dsimp only [length0] at hlength
    omega
  have hTailAt : tailLength <= length := by
    dsimp only [length0] at hlength
    omega
  have hWidthAt : widthLength <= length := by
    dsimp only [length0] at hlength
    omega
  have hGeometryAt : geometryLength <= length := by
    dsimp only [length0] at hlength
    omega
  have hBaseAt : baseLength <= length := by
    dsimp only [length0] at hlength
    omega
  have hReciprocalAt : reciprocalLength <= length := by
    dsimp only [length0] at hlength
    omega
  have hlengthOne : 1 <= length := by omega
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let z1 : Real := sectionSixZOne epsilon X
  let z2 : Real := sectionSixZTwo epsilon X
  let z3 : Real := sectionSixZThree epsilon X
  let z4 : Real := sectionSixZFour X
  let split : Real := X ^ (1 / 2 - tau)
  let deltaX : Real := majorArcM2LogLogDelta XNat
  let nearX : Finset Nat := typeIINearXCarrier XNat deltaX
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let rho : Real := restrictedDigitDensity digit
  let lambda : Real := rho * ((A.card : Real) / X)
  let mass : Real := (A.card : Real) / Real.log X
  have hX : 1 < X := by
    dsimp only [X, XNat]
    exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < (10 : Nat))
  have hXPos : 0 < X := zero_lt_one.trans hX
  have hlog : 0 < Real.log X := Real.log_pos hX
  have hmass : 0 <= mass := by
    dsimp only [mass]
    positivity
  have hlambda : 0 <= lambda := by
    dsimp only [lambda, rho]
    exact mul_nonneg (restrictedDigitDensity_nonneg digit)
      (div_nonneg (by positivity) hXPos.le)
  have hgeometryAt := hgeometry length hGeometryAt
  have hdeltaWidth : deltaX ^ 2 <= 2 * tau := by
    simpa only [deltaX, XNat] using hgeometryAt.1.le
  have hfinite :=
    sectionSixFirstFactorErrors_abs_le_farTail_add_nearBase hepsilon
      hepsilonSmall digit hlengthTwo
        (by simpa only [deltaX, XNat] using hdeltaWidth)
  have htailAt := htail length hTailAt digit
  have htailAt' : ((A \ nearX).card : Real) +
      lambda * ((B \ nearX).card : Real) <=
        Ctail * deltaX * (A.card : Real) / Real.log X := by
    simpa only [A, B, nearX, lambda, rho, X, XNat, deltaX,
      mul_div_assoc] using htailAt
  have hwidthAt : Ctail * deltaX <= piece := by
    simpa only [deltaX, XNat] using hwidth length hWidthAt
  have hfar : ((A \ nearX).card : Real) +
      lambda * ((B \ nearX).card : Real) <= piece * mass := by
    calc
      _ <= Ctail * deltaX * (A.card : Real) / Real.log X := htailAt'
      _ = (Ctail * deltaX) * mass := by
        dsimp only [mass]
        ring
      _ <= piece * mass :=
        mul_le_mul_of_nonneg_right hwidthAt hmass
  have hbaseAt := hbase length hBaseAt digit
  have hbaseBound :
      abs (sectionSixFirstOuterBaseSum digit length z1 split z4) <=
        piece * mass := by
    simpa only [X, z1, z4, split, mass, mul_div_assoc] using hbaseAt
  have hpoint := hambient length hAmbientAt
  have hbaseAmbient := sectionSixFirstFactor_ambientBaseCountSum_le
    epsilon K hlengthOne hpoint tau
  have hbaseAmbient' : sectionSixFirstFactorBaseCountSum B length
      z1 split z4 <= (K * X / Real.log X) * (6 * tau) := by
    calc
      _ <= (K * X / Real.log X) *
          ∑ p ∈ sievePrimeInterval split z4, (p : Real)⁻¹ := by
        simpa only [X, z1, z4, split, B] using hbaseAmbient
      _ <= (K * X / Real.log X) * (6 * tau) := by
        apply mul_le_mul_of_nonneg_left
        · simpa only [X, split, z4] using
            hreciprocal length hReciprocalAt
        · positivity
  have hrhoUpper : rho <= 10 / 9 := by
    simpa only [rho] using restrictedDigitDensity_le_ten_ninths digit
  have hscalar : (40 / 3 : Real) * K * tau <= budget / 6 := by
    nlinarith [mul_pos hK htau]
  have hambientBound :
      2 * lambda * sectionSixFirstFactorBaseCountSum B length z1 split z4 <=
        (budget / 6) * mass := by
    have hmul := mul_le_mul_of_nonneg_left hbaseAmbient'
      (mul_nonneg (by norm_num : (0 : Real) <= 2) hlambda)
    calc
      2 * lambda * sectionSixFirstFactorBaseCountSum B length z1 split z4 <=
          2 * lambda * ((K * X / Real.log X) * (6 * tau)) := hmul
      _ = 12 * rho * K * tau * mass := by
        dsimp only [lambda, mass]
        field_simp [hXPos.ne', hlog.ne']
        ring
      _ <= 12 * (10 / 9 : Real) * K * tau * mass := by
        gcongr
      _ = ((40 / 3 : Real) * K * tau) * mass := by ring
      _ <= (budget / 6) * mass :=
        mul_le_mul_of_nonneg_right hscalar hmass
  change abs (sectionSixFirstFactorError digit length z1 z2) +
      abs (sectionSixFirstFactorError digit length z3 z4) <=
    budget * (A.card : Real) / Real.log X
  calc
    _ <= (((A \ nearX).card : Real) +
          lambda * ((B \ nearX).card : Real)) +
        abs (sectionSixFirstOuterBaseSum digit length z1 split z4) +
        2 * lambda *
          sectionSixFirstFactorBaseCountSum B length z1 split z4 := by
      simpa only [XNat, X, z1, z2, z3, z4, split, nearX, A, B,
        lambda, rho, deltaX] using hfinite
    _ <= piece * mass + piece * mass + (budget / 6) * mass := by
      gcongr
    _ <= budget * mass := by
      dsimp only [piece]
      nlinarith
    _ = budget * (A.card : Real) / Real.log X := by
      dsimp only [mass]
      ring

end

end PrimesRestrictedDigits
