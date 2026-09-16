import PrimesRestrictedDigits.PrimeNumberTheorem.ReciprocalPrimeMertens
import PrimesRestrictedDigits.SieveAsymptotics.FundamentalLargeDeltaAmbient
import PrimesRestrictedDigits.SieveAsymptotics.FundamentalLargeDeltaMonotonicity
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstFactorReductionFiniteBound
import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstPropositionResidualCarriers

/-!
# First factor-reduction scalar estimates

This file supplies the fixed-region Proposition 6.1 estimate, a reciprocal prime bound on the
enlarged near window, and the ambient pointwise bound at the `z1` threshold.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, pp. 139--140, Eq. (6.4).
-/

open Filter
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The ambient large-delta cutoff lies below the first Section 6 cutoff. -/
theorem epsilon_pow_four_le_sectionSixThetaGap
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) :
    epsilon ^ (4 : Nat) <= sectionSixThetaGap epsilon := by
  have hpow : epsilon ^ (4 : Nat) <= (1 / 64 : Real) ^ (4 : Nat) :=
    pow_le_pow_left₀ hepsilon.le hepsilonSmall 4
  rw [sectionSixThetaGap_eq]
  norm_num at hpow ⊢
  linarith

private theorem sectionSixFirstFactor_tau_parameter_bounds
    {epsilon tau : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (_htau : 0 < tau) (htauSmall : tau <= 1 / 64) :
    sectionSixThetaGap epsilon <= 1 / 2 - tau ∧
      sectionSixThetaTwo epsilon < 1 / 2 - tau ∧
      (1 / 2 : Real) <= 1 - sectionSixThetaOne epsilon := by
  rw [sectionSixThetaGap_eq]
  simp only [sectionSixThetaOne, sectionSixThetaTwo]
  constructor
  · linarith
  constructor <;> linarith

/-- The fixed near base interval is the difference of two cumulative weak
one-coordinate Proposition 6.1 regions. -/
theorem sectionSixFirstNearBase_eq_propositionSixOneUpper_sub
    {epsilon tau : Real} (hepsilon : 0 < epsilon)
    (htau : 0 <= tau)
    (hlower : sectionSixThetaGap epsilon <= 1 / 2 - tau)
    (hupper : (1 / 2 : Real) <= 1 - sectionSixThetaOne epsilon)
    (digit : Fin 10) {length : Nat} (hlength : 1 <= length) :
    let X : Real := ((10 ^ length : Nat) : Real)
    let z1 : Real := sectionSixZOne epsilon X
    let z4 : Real := sectionSixZFour X
    sectionSixFirstOuterBaseSum digit length z1
        (X ^ (1 / 2 - tau)) z4 =
      propositionSixOneSum epsilon 1
          (sectionSixOneCoordinateUpperRegion (1 / 2)) digit length -
        propositionSixOneSum epsilon 1
          (sectionSixOneCoordinateUpperRegion (1 / 2 - tau)) digit length := by
  have hgeneric := sectionSixFirstOuterBaseSum_eq_propositionSixOneSum_ioc
    epsilon (1 / 2 - tau) (1 / 2 : Real) hepsilon hlower hupper digit hlength
  have hsub :
      sectionSixOneCoordinateUpperRegion (1 / 2 - tau) ⊆
        sectionSixOneCoordinateUpperRegion (1 / 2 : Real) := by
    intro x hx
    change x 0 <= 1 / 2 - tau at hx
    change x 0 <= (1 / 2 : Real)
    linarith
  rw [sectionSixOneCoordinateIocRegion_eq_sdiff,
    propositionSixOneSum_sdiff epsilon 1 hsub digit length] at hgeneric
  simpa only [sectionSixZOne, sectionSixZFour_eq_rpow] using hgeneric

/-- Two fixed-region Proposition 6.1 calls absorb the signed near base
discrepancy uniformly in the excluded digit. -/
theorem exists_sectionSixFirstNearBase_budget_upper
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hepsilonRosser :
      2 * (Real.exp 5000 + 2) * epsilon ^ (3 : Nat) <= 1)
    (tau : Real) (htau : 0 < tau) (htauSmall : tau <= 1 / 64)
    (budget : Real) (hbudget : 0 < budget) :
    ∃ length0 : Nat, 1 <= length0 ∧
      ∀ length : Nat, length0 <= length ->
        ∀ digit : Fin 10,
          let X : Real := ((10 ^ length : Nat) : Real)
          let z1 : Real := sectionSixZOne epsilon X
          let z4 : Real := sectionSixZFour X
          abs (sectionSixFirstOuterBaseSum digit length z1
              (X ^ (1 / 2 - tau)) z4) <=
            budget * ((paddedRestrictedNumbers digit length).card : Real) /
              Real.log X := by
  have hparams := sectionSixFirstFactor_tau_parameter_bounds hepsilon
    hepsilonSmall htau htauSmall
  let piece : Real := budget / 2
  have hpiece : 0 < piece := by
    dsimp only [piece]
    positivity
  obtain ⟨halfLength, hhalfLength, hhalf⟩ :=
    propositionSixOne epsilon hepsilon hepsilonSmall hepsilonRosser
      (sectionSixOneCoordinateUpperPresentation (1 / 2)) piece hpiece
  obtain ⟨lowerLength, hlowerLength, hlower⟩ :=
    propositionSixOne epsilon hepsilon hepsilonSmall hepsilonRosser
      (sectionSixOneCoordinateUpperPresentation (1 / 2 - tau)) piece hpiece
  let length0 := max halfLength lowerLength
  have hlength0 : 1 <= length0 :=
    hhalfLength.trans (Nat.le_max_left _ _)
  refine ⟨length0, hlength0, ?_⟩
  intro length hlength digit
  have hhalfAt : halfLength <= length :=
    (Nat.le_max_left _ _).trans hlength
  have hlowerAt : lowerLength <= length :=
    (Nat.le_max_right _ _).trans hlength
  have hlengthOne : 1 <= length := hlength0.trans hlength
  let X : Real := ((10 ^ length : Nat) : Real)
  let z1 : Real := sectionSixZOne epsilon X
  let z4 : Real := sectionSixZFour X
  let mass : Real := ((paddedRestrictedNumbers digit length).card : Real) /
    Real.log X
  let Phalf : Real := propositionSixOneSum epsilon 1
    (sectionSixOneCoordinateUpperRegion (1 / 2)) digit length
  let Plower : Real := propositionSixOneSum epsilon 1
    (sectionSixOneCoordinateUpperRegion (1 / 2 - tau)) digit length
  have hhalfBound : abs Phalf <= piece * mass := by
    simpa only [Phalf, piece, mass, X, mul_div_assoc] using
      hhalf length hhalfAt digit
  have hlowerBound : abs Plower <= piece * mass := by
    simpa only [Plower, piece, mass, X, mul_div_assoc] using
      hlower length hlowerAt digit
  have hbridge := sectionSixFirstNearBase_eq_propositionSixOneUpper_sub
    hepsilon htau.le hparams.1 hparams.2.2 digit hlengthOne
  have hbridge' :
      sectionSixFirstOuterBaseSum digit length z1
          (X ^ (1 / 2 - tau)) z4 = Phalf - Plower := by
    simpa only [X, z1, z4, Phalf, Plower] using hbridge
  change abs (sectionSixFirstOuterBaseSum digit length z1
      (X ^ (1 / 2 - tau)) z4) <=
    budget * ((paddedRestrictedNumbers digit length).card : Real) /
      Real.log X
  rw [hbridge']
  calc
    abs (Phalf - Plower) <= abs Phalf + abs Plower := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le Phalf (-Plower)
    _ <= piece * mass + piece * mass := add_le_add hhalfBound hlowerBound
    _ = budget * ((paddedRestrictedNumbers digit length).card : Real) /
        Real.log X := by
      dsimp only [piece, mass]
      ring

private theorem sectionSixFirst_log_tau_ratio_le
    {tau : Real} (htau : 0 < tau) (htauSmall : tau <= 1 / 64) :
    Real.log ((1 / 2 + tau) / (1 / 2 - tau)) <= 5 * tau := by
  have hden : 0 < (1 / 2 - tau : Real) := by linarith
  have hnum : 0 < (1 / 2 + tau : Real) := by linarith
  have hratio : 0 < (1 / 2 + tau) / (1 / 2 - tau) :=
    div_pos hnum hden
  have hlog := Real.log_le_sub_one_of_pos hratio
  have hratioBound :
      (1 / 2 + tau) / (1 / 2 - tau) - 1 <= 5 * tau := by
    rw [sub_le_iff_le_add]
    apply (div_le_iff₀ hden).2
    nlinarith
  exact hlog.trans hratioBound

/-- The reciprocal-prime mass in the fixed near interval is eventually at
most `6*tau`. The proof enlarges past `sqrt X`, retaining its equality fiber. -/
theorem exists_sectionSixFirstNearPrimeReciprocal_upper
    (tau : Real) (htau : 0 < tau) (htauSmall : tau <= 1 / 64) :
    ∃ length0 : Nat, 1 <= length0 ∧
      ∀ length : Nat, length0 <= length ->
        let X : Real := ((10 ^ length : Nat) : Real)
        (∑ p ∈ sievePrimeInterval (X ^ (1 / 2 - tau))
            (sectionSixZFour X), (p : Real)⁻¹) <= 6 * tau := by
  obtain ⟨D, hD, hMertens⟩ := exists_sum_prime_inv_halfOpen_le_log_ratio
  let Xfun : Nat -> Real := fun length => ((10 ^ length : Nat) : Real)
  have hXtop : Tendsto Xfun atTop atTop := by
    simpa only [Xfun, Nat.cast_pow, Nat.cast_ofNat] using
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : Real) < 10))
  have hlogtop :
      Tendsto (fun length : Nat => Real.log (Xfun length)) atTop atTop :=
    Real.tendsto_log_atTop.comp hXtop
  have hcoef : 0 < (1 / 2 - tau : Real) := by linarith
  have hscaled : Tendsto
      (fun length : Nat => (1 / 2 - tau) * Real.log (Xfun length))
      atTop atTop := hlogtop.const_mul_atTop hcoef
  have hguards : ∀ᶠ length : Nat in atTop,
      1 <= length ∧
      2 <= Xfun length ^ (1 / 2 - tau) ∧
      D / ((1 / 2 - tau) * Real.log (Xfun length)) <= tau := by
    filter_upwards [eventually_ge_atTop (1 : Nat),
      ((tendsto_rpow_atTop hcoef).comp hXtop).eventually_ge_atTop (2 : Real),
      hscaled.eventually_ge_atTop (D / tau)] with length hlength hw hrem
    refine ⟨hlength, hw, ?_⟩
    have hdenPos : 0 < (1 / 2 - tau) * Real.log (Xfun length) := by
      have : 0 < D / tau := div_pos hD htau
      exact this.trans_le hrem
    apply (div_le_iff₀ hdenPos).2
    calc
      D = tau * (D / tau) := by field_simp
      _ <= tau * ((1 / 2 - tau) * Real.log (Xfun length)) :=
        mul_le_mul_of_nonneg_left hrem htau.le
  obtain ⟨lengthGuard, hlengthGuard⟩ := eventually_atTop.mp hguards
  let length0 := max 1 lengthGuard
  refine ⟨length0, Nat.le_max_left _ _, ?_⟩
  intro length hlength
  have hlengthGuardAt : lengthGuard <= length :=
    (Nat.le_max_right 1 lengthGuard).trans hlength
  have hguard := hlengthGuard length hlengthGuardAt
  let X : Real := ((10 ^ length : Nat) : Real)
  let w : Real := X ^ (1 / 2 - tau)
  let z : Real := X ^ (1 / 2 + tau)
  have hX : 1 < X := by
    dsimp only [X]
    exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < (10 : Nat))
  have hXPos : 0 < X := zero_lt_one.trans hX
  have hwTwo : 2 <= w := by
    simpa only [w, X, Xfun] using hguard.2.1
  have hwz : w <= z := by
    dsimp only [w, z]
    apply Real.rpow_le_rpow_of_exponent_le hX.le
    linarith
  have hsubset : sievePrimeInterval w (sectionSixZFour X) ⊆
      (naturalLeftClosedRightOpenInterval w z).filter Nat.Prime := by
    intro p hp
    have hpData := mem_sievePrimeInterval.mp hp
    rw [Finset.mem_filter, mem_naturalLeftClosedRightOpenInterval]
    refine ⟨⟨hpData.2.1.le, ?_⟩, hpData.1⟩
    calc
      (p : Real) <= sectionSixZFour X := hpData.2.2
      _ = X ^ (1 / 2 : Real) := sectionSixZFour_eq_rpow X
      _ < X ^ (1 / 2 + tau) :=
        Real.rpow_lt_rpow_of_exponent_lt hX (by linarith)
  have hsumSub :
      (∑ p ∈ sievePrimeInterval w (sectionSixZFour X), (p : Real)⁻¹) <=
        ∑ p ∈ (naturalLeftClosedRightOpenInterval w z).filter Nat.Prime,
          (p : Real)⁻¹ := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun p hp hnot => inv_nonneg.mpr (Nat.cast_nonneg p))
  have hM := hMertens w z hwTwo hwz
  have hratio :
      Real.log (Real.log z / Real.log w) =
        Real.log ((1 / 2 + tau) / (1 / 2 - tau)) := by
    have hlogX : 0 < Real.log X := Real.log_pos hX
    dsimp only [w, z]
    rw [Real.log_rpow hXPos, Real.log_rpow hXPos]
    congr 1
    field_simp
  have hrem : D / Real.log w <= tau := by
    have := hguard.2.2
    dsimp only [w]
    rw [Real.log_rpow hXPos]
    simpa only [X, Xfun] using this
  change (∑ p ∈ sievePrimeInterval w (sectionSixZFour X),
      (p : Real)⁻¹) <= 6 * tau
  calc
    _ <= ∑ p ∈ (naturalLeftClosedRightOpenInterval w z).filter Nat.Prime,
        (p : Real)⁻¹ := hsumSub
    _ <= Real.log (Real.log z / Real.log w) + D / Real.log w := hM
    _ <= 5 * tau + tau := by
      rw [hratio]
      exact add_le_add (sectionSixFirst_log_tau_ratio_le htau htauSmall) hrem
    _ = 6 * tau := by ring

/-- The ambient once-dilated count at `z1` has the required uniform
`X/(p log X)` bound throughout the weak interval `p<=sqrt X`. -/
theorem exists_sectionSixFirstAmbientZOne_upper
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hepsilonRosser :
      2 * (Real.exp 5000 + 2) * epsilon ^ (3 : Nat) <= 1) :
    ∃ K : Real, 0 < K ∧
      ∃ length0 : Nat, 1 <= length0 ∧
        ∀ length : Nat, length0 <= length ->
          ∀ p : Nat, p.Prime ->
            (p : Real) <= sectionSixZFour ((10 ^ length : Nat) : Real) ->
            ((strictSiftedCarrier
                (sieveDilation
                  (maynardAmbientCarrier ((10 ^ length : Nat) : Real))
                  p.toPNat')
                (sectionSixZOne epsilon
                  ((10 ^ length : Nat) : Real))).card : Real) <=
              K * ((10 ^ length : Nat) : Real) /
                ((p : Real) * Real.log ((10 ^ length : Nat) : Real)) := by
  obtain ⟨K, hK, length0, hlength0, hbound⟩ :=
    exists_largeDeltaAmbientSiftedCount_upper epsilon hepsilon
      hepsilonSmall hepsilonRosser
  refine ⟨K, hK, length0, hlength0, ?_⟩
  intro length hlength p hp hpUpper
  let X : Real := ((10 ^ length : Nat) : Real)
  have hX : 1 < X := by
    dsimp only [X]
    exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < (10 : Nat))
  have hhalfLevel : (1 / 2 : Real) < 50 / 77 - epsilon := by linarith
  have hpLevel : (p : Real) < X ^ (50 / 77 - epsilon) := by
    calc
      (p : Real) <= sectionSixZFour X := by simpa only [X] using hpUpper
      _ = X ^ (1 / 2 : Real) := sectionSixZFour_eq_rpow X
      _ < X ^ (50 / 77 - epsilon) :=
        Real.rpow_lt_rpow_of_exponent_lt hX hhalfLevel
  have hraw := hbound length hlength p hp.one_le
    (by simpa only [X] using hpLevel)
  have hthreshold : X ^ (epsilon ^ (4 : Nat)) <=
      sectionSixZOne epsilon X := by
    exact Real.rpow_le_rpow_of_exponent_le hX.le
      (epsilon_pow_four_le_sectionSixThetaGap hepsilon hepsilonSmall)
  calc
    ((strictSiftedCarrier
        (sieveDilation (maynardAmbientCarrier X) p.toPNat')
        (sectionSixZOne epsilon X)).card : Real) <=
      ((strictSiftedCarrier
        (sieveDilation (maynardAmbientCarrier X) p.toPNat')
        (X ^ (epsilon ^ (4 : Nat)))).card : Real) :=
      card_strictSiftedCarrier_threshold_le_real _ hthreshold
    _ <= K * X / ((p : Real) * Real.log X) := by
      simpa only [X] using hraw

end

end PrimesRestrictedDigits
