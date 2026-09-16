import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectRangeRecurrence
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalFundamentalAbsorption
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalFundamentalContribution
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIPrimeTupleMultiplicity
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIRegionSupport
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Joint Fundamental reindex for the two direct base ranges

The two closed direct ranges have singleton complete-product fibres. This gives their joint
base contribution with coefficient one in the exact Fundamental residual.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private theorem sectionSixDirectRangePrimeTuple_mem_fundamentalCarrier
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell → Real)}
    (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    {band : SectionSixDirectBand} {p : Fin ell → Nat}
    (hp : p ∈ sectionSixDirectRangePrimeTuples
      epsilon ell region length band) :
    primeTupleProduct p ∈ maynardStrictRoughCarrier
      (((10 ^ length : Nat) : Real) ^ (50 / 77 - epsilon))
      (((10 ^ length : Nat) : Real) ^ delta) := by
  let X : Real := ((10 ^ length : Nat) : Real)
  have hX : 1 < X := by
    dsimp [X]
    exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < (10 : Nat))
  have hpBand := (mem_sectionSixDirectRangePrimeTuples.mp hp).2
  have hpData := (mem_sectionSixDirectRangePrimeTuples.mp hp).1
  have hpSource : IsPropositionSixOnePrimeTuple epsilon length region p :=
    (mem_propositionSixOnePrimeTuples_iff_source hepsilon hlength).mp hpData
  have hprime : ∀ i, (p i).Prime := hpSource.1
  have hrough : strictRoughPredicate (X ^ delta) (primeTupleProduct p) := by
    apply strictRoughPredicate_primeTupleProduct hprime
    intro i
    have hgap : X ^ delta < X ^ sectionSixThetaGap epsilon :=
      Real.rpow_lt_rpow_of_exponent_lt hX hdeltaGapStrict
    exact hgap.trans_le (by simpa [X] using hpSource.2.2.1 i)
  have hpositive : 0 < primeTupleProduct p :=
    primeTupleProduct_pos_of_mem_propositionSixOnePrimeTuples hpData
  have hcutoff : (primeTupleProduct p : Real) <
      X ^ (50 / 77 - epsilon) := by
    cases band with
    | first =>
        have hupper : (primeTupleProduct p : Real) ≤
            X ^ sectionSixThetaTwo epsilon := by
          simpa [X, sectionSixDirectRangeMembership] using hpBand.2
        apply hupper.trans_lt
        apply Real.rpow_lt_rpow_of_exponent_lt hX
        have horder := sectionSix_outerRange_exponent_order
          hepsilon hepsilonSmall
        linarith [horder.2.1, horder.2.2.1, horder.2.2.2.1]
    | second =>
        have hupper : (primeTupleProduct p : Real) ≤
            X ^ (1 - sectionSixThetaOne epsilon) := by
          simpa [X, sectionSixDirectRangeMembership] using hpBand.2
        apply hupper.trans_lt
        apply Real.rpow_lt_rpow_of_exponent_lt hX
        exact (sectionSix_outerRange_exponent_order
          hepsilon hepsilonSmall).2.2.2.1
  rw [mem_maynardStrictRoughCarrier]
  refine ⟨?_, hcutoff, hrough⟩
  exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hpositive)

private theorem sectionSixDirectRangePrimeTupleUnion_product_injOn
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon ≤ 1 / 64)
    {ell length : Nat} (hlength : 1 ≤ length)
    (region : Set (Fin ell → Real)) :
    Set.InjOn primeTupleProduct
      ((sectionSixDirectRangePrimeTuples
          epsilon ell region length .first ∪
        sectionSixDirectRangePrimeTuples
          epsilon ell region length .second :
        Finset (Fin ell → Nat)) : Set (Fin ell → Nat)) := by
  intro p hp q hq hproduct
  have hpBand : p ∈ sectionSixDirectRangePrimeTuples
        epsilon ell region length .first ∨
      p ∈ sectionSixDirectRangePrimeTuples
        epsilon ell region length .second := by
    exact Finset.mem_union.mp hp
  have hqBand : q ∈ sectionSixDirectRangePrimeTuples
        epsilon ell region length .first ∨
      q ∈ sectionSixDirectRangePrimeTuples
        epsilon ell region length .second := by
    exact Finset.mem_union.mp hq
  have hpData : p ∈ propositionSixOnePrimeTuples epsilon ell region length := by
    rcases hpBand with hpFirst | hpSecond
    · exact (mem_sectionSixDirectRangePrimeTuples.mp hpFirst).1
    · exact (mem_sectionSixDirectRangePrimeTuples.mp hpSecond).1
  have hqData : q ∈ propositionSixOnePrimeTuples epsilon ell region length := by
    rcases hqBand with hqFirst | hqSecond
    · exact (mem_sectionSixDirectRangePrimeTuples.mp hqFirst).1
    · exact (mem_sectionSixDirectRangePrimeTuples.mp hqSecond).1
  have hpSource : IsPropositionSixOnePrimeTuple epsilon length region p :=
    (mem_propositionSixOnePrimeTuples_iff_source hepsilon hlength).mp hpData
  have hqSource : IsPropositionSixOnePrimeTuple epsilon length region q :=
    (mem_propositionSixOnePrimeTuples_iff_source hepsilon hlength).mp hqData
  have hpEqReal : (primeTupleProduct p : Real) =
      (primeTupleProduct q : Real) := by exact_mod_cast hproduct
  rcases hpBand with hpFirst | hpSecond <;>
    rcases hqBand with hqFirst | hqSecond
  · exact eq_of_monotone_primeTupleProduct_eq hpSource.1 hqSource.1
      hpSource.2.1 hqSource.2.1 hproduct
  · have hpUpper : (primeTupleProduct p : Real) ≤
        (((10 ^ length : Nat) : Real) ^ sectionSixThetaTwo epsilon) := by
      simpa [sectionSixDirectRangeMembership] using
        (mem_sectionSixDirectRangePrimeTuples.mp hpFirst).2.2
    have hqLower : (((10 ^ length : Nat) : Real) ^
        (1 - sectionSixThetaTwo epsilon)) ≤
        (primeTupleProduct q : Real) := by
      simpa [sectionSixDirectRangeMembership] using
        (mem_sectionSixDirectRangePrimeTuples.mp hqSecond).2.1
    have horder := sectionSix_outerRange_exponent_order
      hepsilon hepsilonSmall
    have hwall : (((10 ^ length : Nat) : Real) ^ sectionSixThetaTwo epsilon) <
        (((10 ^ length : Nat) : Real) ^ (1 - sectionSixThetaTwo epsilon)) := by
      have hX : (1 : Real) < ((10 ^ length : Nat) : Real) := by
        exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
          (by norm_num : 1 < (10 : Nat))
      exact Real.rpow_lt_rpow_of_exponent_lt hX horder.2.1
    exfalso
    linarith
  · have hpLower : (((10 ^ length : Nat) : Real) ^
        (1 - sectionSixThetaTwo epsilon)) ≤
        (primeTupleProduct p : Real) := by
      simpa [sectionSixDirectRangeMembership] using
        (mem_sectionSixDirectRangePrimeTuples.mp hpSecond).2.1
    have hqUpper : (primeTupleProduct q : Real) ≤
        (((10 ^ length : Nat) : Real) ^ sectionSixThetaTwo epsilon) := by
      simpa [sectionSixDirectRangeMembership] using
        (mem_sectionSixDirectRangePrimeTuples.mp hqFirst).2.2
    have horder := sectionSix_outerRange_exponent_order
      hepsilon hepsilonSmall
    have hwall : (((10 ^ length : Nat) : Real) ^ sectionSixThetaTwo epsilon) <
        (((10 ^ length : Nat) : Real) ^ (1 - sectionSixThetaTwo epsilon)) := by
      have hX : (1 : Real) < ((10 ^ length : Nat) : Real) := by
        exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
          (by norm_num : 1 < (10 : Nat))
      exact Real.rpow_lt_rpow_of_exponent_lt hX horder.2.1
    exfalso
    linarith
  · exact eq_of_monotone_primeTupleProduct_eq hpSource.1 hqSource.1
      hpSource.2.1 hqSource.2.1 hproduct

theorem abs_sectionSixDirectRangeBaseContributions_le_fundamentalResidual
    (digit : Fin 10) {epsilon delta : Real} {ell length : Nat}
    (region : Set (Fin ell → Real))
    (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon ≤ 1 / 64)
    (hlength : 1 ≤ length)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon) :
    abs (sectionSixDirectRangeBaseContribution digit epsilon delta ell length
      region .first +
      sectionSixDirectRangeBaseContribution digit epsilon delta ell length
        region .second) ≤
      sectionSixFundamentalResidual digit epsilon delta length := by
  classical
  let first := sectionSixDirectRangePrimeTuples
    epsilon ell region length .first
  let second := sectionSixDirectRangePrimeTuples
    epsilon ell region length .second
  let states : Finset (Fin ell → Nat) := first ∪ second
  let X : Real := ((10 ^ length : Nat) : Real)
  let carrier := maynardStrictRoughCarrier
    (X ^ (50 / 77 - epsilon)) (X ^ delta)
  let value : (Fin ell → Nat) → Real := fun p =>
    sectionSixSiftedSum digit length (primeTupleProduct p).toPNat'
      (X ^ delta)
  let charge : Nat → Real := fun D =>
    abs (((strictSiftedCarrier
        (sieveDilation (paddedRestrictedNumbers digit length) D.toPNat')
        (X ^ delta)).card : Real) -
      (restrictedDigitDensity digit : Real) *
        ((paddedRestrictedNumbers digit length).card : Real) / X *
      ((strictSiftedCarrier
        (sieveDilation (maynardAmbientCarrier X) D.toPNat')
        (X ^ delta)).card : Real))
  have hdisjoint : Disjoint first second := by
    dsimp [first, second]
    exact (sectionSixOuterRanges_pairwiseDisjoint
      hepsilon hepsilonSmall hlength region).2.2.2.2.1
  have hmap : ∀ p, p ∈ states → primeTupleProduct p ∈ carrier := by
    intro p hp
    dsimp [states, carrier, first, second] at hp ⊢
    rcases Finset.mem_union.mp hp with hp | hp
    · exact sectionSixDirectRangePrimeTuple_mem_fundamentalCarrier
        hepsilon hepsilonSmall hlength hdeltaGapStrict hp
    · exact sectionSixDirectRangePrimeTuple_mem_fundamentalCarrier
        hepsilon hepsilonSmall hlength hdeltaGapStrict hp
  have hinj : Set.InjOn primeTupleProduct (states : Set (Fin ell → Nat)) := by
    dsimp [states, first, second]
    exact sectionSixDirectRangePrimeTupleUnion_product_injOn
      hepsilon hepsilonSmall hlength region
  have hfiber : ∀ D, D ∈ carrier →
      (states.filter (fun p => primeTupleProduct p = D)).card ≤ 1 := by
    intro D hD
    apply Finset.card_le_one.mpr
    intro p hp q hq
    apply hinj
    · exact Finset.mem_filter.mp hp |>.1
    · exact Finset.mem_filter.mp hq |>.1
    · exact (Finset.mem_filter.mp hp |>.2).trans
        (Finset.mem_filter.mp hq |>.2).symm
  have hpoint : ∀ p, p ∈ states → |value p| ≤ charge (primeTupleProduct p) := by
    intro p hp
    dsimp [value, charge]
    rw [sectionSixSiftedSum_eq_card_sub_density_mul_card]
    dsimp [X]
    apply le_of_eq
    congr 1
    ring
  have hcharge : ∀ D, D ∈ carrier → 0 ≤ charge D := by
    intro D hD
    exact abs_nonneg _
  have hbound := sum_abs_value_le_cardinality_charge_of_fiber_card
    states carrier primeTupleProduct value charge 1 hmap hfiber hpoint hcharge
  have hsum : (∑ p ∈ states, value p) =
      sectionSixDirectRangeBaseContribution digit epsilon delta ell length
          region .first +
        sectionSixDirectRangeBaseContribution digit epsilon delta ell length
          region .second := by
    dsimp [states, first, second, value]
    rw [Finset.sum_union hdisjoint]
    rfl
  calc
    abs (sectionSixDirectRangeBaseContribution digit epsilon delta ell length
        region .first +
      sectionSixDirectRangeBaseContribution digit epsilon delta ell length
        region .second) = abs (∑ p ∈ states, value p) := by rw [hsum]
    _ ≤ ∑ p ∈ states, |value p| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ (1 : Real) * ∑ D ∈ carrier, charge D := by simpa using hbound
    _ = sectionSixFundamentalResidual digit epsilon delta length := by
      dsimp [carrier, X, charge, sectionSixFundamentalResidual]
      simp only [one_mul]

end

end PrimesRestrictedDigits
