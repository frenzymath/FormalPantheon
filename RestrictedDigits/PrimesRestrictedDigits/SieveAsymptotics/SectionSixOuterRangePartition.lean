import PrimesRestrictedDigits.SieveAsymptotics.SectionSixSourceTerminalStates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Four outer-product ranges in Proposition 6.1

The two source ranges expanded by the long recurrence and the two closed direct ranges form an
exact disjoint partition.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The two closed source-product ranges treated by one Buchstab step. -/
inductive SectionSixDirectBand
  | first
  | second
  deriving DecidableEq

/-- Literal membership in one of the two closed direct ranges. -/
def sectionSixDirectRangeMembership
    (band : SectionSixDirectBand)
    (X thetaOne thetaTwo d : Real) : Prop :=
  match band with
  | .first => X ^ thetaOne <= d ∧ d <= X ^ thetaTwo
  | .second => X ^ (1 - thetaTwo) <= d ∧ d <= X ^ (1 - thetaOne)

@[simp] theorem sectionSixDirectRangeMembership_first
    (X thetaOne thetaTwo d : Real) :
    sectionSixDirectRangeMembership .first X thetaOne thetaTwo d <->
      X ^ thetaOne <= d ∧ d <= X ^ thetaTwo :=
  Iff.rfl

@[simp] theorem sectionSixDirectRangeMembership_second
    (X thetaOne thetaTwo d : Real) :
    sectionSixDirectRangeMembership .second X thetaOne thetaTwo d <->
      X ^ (1 - thetaTwo) <= d ∧ d <= X ^ (1 - thetaOne) :=
  Iff.rfl

/-- The complete strict exponent order and the direct repeated-term margin. -/
theorem sectionSix_outerRange_exponent_order
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64) :
    sectionSixThetaOne epsilon < sectionSixThetaTwo epsilon ∧
      sectionSixThetaTwo epsilon < 1 - sectionSixThetaTwo epsilon ∧
      1 - sectionSixThetaTwo epsilon < 1 - sectionSixThetaOne epsilon ∧
      1 - sectionSixThetaOne epsilon < 50 / 77 - epsilon ∧
      1 - sectionSixThetaOne epsilon +
          2 * sectionSixThetaGap epsilon < 1 := by
  simp only [sectionSixThetaOne, sectionSixThetaTwo, sectionSixThetaGap]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Proposition 6.1 tuples whose complete outer product is in one closed
direct range. -/
noncomputable def sectionSixDirectRangePrimeTuples
    (epsilon : Real) (ell : Nat) (region : Set (Fin ell -> Real))
    (length : Nat) (band : SectionSixDirectBand) :
    Finset (Fin ell -> Nat) := by
  classical
  exact (propositionSixOnePrimeTuples epsilon ell region length).filter fun p =>
    sectionSixDirectRangeMembership band
      (((10 ^ length : Nat) : Real))
      (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon)
      (primeTupleProduct p : Real)

@[simp] theorem mem_sectionSixDirectRangePrimeTuples
    {epsilon : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {p : Fin ell -> Nat} :
    p ∈ sectionSixDirectRangePrimeTuples epsilon ell region length band <->
      p ∈ propositionSixOnePrimeTuples epsilon ell region length ∧
        sectionSixDirectRangeMembership band
          (((10 ^ length : Nat) : Real))
          (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon)
          (primeTupleProduct p : Real) := by
  simp [sectionSixDirectRangePrimeTuples]

private theorem sectionSix_outerRange_power_order
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {length : Nat} (hlength : 1 <= length) :
    (((10 ^ length : Nat) : Real)) ^ sectionSixThetaOne epsilon <
        (((10 ^ length : Nat) : Real)) ^ sectionSixThetaTwo epsilon ∧
      (((10 ^ length : Nat) : Real)) ^ sectionSixThetaTwo epsilon <
        (((10 ^ length : Nat) : Real)) ^ (1 - sectionSixThetaTwo epsilon) ∧
      (((10 ^ length : Nat) : Real)) ^ (1 - sectionSixThetaTwo epsilon) <
        (((10 ^ length : Nat) : Real)) ^ (1 - sectionSixThetaOne epsilon) := by
  have hXNat : 1 < 10 ^ length :=
    Nat.one_lt_pow (by omega : length ≠ 0) (by norm_num)
  have hX : (1 : Real) < ((10 ^ length : Nat) : Real) := by
    exact_mod_cast hXNat
  have horder := sectionSix_outerRange_exponent_order hepsilon hepsilonSmall
  exact ⟨Real.rpow_lt_rpow_of_exponent_lt hX horder.1,
    Real.rpow_lt_rpow_of_exponent_lt hX horder.2.1,
    Real.rpow_lt_rpow_of_exponent_lt hX horder.2.2.1⟩

/-- All six pairwise disjointness statements for the four exact ranges. -/
theorem sectionSixOuterRanges_pairwiseDisjoint
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {ell length : Nat} (hlength : 1 <= length)
    (region : Set (Fin ell -> Real)) :
    let low := sectionSixSourceBandPrimeTuples epsilon ell region length .low
    let first := sectionSixDirectRangePrimeTuples epsilon ell region length .first
    let high := sectionSixSourceBandPrimeTuples epsilon ell region length .high
    let second := sectionSixDirectRangePrimeTuples epsilon ell region length .second
    Disjoint low first ∧ Disjoint low high ∧ Disjoint low second ∧
      Disjoint first high ∧ Disjoint first second ∧ Disjoint high second := by
  dsimp only
  have hpower := sectionSix_outerRange_power_order
    hepsilon hepsilonSmall hlength
  constructor
  · rw [Finset.disjoint_left]
    intro p hpLow hpFirst
    have hLow := (mem_sectionSixSourceBandPrimeTuples.mp hpLow).2
    have hFirst := (mem_sectionSixDirectRangePrimeTuples.mp hpFirst).2
    simp only [sectionSixSourceBandMembership_low] at hLow
    simp only [sectionSixDirectRangeMembership_first] at hFirst
    exact (not_lt_of_ge hFirst.1) hLow
  constructor
  · rw [Finset.disjoint_left]
    intro p hpLow hpHigh
    have hLow := (mem_sectionSixSourceBandPrimeTuples.mp hpLow).2
    have hHigh := (mem_sectionSixSourceBandPrimeTuples.mp hpHigh).2
    simp only [sectionSixSourceBandMembership_low] at hLow
    simp only [sectionSixSourceBandMembership_high] at hHigh
    linarith [hpower.1]
  constructor
  · rw [Finset.disjoint_left]
    intro p hpLow hpSecond
    have hLow := (mem_sectionSixSourceBandPrimeTuples.mp hpLow).2
    have hSecond := (mem_sectionSixDirectRangePrimeTuples.mp hpSecond).2
    simp only [sectionSixSourceBandMembership_low] at hLow
    simp only [sectionSixDirectRangeMembership_second] at hSecond
    linarith [hpower.1, hpower.2.1]
  constructor
  · rw [Finset.disjoint_left]
    intro p hpFirst hpHigh
    have hFirst := (mem_sectionSixDirectRangePrimeTuples.mp hpFirst).2
    have hHigh := (mem_sectionSixSourceBandPrimeTuples.mp hpHigh).2
    simp only [sectionSixDirectRangeMembership_first] at hFirst
    simp only [sectionSixSourceBandMembership_high] at hHigh
    exact (not_lt_of_ge hFirst.2) hHigh.1
  constructor
  · rw [Finset.disjoint_left]
    intro p hpFirst hpSecond
    have hFirst := (mem_sectionSixDirectRangePrimeTuples.mp hpFirst).2
    have hSecond := (mem_sectionSixDirectRangePrimeTuples.mp hpSecond).2
    simp only [sectionSixDirectRangeMembership_first] at hFirst
    simp only [sectionSixDirectRangeMembership_second] at hSecond
    linarith [hpower.2.1]
  · rw [Finset.disjoint_left]
    intro p hpHigh hpSecond
    have hHigh := (mem_sectionSixSourceBandPrimeTuples.mp hpHigh).2
    have hSecond := (mem_sectionSixDirectRangePrimeTuples.mp hpSecond).2
    simp only [sectionSixSourceBandMembership_high] at hHigh
    simp only [sectionSixDirectRangeMembership_second] at hSecond
    exact (not_lt_of_ge hSecond.1) hHigh.2

/-- The two recurrence ranges and two closed direct ranges cover the complete
Proposition 6.1 tuple carrier. -/
theorem propositionSixOnePrimeTuples_eq_four_range_union
    {epsilon : Real} (_hepsilon : 0 < epsilon)
    (_hepsilonSmall : epsilon <= 1 / 64)
    {ell length : Nat} (_hlength : 1 <= length)
    (region : Set (Fin ell -> Real)) :
    propositionSixOnePrimeTuples epsilon ell region length =
      ((sectionSixSourceBandPrimeTuples epsilon ell region length .low ∪
          sectionSixDirectRangePrimeTuples epsilon ell region length .first) ∪
        sectionSixSourceBandPrimeTuples epsilon ell region length .high) ∪
      sectionSixDirectRangePrimeTuples epsilon ell region length .second := by
  classical
  ext p
  simp only [Finset.mem_union, mem_sectionSixSourceBandPrimeTuples,
    mem_sectionSixDirectRangePrimeTuples]
  constructor
  · intro hp
    have hpData := (mem_propositionSixOnePrimeTuples.mp hp).2
    dsimp [IsPropositionSixOnePrimeTuple] at hpData
    let X : Real := ((10 ^ length : Nat) : Real)
    let d : Real := (primeTupleProduct p : Real)
    by_cases hLow : d < X ^ sectionSixThetaOne epsilon
    · exact Or.inl (Or.inl (Or.inl ⟨hp, hLow⟩))
    by_cases hFirst : d <= X ^ sectionSixThetaTwo epsilon
    · exact Or.inl (Or.inl (Or.inr ⟨hp, le_of_not_gt hLow, hFirst⟩))
    by_cases hHigh : d < X ^ (1 - sectionSixThetaTwo epsilon)
    · exact Or.inl (Or.inr ⟨hp, lt_of_not_ge hFirst, hHigh⟩)
    · exact Or.inr ⟨hp, le_of_not_gt hHigh, hpData.2.2.2.1⟩
  · rintro (((⟨hp, _⟩ | ⟨hp, _⟩) | ⟨hp, _⟩) | ⟨hp, _⟩) <;> exact hp

/-- The literal Proposition 6.1 source sum is the sum over the four exact
outer-product ranges. -/
theorem propositionSixOneSum_eq_four_range_sums
    {epsilon : Real} (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    {ell length : Nat} (hlength : 1 <= length)
    (region : Set (Fin ell -> Real)) (digit : Fin 10) :
    propositionSixOneSum epsilon ell region digit length =
      ((∑ p ∈ sectionSixSourceBandPrimeTuples epsilon ell region length .low,
          sectionSixSiftedSum digit length (primeTupleProduct p).toPNat'
            (((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon)) +
        ∑ p ∈ sectionSixDirectRangePrimeTuples epsilon ell region length .first,
          sectionSixSiftedSum digit length (primeTupleProduct p).toPNat'
            (((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon)) +
      ∑ p ∈ sectionSixSourceBandPrimeTuples epsilon ell region length .high,
        sectionSixSiftedSum digit length (primeTupleProduct p).toPNat'
          (((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon) +
      ∑ p ∈ sectionSixDirectRangePrimeTuples epsilon ell region length .second,
        sectionSixSiftedSum digit length (primeTupleProduct p).toPNat'
          (((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon) := by
  let low := sectionSixSourceBandPrimeTuples epsilon ell region length .low
  let first := sectionSixDirectRangePrimeTuples epsilon ell region length .first
  let high := sectionSixSourceBandPrimeTuples epsilon ell region length .high
  let second := sectionSixDirectRangePrimeTuples epsilon ell region length .second
  let term : (Fin ell -> Nat) -> Real := fun p =>
    sectionSixSiftedSum digit length (primeTupleProduct p).toPNat'
      (((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon)
  have hpair := sectionSixOuterRanges_pairwiseDisjoint
    hepsilon hepsilonSmall hlength region
  have hLowFirst : Disjoint low first := hpair.1
  have hLowFirstHigh : Disjoint (low ∪ first) high :=
    Finset.disjoint_union_left.mpr ⟨hpair.2.1, hpair.2.2.2.1⟩
  have hAllSecond : Disjoint ((low ∪ first) ∪ high) second :=
    Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_left.mpr
        ⟨hpair.2.2.1, hpair.2.2.2.2.1⟩,
        hpair.2.2.2.2.2⟩
  unfold propositionSixOneSum
  rw [propositionSixOnePrimeTuples_eq_four_range_union
      hepsilon hepsilonSmall hlength region,
    Finset.sum_union hAllSecond, Finset.sum_union hLowFirstHigh,
    Finset.sum_union hLowFirst]

end

end PrimesRestrictedDigits
