import PrimesRestrictedDigits.MajorArcs.RationalApproximation

/-!
# Canonical major-arc partition

This implements the reduced-denominator priority partition. The three classes partition the
raw major arcs without claiming equality with the overlapping classes printed in Section 11 of
`MAYNARD-PRD-PUBLISHED`.
-/

namespace PrimesRestrictedDigits

def majorArcNondivisorApproximation (X a : Nat) (Q : Real) : Prop :=
  ∃ r : Rat, majorArcRationalApproximation X a Q r ∧ ¬r.den ∣ X

def majorArcDivisorNonzeroApproximation (X a : Nat) (Q : Real) : Prop :=
  ∃ r : Rat, majorArcRationalApproximation X a Q r ∧ r.den ∣ X ∧
    r ≠ (a : Rat) / (X : Rat)

def majorArcExactApproximation (X a : Nat) (Q : Real) : Prop :=
  ∃ r : Rat, majorArcRationalApproximation X a Q r ∧ r.den ∣ X ∧
    r = (a : Rat) / (X : Rat)

def majorArcClassThree (X a : Nat) (Q : Real) : Prop :=
  majorArcExactApproximation X a Q

def majorArcClassTwo (X a : Nat) (Q : Real) : Prop :=
  majorArcDivisorNonzeroApproximation X a Q ∧
    ¬majorArcExactApproximation X a Q

def majorArcClassOne (X a : Nat) (Q : Real) : Prop :=
  majorArcNondivisorApproximation X a Q ∧
    ¬majorArcDivisorNonzeroApproximation X a Q ∧
    ¬majorArcExactApproximation X a Q

noncomputable def majorArcRawFrequencies (X : Nat) (Q : Real) : Finset Nat :=
  by classical exact
    (Finset.range X).filter fun a => majorArcRawApproximation X a Q

noncomputable def majorArcClassOneFrequencies
    (X : Nat) (Q : Real) : Finset Nat :=
  by classical exact
    (Finset.range X).filter fun a => majorArcClassOne X a Q

noncomputable def majorArcClassTwoFrequencies
    (X : Nat) (Q : Real) : Finset Nat :=
  by classical exact
    (Finset.range X).filter fun a => majorArcClassTwo X a Q

noncomputable def majorArcClassThreeFrequencies
    (X : Nat) (Q : Real) : Finset Nat :=
  by classical exact
    (Finset.range X).filter fun a => majorArcClassThree X a Q

theorem majorArcRawApproximation_iff_classes (X a : Nat) (Q : Real) :
    majorArcRawApproximation X a Q ↔
      majorArcClassOne X a Q ∨ majorArcClassTwo X a Q ∨
        majorArcClassThree X a Q := by
  unfold majorArcClassOne majorArcClassTwo majorArcClassThree
  constructor
  · rintro ⟨r, hr⟩
    by_cases hexact : majorArcExactApproximation X a Q
    · exact Or.inr (Or.inr hexact)
    by_cases hdivisor : majorArcDivisorNonzeroApproximation X a Q
    · exact Or.inr (Or.inl ⟨hdivisor, hexact⟩)
    refine Or.inl ⟨?_, hdivisor, hexact⟩
    by_cases hden : r.den ∣ X
    · by_cases heq : r = (a : Rat) / (X : Rat)
      · exact (hexact ⟨r, hr, hden, heq⟩).elim
      · exact (hdivisor ⟨r, hr, hden, heq⟩).elim
    · exact ⟨r, hr, hden⟩
  · rintro (hclassOne | hclassTwo | hclassThree)
    · rcases hclassOne.1 with ⟨r, hr, _⟩
      exact ⟨r, hr⟩
    · rcases hclassTwo.1 with ⟨r, hr, _⟩
      exact ⟨r, hr⟩
    · rcases hclassThree with ⟨r, hr, _⟩
      exact ⟨r, hr⟩

theorem majorArcClassOne.nondivisor
    {X a : Nat} {Q : Real} (ha : majorArcClassOne X a Q) :
    majorArcNondivisorApproximation X a Q :=
  ha.1

theorem majorArcClassTwo.divisorNonzero
    {X a : Nat} {Q : Real} (ha : majorArcClassTwo X a Q) :
    majorArcDivisorNonzeroApproximation X a Q :=
  ha.1

theorem majorArcClassThree.exact
    {X a : Nat} {Q : Real} (ha : majorArcClassThree X a Q) :
    majorArcExactApproximation X a Q :=
  ha

theorem majorArcDivisorNonzeroApproximation.offset
    {X a : Nat} {Q : Real} (hX : 0 < X)
    (ha : majorArcDivisorNonzeroApproximation X a Q) :
    ∃ r : Rat, majorArcRationalApproximation X a Q r ∧ r.den ∣ X ∧
      majorArcSignedOffset X a r ≠ 0 ∧
      abs (majorArcSignedOffset X a r : Real) <= Q := by
  rcases ha with ⟨r, hr, hden, hne⟩
  refine ⟨r, hr, hden, ?_, abs_majorArcSignedOffset_le hX hden hr⟩
  apply (majorArcSignedOffset_ne_zero_iff hX hden).2
  exact fun heq => hne heq.symm

theorem majorArcClassFrequencies_union (X : Nat) (Q : Real) :
    majorArcClassOneFrequencies X Q ∪ majorArcClassTwoFrequencies X Q ∪
        majorArcClassThreeFrequencies X Q =
      majorArcRawFrequencies X Q := by
  classical
  apply Finset.ext
  intro a
  simp only [majorArcClassOneFrequencies, majorArcClassTwoFrequencies,
    majorArcClassThreeFrequencies, majorArcRawFrequencies, Finset.mem_union,
    Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ((⟨ha, hclassOne⟩ | ⟨ha, hclassTwo⟩) | ⟨ha, hclassThree⟩)
    · exact ⟨ha, (majorArcRawApproximation_iff_classes X a Q).2
        (Or.inl hclassOne)⟩
    · exact ⟨ha, (majorArcRawApproximation_iff_classes X a Q).2
        (Or.inr (Or.inl hclassTwo))⟩
    · exact ⟨ha, (majorArcRawApproximation_iff_classes X a Q).2
        (Or.inr (Or.inr hclassThree))⟩
  · rintro ⟨ha, hraw⟩
    rcases (majorArcRawApproximation_iff_classes X a Q).1 hraw with
      hclassOne | hclassTwo | hclassThree
    · exact Or.inl (Or.inl ⟨ha, hclassOne⟩)
    · exact Or.inl (Or.inr ⟨ha, hclassTwo⟩)
    · exact Or.inr ⟨ha, hclassThree⟩

theorem majorArcClassOne_disjoint_classTwo (X : Nat) (Q : Real) :
    Disjoint (majorArcClassOneFrequencies X Q)
      (majorArcClassTwoFrequencies X Q) := by
  classical
  rw [Finset.disjoint_left]
  intro a hclassOne hclassTwo
  simp only [majorArcClassOneFrequencies, majorArcClassTwoFrequencies,
    Finset.mem_filter, majorArcClassOne, majorArcClassTwo] at hclassOne hclassTwo
  exact hclassOne.2.2.1 hclassTwo.2.1

theorem majorArcClassOne_disjoint_classThree (X : Nat) (Q : Real) :
    Disjoint (majorArcClassOneFrequencies X Q)
      (majorArcClassThreeFrequencies X Q) := by
  classical
  rw [Finset.disjoint_left]
  intro a hclassOne hclassThree
  simp only [majorArcClassOneFrequencies, majorArcClassThreeFrequencies,
    Finset.mem_filter, majorArcClassOne, majorArcClassThree] at hclassOne hclassThree
  exact hclassOne.2.2.2 hclassThree.2

theorem majorArcClassTwo_disjoint_classThree (X : Nat) (Q : Real) :
    Disjoint (majorArcClassTwoFrequencies X Q)
      (majorArcClassThreeFrequencies X Q) := by
  classical
  rw [Finset.disjoint_left]
  intro a hclassTwo hclassThree
  simp only [majorArcClassTwoFrequencies, majorArcClassThreeFrequencies,
    Finset.mem_filter, majorArcClassTwo, majorArcClassThree] at hclassTwo hclassThree
  exact hclassTwo.2.2 hclassThree.2

end PrimesRestrictedDigits
