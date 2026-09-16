import PrimesRestrictedDigits.ExceptionalMinorArcs.LineZeroCoefficientWitnesses
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.SDiff

/-!
# Corrected second-moment carrier for low-height plane relations

This implements the ordered existential `N_2` carrier from
`MAYNARD-PRD-PUBLISHED`, Lemma 15.2, pp. 211--212, directly from the exact
integer relations. Coefficient witnesses form a separate finite overcount.
-/

namespace PrimesRestrictedDigits

namespace LowHeightPlaneWitness

/-- Every coefficient in the stored relation is nonzero. -/
def AllCoefficientsNonzero {X : Nat}
    (w : LowHeightPlaneWitness X) : Prop :=
  And (forall i, w.v i ≠ 0) (w.v4 ≠ 0)

end LowHeightPlaneWitness

/-- An exact bounded plane relation with all four coefficients nonzero. -/
def HasAllNonzeroLineRelation {X : Nat}
    (V : Real) (a1 a2 : Fin X) : Prop :=
  Exists fun w : LowHeightPlaneWitness X =>
    And (w.a1 = a1) (And (w.a2 = a2)
      (And (w.IsRelation V) w.AllCoefficientsNonzero))

/-- The source-ordered existential triples `((a2,a2'),a1)` in corrected
`N_2`. Different coefficient witnesses for one triple are identified. -/
noncomputable def lineSecondMomentTriples {X : Nat}
    (C D : Finset (Fin X)) (V : Real) :
    Finset ((Fin X × Fin X) × Fin X) := by
  classical
  exact ((D.product D).product C).filter fun triple =>
    And (0 < triple.1.1.val) (And (0 < triple.1.2.val)
      (And (0 < triple.2.val)
        (And (HasAllNonzeroLineRelation V triple.2 triple.1.1)
          (HasAllNonzeroLineRelation V triple.2 triple.1.2))))

@[simp]
theorem mem_lineSecondMomentTriples
    {X : Nat} {C D : Finset (Fin X)} {V : Real}
    {triple : (Fin X × Fin X) × Fin X} :
    triple ∈ lineSecondMomentTriples C D V ↔
      And (triple.1.1 ∈ D) (And (triple.1.2 ∈ D)
        (And (triple.2 ∈ C) (And (0 < triple.1.1.val)
          (And (0 < triple.1.2.val) (And (0 < triple.2.val)
            (And (HasAllNonzeroLineRelation V triple.2 triple.1.1)
              (HasAllNonzeroLineRelation V triple.2 triple.1.2))))))) := by
  classical
  rcases triple with ⟨⟨a2, a2'⟩, a1⟩
  simp [lineSecondMomentTriples, and_assoc]

/-- Positive finite coefficient-box witnesses having no zero coefficient. -/
noncomputable def positiveAllNonzeroPlaneWitnesses {X : Nat}
    (C : Finset (Fin X)) (V : Real) :
    Finset (LowHeightPlaneWitness X) := by
  classical
  exact (positivePlaneWitnessCandidates C V).filter fun w =>
    And (w.IsRelation V) w.AllCoefficientsNonzero

@[simp]
theorem mem_positiveAllNonzeroPlaneWitnesses
    {X : Nat} {C : Finset (Fin X)} {V : Real}
    {w : LowHeightPlaneWitness X} :
    w ∈ positiveAllNonzeroPlaneWitnesses C V ↔
      And (w ∈ positivePlaneWitnessCandidates C V)
        (And (w.IsRelation V) w.AllCoefficientsNonzero) := by
  classical
  simp [positiveAllNonzeroPlaneWitnesses]

/-- Ordered pairs of all-nonzero witnesses with a common first member and
both second members in `D`. -/
noncomputable def lineSecondMomentWitnessPairs {X : Nat}
    (C D : Finset (Fin X)) (V : Real) :
    Finset (LowHeightPlaneWitness X × LowHeightPlaneWitness X) := by
  classical
  exact ((positiveAllNonzeroPlaneWitnesses C V).product
      (positiveAllNonzeroPlaneWitnesses C V)).filter fun pair =>
    And (pair.1.a1 = pair.2.a1)
      (And (pair.1.a2 ∈ D) (pair.2.a2 ∈ D))

@[simp]
theorem mem_lineSecondMomentWitnessPairs
    {X : Nat} {C D : Finset (Fin X)} {V : Real}
    {pair : LowHeightPlaneWitness X × LowHeightPlaneWitness X} :
    pair ∈ lineSecondMomentWitnessPairs C D V ↔
      And (pair.1 ∈ positiveAllNonzeroPlaneWitnesses C V)
        (And (pair.2 ∈ positiveAllNonzeroPlaneWitnesses C V)
          (And (pair.1.a1 = pair.2.a1)
            (And (pair.1.a2 ∈ D) (pair.2.a2 ∈ D)))) := by
  classical
  rcases pair with ⟨w, w'⟩
  simp [lineSecondMomentWitnessPairs, and_assoc]

/-- Forget the two coefficient witnesses while preserving the source order. -/
def lineSecondMomentWitnessPairProjection {X : Nat}
    (pair : LowHeightPlaneWitness X × LowHeightPlaneWitness X) :
    (Fin X × Fin X) × Fin X :=
  ((pair.1.a2, pair.2.a2), pair.1.a1)

/-- Under the natural localized-class inclusion, the witness projection is
exactly the existential corrected `N_2` carrier. -/
theorem image_lineSecondMomentWitnessPairs_eq_triples
    {X : Nat} {C D : Finset (Fin X)} {V : Real}
    (hV : 0 ≤ V) (hDC : D ⊆ C) :
    (lineSecondMomentWitnessPairs C D V).image
        lineSecondMomentWitnessPairProjection =
      lineSecondMomentTriples C D V := by
  classical
  apply Finset.Subset.antisymm
  · intro triple htriple
    obtain ⟨pair, hpair, rfl⟩ := Finset.mem_image.mp htriple
    have hp := mem_lineSecondMomentWitnessPairs.mp hpair
    have hw := mem_positiveAllNonzeroPlaneWitnesses.mp hp.1
    have hw' := mem_positiveAllNonzeroPlaneWitnesses.mp hp.2.1
    have hc := mem_positivePlaneWitnessCandidates.mp hw.1
    have hc' := mem_positivePlaneWitnessCandidates.mp hw'.1
    apply mem_lineSecondMomentTriples.mpr
    exact ⟨hp.2.2.2.1, hp.2.2.2.2, hc.1, hc.2.2.2.1,
      hc'.2.2.2.1, hc.2.1,
      ⟨pair.1, rfl, rfl, hw.2.1, hw.2.2⟩,
      ⟨pair.2, hp.2.2.1.symm, rfl, hw'.2.1, hw'.2.2⟩⟩
  · intro triple htriple
    have ht := mem_lineSecondMomentTriples.mp htriple
    obtain ⟨w, hw1, hw2, hwRelation, hwNonzero⟩ := ht.2.2.2.2.2.2.1
    obtain ⟨w', hw1', hw2', hwRelation', hwNonzero'⟩ :=
      ht.2.2.2.2.2.2.2
    have hwCandidate : w ∈ positivePlaneWitnessCandidates C V := by
      apply mem_positivePlaneWitnessCandidates.mpr
      refine ⟨hw1.symm ▸ ht.2.2.1, hw1.symm ▸ ht.2.2.2.2.2.1,
        hDC (hw2.symm ▸ ht.1), hw2.symm ▸ ht.2.2.2.1, ?_, ?_⟩
      · intro i
        exact (mem_lineCoefficientBox_iff hV).2 (hwRelation.2.1 i)
      · exact (mem_lineCoefficientBox_iff hV).2 hwRelation.2.2.1
    have hwCandidate' : w' ∈ positivePlaneWitnessCandidates C V := by
      apply mem_positivePlaneWitnessCandidates.mpr
      refine ⟨hw1'.symm ▸ ht.2.2.1, hw1'.symm ▸ ht.2.2.2.2.2.1,
        hDC (hw2'.symm ▸ ht.2.1), hw2'.symm ▸ ht.2.2.2.2.1, ?_, ?_⟩
      · intro i
        exact (mem_lineCoefficientBox_iff hV).2 (hwRelation'.2.1 i)
      · exact (mem_lineCoefficientBox_iff hV).2 hwRelation'.2.2.1
    apply Finset.mem_image.mpr
    refine ⟨(w, w'), mem_lineSecondMomentWitnessPairs.mpr
      ⟨mem_positiveAllNonzeroPlaneWitnesses.mpr
          ⟨hwCandidate, hwRelation, hwNonzero⟩,
        mem_positiveAllNonzeroPlaneWitnesses.mpr
          ⟨hwCandidate', hwRelation', hwNonzero'⟩,
        hw1.trans hw1'.symm, hw2 ▸ ht.1, hw2' ▸ ht.2.1⟩, ?_⟩
    simp [lineSecondMomentWitnessPairProjection, hw1,  hw2, hw2']

theorem card_lineSecondMomentTriples_le_witnessPairs
    {X : Nat} {C D : Finset (Fin X)} {V : Real}
    (hV : 0 ≤ V) (hDC : D ⊆ C) :
    (lineSecondMomentTriples C D V).card ≤
      (lineSecondMomentWitnessPairs C D V).card := by
  rw [← image_lineSecondMomentWitnessPairs_eq_triples hV hDC]
  exact Finset.card_image_le

/-- Low-height pairs assigned to the nonzero-coefficient side of the
project's disjoint pair decomposition. -/
noncomputable def residualLowHeightPlanePairs {X : Nat}
    (C : Finset (Fin X)) (V : Real) : Finset (Fin X × Fin X) :=
  lowHeightPlanePairs C V \ zeroTermLowHeightPlanePairCover C V

@[simp]
theorem mem_residualLowHeightPlanePairs
    {X : Nat} {C : Finset (Fin X)} {V : Real}
    {pair : Fin X × Fin X} :
    pair ∈ residualLowHeightPlanePairs C V ↔
      And (pair ∈ lowHeightPlanePairs C V)
        (pair ∉ zeroTermLowHeightPlanePairCover C V) := by
  classical
  simp [residualLowHeightPlanePairs]

theorem lowHeightPlanePairs_subset_zeroTerm_union_residual
    {X : Nat} (C : Finset (Fin X)) (V : Real) :
    lowHeightPlanePairs C V ⊆
      zeroTermLowHeightPlanePairCover C V ∪
        residualLowHeightPlanePairs C V := by
  classical
  intro pair hpair
  by_cases hzero : pair ∈ zeroTermLowHeightPlanePairCover C V
  · exact Finset.mem_union_left _ hzero
  · exact Finset.mem_union_right _
      (mem_residualLowHeightPlanePairs.mpr ⟨hpair, hzero⟩)

/-- A residual pair has a finite positive all-nonzero witness over `C`. -/
theorem exists_mem_positiveAllNonzeroPlaneWitnesses_of_mem_residual
    {X : Nat} {C : Finset (Fin X)} {V : Real}
    {pair : Fin X × Fin X} (hV : 0 ≤ V)
    (hpair : pair ∈ residualLowHeightPlanePairs C V) :
    Exists fun w : LowHeightPlaneWitness X =>
      And (w ∈ positiveAllNonzeroPlaneWitnesses C V)
        (And (w.a1 = pair.1) (w.a2 = pair.2)) := by
  have hr := mem_residualLowHeightPlanePairs.mp hpair
  obtain ⟨ha1, ha2, w, hw1, hw2, hwRelation, hwv, hw4⟩ :=
    exists_all_coefficients_ne_zero_of_mem_lowHeightPlanePairs_of_not_mem_zeroTermCover
      hV hr.1 hr.2
  have hlow := mem_lowHeightPlanePairs.mp hr.1
  have hwCandidate : w ∈ positivePlaneWitnessCandidates C V := by
    apply mem_positivePlaneWitnessCandidates.mpr
    refine ⟨hw1.symm ▸ hlow.1, hw1.symm ▸ Nat.pos_of_ne_zero ha1,
      hw2.symm ▸ hlow.2.1, hw2.symm ▸ Nat.pos_of_ne_zero ha2, ?_, ?_⟩
    · intro i
      exact (mem_lineCoefficientBox_iff hV).2 (hwRelation.2.1 i)
    · exact (mem_lineCoefficientBox_iff hV).2 hwRelation.2.2.1
  exact ⟨w, mem_positiveAllNonzeroPlaneWitnesses.mpr
    ⟨hwCandidate, hwRelation, hwv, hw4⟩, hw1, hw2⟩

/-- Source-ordered triples whose two pairs lie outside the zero-term cover. -/
noncomputable def residualLineSecondMomentTriples {X : Nat}
    (C D : Finset (Fin X)) (V : Real) :
    Finset ((Fin X × Fin X) × Fin X) := by
  classical
  exact ((D.product D).product C).filter fun triple =>
    And ((triple.2, triple.1.1) ∈ residualLowHeightPlanePairs C V)
      ((triple.2, triple.1.2) ∈ residualLowHeightPlanePairs C V)

@[simp]
theorem mem_residualLineSecondMomentTriples
    {X : Nat} {C D : Finset (Fin X)} {V : Real}
    {triple : (Fin X × Fin X) × Fin X} :
    triple ∈ residualLineSecondMomentTriples C D V ↔
      And (triple.1.1 ∈ D) (And (triple.1.2 ∈ D)
        (And (triple.2 ∈ C)
          (And ((triple.2, triple.1.1) ∈
              residualLowHeightPlanePairs C V)
            ((triple.2, triple.1.2) ∈
              residualLowHeightPlanePairs C V)))) := by
  classical
  rcases triple with ⟨⟨a2, a2'⟩, a1⟩
  simp [residualLineSecondMomentTriples, and_assoc]

theorem residualLineSecondMomentTriples_subset
    {X : Nat} {C D : Finset (Fin X)} {V : Real}
    (hV : 0 ≤ V) :
    residualLineSecondMomentTriples C D V ⊆
      lineSecondMomentTriples C D V := by
  intro triple htriple
  have ht := mem_residualLineSecondMomentTriples.mp htriple
  obtain ⟨w, hw, hw1, hw2⟩ :=
    exists_mem_positiveAllNonzeroPlaneWitnesses_of_mem_residual hV ht.2.2.2.1
  obtain ⟨w', hw', hw1', hw2'⟩ :=
    exists_mem_positiveAllNonzeroPlaneWitnesses_of_mem_residual hV ht.2.2.2.2
  change w.a1 = triple.2 at hw1
  change w.a2 = triple.1.1 at hw2
  change w'.a1 = triple.2 at hw1'
  change w'.a2 = triple.1.2 at hw2'
  have hc := mem_positivePlaneWitnessCandidates.mp
    (mem_positiveAllNonzeroPlaneWitnesses.mp hw).1
  have hc' := mem_positivePlaneWitnessCandidates.mp
    (mem_positiveAllNonzeroPlaneWitnesses.mp hw').1
  have hr := mem_positiveAllNonzeroPlaneWitnesses.mp hw
  have hr' := mem_positiveAllNonzeroPlaneWitnesses.mp hw'
  apply mem_lineSecondMomentTriples.mpr
  exact ⟨ht.1, ht.2.1, ht.2.2.1, hw2.symm ▸ hc.2.2.2.1,
    hw2'.symm ▸ hc'.2.2.2.1, hw1.symm ▸ hc.2.1,
    ⟨w, hw1, hw2, hr.2.1, hr.2.2⟩,
    ⟨w', hw1', hw2', hr'.2.1, hr'.2.2⟩⟩

theorem residualLineSecondMomentTriples_subset_image_witnessPairs
    {X : Nat} {C D : Finset (Fin X)} {V : Real}
    (hV : 0 ≤ V) :
    residualLineSecondMomentTriples C D V ⊆
      (lineSecondMomentWitnessPairs C D V).image
        lineSecondMomentWitnessPairProjection := by
  classical
  intro triple htriple
  have ht := mem_residualLineSecondMomentTriples.mp htriple
  obtain ⟨w, hw, hw1, hw2⟩ :=
    exists_mem_positiveAllNonzeroPlaneWitnesses_of_mem_residual hV ht.2.2.2.1
  obtain ⟨w', hw', hw1', hw2'⟩ :=
    exists_mem_positiveAllNonzeroPlaneWitnesses_of_mem_residual hV ht.2.2.2.2
  change w.a1 = triple.2 at hw1
  change w.a2 = triple.1.1 at hw2
  change w'.a1 = triple.2 at hw1'
  change w'.a2 = triple.1.2 at hw2'
  apply Finset.mem_image.mpr
  refine ⟨(w, w'), mem_lineSecondMomentWitnessPairs.mpr
    ⟨hw, hw', hw1.trans hw1'.symm, hw2 ▸ ht.1, hw2' ▸ ht.2.1⟩, ?_⟩
  simp [lineSecondMomentWitnessPairProjection, hw1,  hw2, hw2']

theorem card_residualLineSecondMomentTriples_le_witnessPairs
    {X : Nat} {C D : Finset (Fin X)} {V : Real}
    (hV : 0 ≤ V) :
    (residualLineSecondMomentTriples C D V).card ≤
      (lineSecondMomentWitnessPairs C D V).card := by
  calc
    (residualLineSecondMomentTriples C D V).card ≤
        ((lineSecondMomentWitnessPairs C D V).image
          lineSecondMomentWitnessPairProjection).card :=
      Finset.card_le_card
        (residualLineSecondMomentTriples_subset_image_witnessPairs hV)
    _ ≤ (lineSecondMomentWitnessPairs C D V).card :=
      Finset.card_image_le

end PrimesRestrictedDigits
