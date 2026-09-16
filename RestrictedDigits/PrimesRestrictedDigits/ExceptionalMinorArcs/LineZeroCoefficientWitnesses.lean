import PrimesRestrictedDigits.ExceptionalMinorArcs.LowHeightPlanePairs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Pi.Interval
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite witnesses for zero-coefficient plane relations

This is the exact finite carrier behind the zero-term estimate `(15.1)` in
`MAYNARD-PRD-PUBLISHED`, Lemma 15.2, pp. 210--211. It keeps the two
zero-member rectangles separate from positive relation witnesses.
-/

namespace PrimesRestrictedDigits

/-- One ordered pair together with a source-ordered coefficient quadruple. -/
structure LowHeightPlaneWitness (X : Nat) where
  /-- First member of the ordered pair. -/
  a1 : Fin X
  /-- Second member of the ordered pair. -/
  a2 : Fin X
  /-- The first three source-ordered relation coefficients. -/
  v : Fin 3 -> Int
  /-- The constant coefficient of the relation. -/
  v4 : Int
  deriving DecidableEq

namespace LowHeightPlaneWitness

@[ext]
theorem ext {X : Nat} {w w' : LowHeightPlaneWitness X}
    (ha1 : w.a1 = w'.a1) (ha2 : w.a2 = w'.a2)
    (hv : w.v = w'.v) (hv4 : w.v4 = w'.v4) :
    w = w' := by
  cases w
  cases w'
  simp_all

/-- The stored coefficients give a bounded nontrivial exact plane relation. -/
def IsRelation {X : Nat}
    (V : Real) (w : LowHeightPlaneWitness X) : Prop :=
  And (Or (Not (w.v = 0)) (Not (w.v4 = 0)))
    (And (forall i, abs ((w.v i : Int) : Real) <= V)
      (And (abs ((w.v4 : Int) : Real) <= V)
        (intVectorDot w.v (lineCoefficientVector w.a1 w.a2) +
          w.v4 = 0)))

/-- At least one coefficient of the stored quadruple vanishes. -/
def HasZeroCoefficient {X : Nat} (w : LowHeightPlaneWitness X) : Prop :=
  w.v 0 = 0 ∨ w.v 1 = 0 ∨ w.v 2 = 0 ∨ w.v4 = 0

theorem relation_eq {X : Nat} {V : Real}
    {w : LowHeightPlaneWitness X} (hw : w.IsRelation V) :
    w.v 0 * (w.a1.val : Int) + w.v 1 * (w.a2.val : Int) +
        w.v 2 * (X : Int) + w.v4 = 0 := by
  have hrelation := hw.2.2.2
  simp [intVectorDot, Fin.sum_univ_succ] at hrelation
  linear_combination hrelation

end LowHeightPlaneWitness

/-- All positive pair/coefficient choices in the exact finite coefficient
box, before imposing the plane relation. -/
noncomputable def positivePlaneWitnessCandidates {X : Nat}
    (C : Finset (Fin X)) (V : Real) :
    Finset (LowHeightPlaneWitness X) :=
  let Cpos := C.filter fun a => 0 < a.val
  let coeff := lineCoefficientBox V
  let vectors := Fintype.piFinset fun _ : Fin 3 => coeff
  ((Cpos.product Cpos).product (vectors.product coeff)).image fun data =>
    { a1 := data.1.1
      a2 := data.1.2
      v := data.2.1
      v4 := data.2.2 }

@[simp]
theorem mem_positivePlaneWitnessCandidates
    {X : Nat} {C : Finset (Fin X)} {V : Real}
    {w : LowHeightPlaneWitness X} :
    w ∈ positivePlaneWitnessCandidates C V <->
      And (w.a1 ∈ C) (And (0 < w.a1.val)
        (And (w.a2 ∈ C) (And (0 < w.a2.val)
          (And (forall i, w.v i ∈ lineCoefficientBox V)
            (w.v4 ∈ lineCoefficientBox V))))) := by
  classical
  constructor
  · intro hw
    rw [positivePlaneWitnessCandidates] at hw
    obtain ⟨data, hdata, rfl⟩ := Finset.mem_image.mp hw
    have houter := Finset.mem_product.mp hdata
    have hpairs := Finset.mem_product.mp houter.1
    have hcoeff := Finset.mem_product.mp houter.2
    have ha1 := Finset.mem_filter.mp hpairs.1
    have ha2 := Finset.mem_filter.mp hpairs.2
    exact ⟨ha1.1, ha1.2, ha2.1, ha2.2,
      Fintype.mem_piFinset.mp hcoeff.1, hcoeff.2⟩
  · intro hw
    rw [positivePlaneWitnessCandidates, Finset.mem_image]
    let data := ((w.a1, w.a2), (w.v, w.v4))
    refine ⟨data, ?_, rfl⟩
    dsimp only [data]
    rw [Finset.product_eq_sprod, Finset.mem_product]
    constructor
    · rw [Finset.product_eq_sprod, Finset.mem_product]
      exact ⟨Finset.mem_filter.mpr ⟨hw.1, hw.2.1⟩,
        Finset.mem_filter.mpr ⟨hw.2.2.1, hw.2.2.2.1⟩⟩
    · rw [Finset.product_eq_sprod, Finset.mem_product]
      exact ⟨Fintype.mem_piFinset.mpr hw.2.2.2.2.1,
        hw.2.2.2.2.2⟩

/-- Positive bounded nontrivial witnesses with at least one zero
coefficient. -/
noncomputable def positiveZeroCoefficientPlaneWitnesses {X : Nat}
    (C : Finset (Fin X)) (V : Real) :
    Finset (LowHeightPlaneWitness X) := by
  classical
  exact (positivePlaneWitnessCandidates C V).filter fun w =>
    And (w.IsRelation V) w.HasZeroCoefficient

@[simp]
theorem mem_positiveZeroCoefficientPlaneWitnesses
    {X : Nat} {C : Finset (Fin X)} {V : Real}
    {w : LowHeightPlaneWitness X} :
    w ∈ positiveZeroCoefficientPlaneWitnesses C V <->
      And (w ∈ positivePlaneWitnessCandidates C V)
        (And (w.IsRelation V) w.HasZeroCoefficient) := by
  classical
  simp [positiveZeroCoefficientPlaneWitnesses]

/-- Positive pairs obtained by forgetting a zero-coefficient relation
witness. -/
noncomputable def zeroCoefficientLowHeightPlanePairs {X : Nat}
    (C : Finset (Fin X)) (V : Real) : Finset (Prod (Fin X) (Fin X)) :=
  (positiveZeroCoefficientPlaneWitnesses C V).image fun w =>
    (w.a1, w.a2)

/-- The two ordered rectangles in `C^2` on which at least one member is zero. -/
noncomputable def zeroElementPlanePairCover {X : Nat}
    (C : Finset (Fin X)) : Finset (Prod (Fin X) (Fin X)) :=
  let Czero := C.filter fun a => a.val = 0
  (Czero.product C) ∪ (C.product Czero)

/-- The complete source zero-term cover: zero pair members or a positive
relation witness with a zero coefficient. -/
noncomputable def zeroTermLowHeightPlanePairCover {X : Nat}
    (C : Finset (Fin X)) (V : Real) : Finset (Prod (Fin X) (Fin X)) :=
  (zeroElementPlanePairCover C) ∪
    zeroCoefficientLowHeightPlanePairs C V

theorem zeroTermLowHeightPlanePairCover_subset_product
    {X : Nat} (C : Finset (Fin X)) (V : Real) :
    zeroTermLowHeightPlanePairCover C V ⊆ C.product C := by
  classical
  intro pair hpair
  rw [zeroTermLowHeightPlanePairCover, Finset.mem_union] at hpair
  rcases hpair with hzero | hcoeff
  · rw [zeroElementPlanePairCover, Finset.mem_union] at hzero
    rcases hzero with hleft | hright
    · have hdata := Finset.mem_product.mp hleft
      exact Finset.mem_product.mpr
        ⟨(Finset.mem_filter.mp hdata.1).1, hdata.2⟩
    · have hdata := Finset.mem_product.mp hright
      exact Finset.mem_product.mpr
        ⟨hdata.1, (Finset.mem_filter.mp hdata.2).1⟩
  · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hcoeff
    have hcandidate :=
      (mem_positiveZeroCoefficientPlaneWitnesses.mp hw).1
    have hdata := mem_positivePlaneWitnessCandidates.mp hcandidate
    exact Finset.mem_product.mpr ⟨hdata.1, hdata.2.2.1⟩

/-- Outside the zero-term cover, a low-height pair is positive and admits a
witness with all four coefficients nonzero. -/
theorem exists_all_coefficients_ne_zero_of_mem_lowHeightPlanePairs_of_not_mem_zeroTermCover
    {X : Nat} {C : Finset (Fin X)} {V : Real}
    {pair : Prod (Fin X) (Fin X)}
    (hV : 0 <= V) (hpair : pair ∈ lowHeightPlanePairs C V)
    (hzero : pair ∉ zeroTermLowHeightPlanePairCover C V) :
    And (Not (pair.1.val = 0)) (And (Not (pair.2.val = 0))
      (Exists fun w : LowHeightPlaneWitness X =>
        And (w.a1 = pair.1) (And (w.a2 = pair.2)
          (And (w.IsRelation V)
            (And (forall i, Not (w.v i = 0))
              (Not (w.v4 = 0))))))) := by
  classical
  have hdata := mem_lowHeightPlanePairs.mp hpair
  have ha1 : Not (pair.1.val = 0) := by
    intro ha1
    apply hzero
    rw [zeroTermLowHeightPlanePairCover, Finset.mem_union]
    apply Or.inl
    rw [zeroElementPlanePairCover, Finset.mem_union]
    exact Or.inl (Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨hdata.1, ha1⟩, hdata.2.1⟩)
  have ha2 : Not (pair.2.val = 0) := by
    intro ha2
    apply hzero
    rw [zeroTermLowHeightPlanePairCover, Finset.mem_union]
    apply Or.inl
    rw [zeroElementPlanePairCover, Finset.mem_union]
    exact Or.inr (Finset.mem_product.mpr
      ⟨hdata.1, Finset.mem_filter.mpr ⟨hdata.2.1, ha2⟩⟩)
  obtain ⟨v, v4, hnonzero, hv, hv4, hrelation⟩ := hdata.2.2
  let w : LowHeightPlaneWitness X :=
    { a1 := pair.1, a2 := pair.2, v := v, v4 := v4 }
  have hwRelation : w.IsRelation V := by
    exact ⟨hnonzero, hv, hv4, hrelation⟩
  have hwCandidate : w ∈ positivePlaneWitnessCandidates C V := by
    apply mem_positivePlaneWitnessCandidates.mpr
    refine ⟨hdata.1, Nat.pos_of_ne_zero ha1, hdata.2.1,
      Nat.pos_of_ne_zero ha2, ?_, ?_⟩
    · intro i
      exact (mem_lineCoefficientBox_iff hV).2 (hv i)
    · exact (mem_lineCoefficientBox_iff hV).2 hv4
  have hwNoZero : Not w.HasZeroCoefficient := by
    intro hwZero
    apply hzero
    rw [zeroTermLowHeightPlanePairCover, Finset.mem_union]
    apply Or.inr
    rw [zeroCoefficientLowHeightPlanePairs, Finset.mem_image]
    exact ⟨w,
      mem_positiveZeroCoefficientPlaneWitnesses.mpr
        ⟨hwCandidate, hwRelation, hwZero⟩,
      rfl⟩
  have hv0 : Not (w.v 0 = 0) := fun h => hwNoZero (Or.inl h)
  have hv1 : Not (w.v 1 = 0) := fun h => hwNoZero (Or.inr (Or.inl h))
  have hv2 : Not (w.v 2 = 0) :=
    fun h => hwNoZero (Or.inr (Or.inr (Or.inl h)))
  have hv4Nonzero : Not (w.v4 = 0) :=
    fun h => hwNoZero (Or.inr (Or.inr (Or.inr h)))
  refine ⟨ha1, ha2, w, rfl, rfl, hwRelation, ?_, hv4Nonzero⟩
  intro i
  fin_cases i
  · exact hv0
  · exact hv1
  · exact hv2

end PrimesRestrictedDigits
