import PrimesRestrictedDigits.ExceptionalMinorArcs.LineSecondMomentCarrier
import Mathlib.Analysis.Real.Sqrt

/-!
# Exact fibers for the line second-moment Cauchy step

This proves the finite pair and triple fiber identities used in the Cauchy step of
`MAYNARD-PRD-PUBLISHED`, Lemma 15.2, pp. 211--214.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- Residual pairs whose second member lies in one fixed
modulus/minimum class. -/
noncomputable def residualLowHeightPlanePairsInClass {X : Nat}
    (C D : Finset (Fin X)) (V : Real) : Finset (Fin X × Fin X) := by
  classical
  exact (residualLowHeightPlanePairs C V).filter fun pair => pair.2 ∈ D

@[simp]
theorem mem_residualLowHeightPlanePairsInClass
    {X : Nat} {C D : Finset (Fin X)} {V : Real}
    {pair : Fin X × Fin X} :
    pair ∈ residualLowHeightPlanePairsInClass C D V ↔
      And (pair ∈ residualLowHeightPlanePairs C V) (pair.2 ∈ D) := by
  classical
  simp [residualLowHeightPlanePairsInClass]

/-- The second-coordinate fiber over a fixed common first member. -/
noncomputable def residualLowHeightPlanePairFiber {X : Nat}
    (C D : Finset (Fin X)) (V : Real) (a1 : Fin X) : Finset (Fin X) := by
  classical
  exact D.filter fun a2 =>
    (a1, a2) ∈ residualLowHeightPlanePairs C V

@[simp]
theorem mem_residualLowHeightPlanePairFiber
    {X : Nat} {C D : Finset (Fin X)} {V : Real}
    {a1 a2 : Fin X} :
    a2 ∈ residualLowHeightPlanePairFiber C D V a1 ↔
      And (a2 ∈ D)
        ((a1, a2) ∈ residualLowHeightPlanePairs C V) := by
  classical
  simp [residualLowHeightPlanePairFiber]

private theorem card_fixedFirst_residualPairsInClass_eq_fiber
    {X : Nat} (C D : Finset (Fin X)) (V : Real) (a1 : Fin X) :
    ((residualLowHeightPlanePairsInClass C D V).filter fun pair =>
        pair.1 = a1).card =
      (residualLowHeightPlanePairFiber C D V a1).card := by
  classical
  apply Finset.card_bij (fun pair _hpair => pair.2)
  · intro pair hpair
    have hp := Finset.mem_filter.mp hpair
    have hclass := mem_residualLowHeightPlanePairsInClass.mp hp.1
    apply mem_residualLowHeightPlanePairFiber.mpr
    refine ⟨hclass.2, ?_⟩
    rw [← hp.2]
    exact hclass.1
  · intro pair hp pair' hp' heq
    apply Prod.ext
    · exact (Finset.mem_filter.mp hp).2.trans
        (Finset.mem_filter.mp hp').2.symm
    · exact heq
  · intro a2 ha2
    have hfiber := mem_residualLowHeightPlanePairFiber.mp ha2
    refine ⟨(a1, a2), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    exact ⟨mem_residualLowHeightPlanePairsInClass.mpr
      ⟨hfiber.2, hfiber.1⟩, rfl⟩

/-- Exact decomposition of one second-coordinate class into fixed-first
fibers. -/
theorem card_residualLowHeightPlanePairsInClass_eq_sum_card_fiber
    {X : Nat} (C D : Finset (Fin X)) (V : Real) :
    (residualLowHeightPlanePairsInClass C D V).card =
      ∑ a1 ∈ C, (residualLowHeightPlanePairFiber C D V a1).card := by
  classical
  let S := residualLowHeightPlanePairsInClass C D V
  have hmaps : Set.MapsTo Prod.fst (S : Set (Fin X × Fin X))
      (C : Set (Fin X)) := by
    intro pair hpair
    have hresidual :=
      (mem_residualLowHeightPlanePairsInClass.mp hpair).1
    exact (mem_lowHeightPlanePairs.mp
      (mem_residualLowHeightPlanePairs.mp hresidual).1).1
  have hdecomp := Finset.card_eq_sum_card_fiberwise hmaps
  calc
    (residualLowHeightPlanePairsInClass C D V).card =
        ∑ a1 ∈ C,
          ((residualLowHeightPlanePairsInClass C D V).filter fun pair =>
            pair.1 = a1).card := by
      simpa only [S] using hdecomp
    _ = ∑ a1 ∈ C,
        (residualLowHeightPlanePairFiber C D V a1).card := by
      apply Finset.sum_congr rfl
      intro a1 _ha1
      exact card_fixedFirst_residualPairsInClass_eq_fiber C D V a1

private theorem card_fixedFirst_residualTriples_eq_fiber_sq
    {X : Nat} (C D : Finset (Fin X)) (V : Real)
    (a1 : Fin X) (ha1 : a1 ∈ C) :
    ((residualLineSecondMomentTriples C D V).filter fun triple =>
        triple.2 = a1).card =
      (residualLowHeightPlanePairFiber C D V a1).card ^ 2 := by
  classical
  let F := residualLowHeightPlanePairFiber C D V a1
  calc
    ((residualLineSecondMomentTriples C D V).filter fun triple =>
        triple.2 = a1).card = (F.product F).card := by
      apply Finset.card_bij (fun triple _htriple => triple.1)
      · intro triple htriple
        have ht := Finset.mem_filter.mp htriple
        have hdata := mem_residualLineSecondMomentTriples.mp ht.1
        apply Finset.mem_product.mpr
        constructor
        · apply mem_residualLowHeightPlanePairFiber.mpr
          refine ⟨hdata.1, ?_⟩
          rw [← ht.2]
          exact hdata.2.2.2.1
        · apply mem_residualLowHeightPlanePairFiber.mpr
          refine ⟨hdata.2.1, ?_⟩
          rw [← ht.2]
          exact hdata.2.2.2.2
      · intro triple ht triple' ht' heq
        apply Prod.ext
        · exact heq
        · exact (Finset.mem_filter.mp ht).2.trans
            (Finset.mem_filter.mp ht').2.symm
      · intro pair hpair
        have hp := Finset.mem_product.mp hpair
        have hp1 := mem_residualLowHeightPlanePairFiber.mp hp.1
        have hp2 := mem_residualLowHeightPlanePairFiber.mp hp.2
        refine ⟨(pair, a1), ?_, rfl⟩
        apply Finset.mem_filter.mpr
        exact ⟨mem_residualLineSecondMomentTriples.mpr
          ⟨hp1.1, hp2.1, ha1, hp1.2, hp2.2⟩, rfl⟩
    _ = F.card ^ 2 := by
      rw [Finset.product_eq_sprod, Finset.card_product, pow_two]

/-- The residual second-moment triple carrier is exactly the sum of the
squares of the fixed-first pair fibers. -/
theorem card_residualLineSecondMomentTriples_eq_sum_sq_card_fiber
    {X : Nat} (C D : Finset (Fin X)) (V : Real) :
    (residualLineSecondMomentTriples C D V).card =
      ∑ a1 ∈ C,
        (residualLowHeightPlanePairFiber C D V a1).card ^ 2 := by
  classical
  let T := residualLineSecondMomentTriples C D V
  have hmaps : Set.MapsTo (fun triple => triple.2)
      (T : Set ((Fin X × Fin X) × Fin X)) (C : Set (Fin X)) := by
    intro triple htriple
    exact (mem_residualLineSecondMomentTriples.mp htriple).2.2.1
  have hdecomp := Finset.card_eq_sum_card_fiberwise hmaps
  calc
    (residualLineSecondMomentTriples C D V).card =
        ∑ a1 ∈ C,
          ((residualLineSecondMomentTriples C D V).filter fun triple =>
            triple.2 = a1).card := by
      simpa only [T] using hdecomp
    _ = ∑ a1 ∈ C,
        (residualLowHeightPlanePairFiber C D V a1).card ^ 2 := by
      apply Finset.sum_congr rfl
      intro a1 ha1
      exact card_fixedFirst_residualTriples_eq_fiber_sq C D V a1 ha1

/-- Finite Cauchy--Schwarz for one fixed second-coordinate class. -/
theorem card_residualLowHeightPlanePairsInClass_real_le_sqrt_mul_sqrt
    {X : Nat} (C D : Finset (Fin X)) (V : Real) :
    ((residualLowHeightPlanePairsInClass C D V).card : Real) <=
      Real.sqrt (C.card : Real) *
        Real.sqrt ((residualLineSecondMomentTriples C D V).card : Real) := by
  let F := residualLowHeightPlanePairFiber C D V
  have hpairs :=
    card_residualLowHeightPlanePairsInClass_eq_sum_card_fiber C D V
  have htriples :=
    card_residualLineSecondMomentTriples_eq_sum_sq_card_fiber C D V
  have hpairsReal :
      ((residualLowHeightPlanePairsInClass C D V).card : Real) =
        ∑ a1 ∈ C, ((F a1).card : Real) := by
    simpa only [Nat.cast_sum] using
      congrArg (fun n : Nat => (n : Real)) hpairs
  have htriplesReal :
      ((residualLineSecondMomentTriples C D V).card : Real) =
        ∑ a1 ∈ C, ((F a1).card : Real) ^ 2 := by
    simpa only [Nat.cast_sum, Nat.cast_pow] using
      congrArg (fun n : Nat => (n : Real)) htriples
  have hcauchy := Real.sum_mul_le_sqrt_mul_sqrt C
    (fun _a1 => (1 : Real)) (fun a1 => ((F a1).card : Real))
  calc
    ((residualLowHeightPlanePairsInClass C D V).card : Real) =
        ∑ a1 ∈ C, (1 : Real) * ((F a1).card : Real) := by
      simpa only [one_mul] using hpairsReal
    _ <= Real.sqrt (∑ a1 ∈ C, (1 : Real) ^ 2) *
        Real.sqrt (∑ a1 ∈ C, ((F a1).card : Real) ^ 2) := hcauchy
    _ = Real.sqrt (C.card : Real) *
        Real.sqrt ((residualLineSecondMomentTriples C D V).card : Real) := by
      rw [← htriplesReal]
      simp

end PrimesRestrictedDigits
