import PrimesRestrictedDigits.MajorArcs.Factorization
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Stable labelled factorisation for the strict Type II transfer

The residual cofactor is expanded with Mathlib's canonical prime-factor list. The outer tuple
is put first before `Tuple.sort`; the sorting permutation is retained so equal prime values
have deterministic outer-before-residual labels.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The labelled concatenation of the outer tuple and residual prime factors. -/
def typeIICombinedLabeledFactors {ell : Nat} (outer : Fin ell → Nat) (m : Nat) :
    Fin (ell + m.primeFactorsList.length) → Nat :=
  Fin.append outer (fun i => m.primeFactorsList.get i)

/-- The permutation supplied by the stable lexicographic tuple sort. -/
def typeIIStableFactorPermutation {ell : Nat} (outer : Fin ell → Nat) (m : Nat) :
    Equiv.Perm (Fin (ell + m.primeFactorsList.length)) :=
  Tuple.sort (typeIICombinedLabeledFactors outer m)

/-- The weakly increasing tuple of labelled factors. -/
def typeIIStableFactorTuple {ell : Nat} (outer : Fin ell → Nat) (m : Nat) :
    Fin (ell + m.primeFactorsList.length) → Nat :=
  typeIICombinedLabeledFactors outer m ∘ typeIIStableFactorPermutation outer m

def typeIIStableOuterPositionEmbedding {ell : Nat}
    (outer : Fin ell → Nat) (m : Nat) :
    Fin ell ↪ Fin (ell + m.primeFactorsList.length) := by
  let k := m.primeFactorsList.length
  let σ := typeIIStableFactorPermutation outer m
  exact
    { toFun := fun i => σ.symm (Fin.castAdd k i)
      inj' := by
        intro i j hij
        apply Fin.ext
        have h := congrArg σ hij
        exact congrArg Fin.val (by simpa using h) }

/-- Sorted positions occupied by a selected set of original outer labels. -/
noncomputable def typeIIStableOuterPositions {ell : Nat}
    (outer : Fin ell → Nat) (m : Nat) (I : Finset (Fin ell)) :
    Finset (Fin (ell + m.primeFactorsList.length)) :=
  I.map (typeIIStableOuterPositionEmbedding outer m)

theorem monotone_typeIIStableFactorTuple {ell : Nat}
    (outer : Fin ell → Nat) (m : Nat) :
    Monotone (typeIIStableFactorTuple outer m) := by
  exact Tuple.monotone_sort (typeIICombinedLabeledFactors outer m)

theorem typeIIStableFactorPermutation_tie {ell : Nat}
    (outer : Fin ell → Nat) (m : Nat)
    {i j : Fin (ell + m.primeFactorsList.length)}
    (hij : i < j)
    (heq : typeIICombinedLabeledFactors outer m
        ((typeIIStableFactorPermutation outer m) i) =
      typeIICombinedLabeledFactors outer m
        ((typeIIStableFactorPermutation outer m) j)) :
    (typeIIStableFactorPermutation outer m) i <
      (typeIIStableFactorPermutation outer m) j := by
  exact (Tuple.eq_sort_iff.mp rfl).2 i j hij heq

theorem typeIIStableFactorTuple_at_outerPosition {ell : Nat}
    (outer : Fin ell → Nat) (m : Nat) (i : Fin ell) :
    typeIIStableFactorTuple outer m
        ((typeIIStableFactorPermutation outer m).symm
          (Fin.castAdd m.primeFactorsList.length i)) = outer i := by
  simp [typeIIStableFactorTuple, typeIICombinedLabeledFactors,
    Function.comp_apply]

theorem typeIIStableOuterPosition_lt_residualPosition_of_eq {ell : Nat}
    (outer : Fin ell → Nat) (m : Nat) {i : Fin ell}
    {j : Fin m.primeFactorsList.length}
    (heq : typeIIStableFactorTuple outer m
        ((typeIIStableFactorPermutation outer m).symm
          (Fin.castAdd m.primeFactorsList.length i)) =
      typeIIStableFactorTuple outer m
        ((typeIIStableFactorPermutation outer m).symm
          (Fin.natAdd ell j))) :
    (typeIIStableFactorPermutation outer m).symm
        (Fin.castAdd m.primeFactorsList.length i) <
      (typeIIStableFactorPermutation outer m).symm (Fin.natAdd ell j) := by
  let σ := typeIIStableFactorPermutation outer m
  let a := σ.symm (Fin.castAdd m.primeFactorsList.length i)
  let b := σ.symm (Fin.natAdd ell j)
  have huv : (Fin.castAdd m.primeFactorsList.length i : Nat) <
      (Fin.natAdd ell j : Nat) := by
    simp only [Fin.val_castAdd, Fin.val_natAdd]
    omega
  have hab : a ≠ b := by
    intro hab
    have hlabels : (Fin.castAdd m.primeFactorsList.length i) =
        (Fin.natAdd ell j) := by
      exact σ.symm.injective hab
    exact (Nat.ne_of_lt huv) (congrArg Fin.val hlabels)
  have hraweq : typeIICombinedLabeledFactors outer m (σ a) =
      typeIICombinedLabeledFactors outer m (σ b) := by
    simpa [a, b, σ, typeIIStableFactorTuple, Function.comp_apply] using heq
  rcases lt_or_gt_of_ne hab with hablt | hblt
  · exact hablt
  · exfalso
    have hsource := typeIIStableFactorPermutation_tie outer m hblt hraweq.symm
    have hsourceVal : (σ b : Nat) < (σ a : Nat) := hsource
    have houterResidual : (σ a : Nat) < (σ b : Nat) := by
      simpa [a, b] using huv
    exact (Nat.not_lt_of_ge houterResidual.le) hsourceVal

theorem card_typeIIStableOuterPositions {ell : Nat}
    (outer : Fin ell → Nat) (m : Nat) (I : Finset (Fin ell)) :
    (typeIIStableOuterPositions outer m I).card = I.card := by
  exact Finset.card_map _

theorem prod_typeIIStableOuterPositions {ell : Nat}
    (outer : Fin ell → Nat) (m : Nat) (I : Finset (Fin ell)) :
    ∏ j ∈ typeIIStableOuterPositions outer m I,
        typeIIStableFactorTuple outer m j = ∏ i ∈ I, outer i := by
  classical
  change (I.map (typeIIStableOuterPositionEmbedding outer m)).prod
      (typeIIStableFactorTuple outer m) = I.prod outer
  rw [Finset.prod_map]
  apply Finset.prod_congr rfl
  intro i hi
  exact typeIIStableFactorTuple_at_outerPosition outer m i

theorem prime_typeIIStableFactorTuple {ell : Nat}
    (outer : Fin ell → Nat) (m : Nat)
    (houter : ∀ i, (outer i).Prime) :
    ∀ j, (typeIIStableFactorTuple outer m j).Prime := by
  intro j
  let σ := typeIIStableFactorPermutation outer m
  have hraw : (typeIICombinedLabeledFactors outer m (σ j)).Prime := by
    refine Fin.addCases (fun i => ?_) (fun r => ?_) (σ j)
    · simpa [typeIICombinedLabeledFactors] using houter i
    · simpa only [typeIICombinedLabeledFactors, Fin.append_right] using
        Nat.prime_of_mem_primeFactorsList (List.get_mem _ r)
  exact hraw

theorem primeTupleProduct_typeIIStableFactorTuple {ell : Nat}
    (outer : Fin ell → Nat) (m : Nat)
    (hm : m ≠ 0) :
    primeTupleProduct (typeIIStableFactorTuple outer m) =
      primeTupleProduct outer * m := by
  let raw := typeIICombinedLabeledFactors outer m
  let σ := typeIIStableFactorPermutation outer m
  rw [primeTupleProduct]
  calc
    (∏ i, typeIIStableFactorTuple outer m i) =
        ∏ i, raw (σ i) := by rfl
    _ = ∏ i, raw i := Equiv.prod_comp σ raw
    _ = (∏ i : Fin ell, raw (Fin.castAdd m.primeFactorsList.length i)) *
        ∏ j : Fin m.primeFactorsList.length, raw (Fin.natAdd ell j) :=
      Fin.prod_univ_add raw
    _ = primeTupleProduct outer * m := by
      have houterprod : (∏ i : Fin ell,
          raw (Fin.castAdd m.primeFactorsList.length i)) =
          primeTupleProduct outer := by
        apply Finset.prod_congr rfl
        intro i hi
        simp [raw, typeIICombinedLabeledFactors]
      have hresprod : (∏ j : Fin m.primeFactorsList.length,
          raw (Fin.natAdd ell j)) = m := by
        calc
          (∏ j : Fin m.primeFactorsList.length,
              raw (Fin.natAdd ell j)) =
              ∏ j : Fin m.primeFactorsList.length,
                m.primeFactorsList.get j := by
            apply Finset.prod_congr rfl
            intro j hj
            simp [raw, typeIICombinedLabeledFactors]
          _ = (List.ofFn m.primeFactorsList.get).prod :=
            (List.prod_ofFn (f := m.primeFactorsList.get)).symm
          _ = m.primeFactorsList.prod := by rw [List.ofFn_get]
          _ = m := Nat.prod_primeFactorsList hm
      rw [houterprod, hresprod]

end

end PrimesRestrictedDigits
