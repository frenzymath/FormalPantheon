import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

/-!
# Finite weighted injective reindexing

This elementary helper records the exact combinatorial principle used by the fixed-cell maps
in the repaired Lemma 14.3 proof. It introduces no representation multiplicity.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

/-- An injective map from a finite source into a nonnegative finite target
bounds the source sum when it preserves every weight. -/
theorem finset_sum_le_fintype_sum_of_injective
    {alpha beta : Type*} [Fintype beta]
    (source : Finset alpha) (sourceWeight : alpha -> Real)
    (targetWeight : beta -> Real)
    (reindex : {x // x ∈ source} -> beta)
    (hinjective : Function.Injective reindex)
    (hweight : ∀ x : {x // x ∈ source},
      sourceWeight x.val = targetWeight (reindex x))
    (htargetNonneg : ∀ y : beta, 0 <= targetWeight y) :
    (∑ x ∈ source, sourceWeight x) <= ∑ y : beta, targetWeight y := by
  classical
  calc
    (∑ x ∈ source, sourceWeight x) =
        ∑ x : {x // x ∈ source}, sourceWeight x.val :=
      Finset.sum_subtype source (fun _ => Iff.rfl) sourceWeight
    _ = ∑ x : {x // x ∈ source}, targetWeight (reindex x) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hweight x
    _ = ∑ y ∈ (Finset.univ.image reindex), targetWeight y := by
      exact (Finset.sum_image (s := Finset.univ)
        (Set.injOn_of_injective hinjective)).symm
    _ <= ∑ y : beta, targetWeight y :=
      Finset.sum_le_univ_sum_of_nonneg htargetNonneg

/-- Fintype-source specialization of the finite weighted injection lemma. -/
theorem fintype_sum_le_fintype_sum_of_injective
    {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    (sourceWeight : alpha -> Real) (targetWeight : beta -> Real)
    (reindex : alpha -> beta) (hinjective : Function.Injective reindex)
    (hweight : ∀ x : alpha, sourceWeight x = targetWeight (reindex x))
    (htargetNonneg : ∀ y : beta, 0 <= targetWeight y) :
    (∑ x : alpha, sourceWeight x) <= ∑ y : beta, targetWeight y := by
  classical
  let attachedReindex : {x // x ∈ (Finset.univ : Finset alpha)} -> beta :=
    fun x => reindex x.val
  have hattachedInjective : Function.Injective attachedReindex := by
    intro x y hxy
    apply Subtype.ext
    exact hinjective hxy
  simpa using
    finset_sum_le_fintype_sum_of_injective (Finset.univ : Finset alpha)
      sourceWeight targetWeight attachedReindex hattachedInjective
      (fun x => hweight x.val) htargetNonneg

end PrimesRestrictedDigits
