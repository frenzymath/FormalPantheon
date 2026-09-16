import PrimesRestrictedDigits.BasicEstimates.FiniteIntegralCover
import PrimesRestrictedDigits.BasicEstimates.RationalTetrahedronSubdivisionD918
/-! # RationalTetrahedronIntegralReplayD923 -/

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private theorem sum_get_eq_map_sum_D923
    {beta : Type*} (items : List beta) (g : beta → Real) :
    (∑ i : Fin items.length, g (items.get i)) = (items.map g).sum := by
  induction items with
  | nil => simp
  | cons item items ih =>
      simp [Fin.sum_univ_succ]

theorem RationalTetraSubdivision.setIntegral_le_replayWeightRat_of_retainedLeaves_cover
    {X : Type*} [MeasurableSpace X]
    {alpha : Type*}
    (mu : Measure X)
    (tree : RationalTetraSubdivision alpha) (root : RationalTetrahedron)
    (payloadWeight : RationalTetrahedron → alpha → Rat)
    (target : Set X)
    (cell : Fin (tree.retainedLeaves root).length → Set X)
    (f : X → Real)
    (htarget : MeasurableSet target)
    (hcellMeasurable : ∀ i, MeasurableSet (cell i))
    (hcellFinite : ∀ i, mu (cell i) ≠ ⊤)
    (hf : IntegrableOn f target mu)
    (hweightNonneg : ∀ i, 0 ≤ payloadWeight
      ((tree.retainedLeaves root).get i).1
      ((tree.retainedLeaves root).get i).2)
    (hcellVolume : ∀ i, mu.real (cell i) =
      (((tree.retainedLeaves root).get i).1.volumeRat : Real))
    (hcover : target ⊆ ⋃ i, cell i)
    (hbound : ∀ i, ∀ x ∈ target ∩ cell i, f x ≤
      (payloadWeight ((tree.retainedLeaves root).get i).1
        ((tree.retainedLeaves root).get i).2 : Real)) :
    (∫ x in target, f x ∂mu) ≤
      (tree.replayWeightRat root payloadWeight : Real) := by
  have hmajorant := setIntegral_le_finset_measureReal_mul_of_cover
    mu (Finset.univ : Finset (Fin (tree.retainedLeaves root).length))
    target cell f
    (fun i => (payloadWeight
      ((tree.retainedLeaves root).get i).1
      ((tree.retainedLeaves root).get i).2 : Real))
    htarget
    (by intro i hi; exact hcellMeasurable i)
    (by intro i hi; exact hcellFinite i)
    hf
    (by
      intro i hi
      exact (Rat.cast_nonneg (K := Real)).2 (hweightNonneg i))
    (by simpa using hcover)
    (by intro i hi x hx; exact hbound i x hx)
  calc
    (∫ x in target, f x ∂mu) ≤
        ∑ i ∈ (Finset.univ : Finset (Fin (tree.retainedLeaves root).length)),
          mu.real (cell i) *
            (payloadWeight
              ((tree.retainedLeaves root).get i).1
              ((tree.retainedLeaves root).get i).2 : Real) := hmajorant
    _ = ∑ i : Fin (tree.retainedLeaves root).length,
        ((((tree.retainedLeaves root).get i).1.volumeRat *
          payloadWeight
            ((tree.retainedLeaves root).get i).1
            ((tree.retainedLeaves root).get i).2 : Rat) : Real) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hcellVolume i, Rat.cast_mul]
    _ = ((tree.retainedLeaves root).map fun leaf =>
        ((leaf.1.volumeRat * payloadWeight leaf.1 leaf.2 : Rat) : Real)).sum :=
      sum_get_eq_map_sum_D923 (tree.retainedLeaves root)
        (fun leaf =>
          ((leaf.1.volumeRat * payloadWeight leaf.1 leaf.2 : Rat) : Real))
    _ = (tree.replayWeightRat root payloadWeight : Real) :=
      (tree.replayWeightRat_cast root payloadWeight).symm

end

end PrimesRestrictedDigits
