import PrimesRestrictedDigits.BasicEstimates.FiniteIntegralCover
import PrimesRestrictedDigits.BasicEstimates.FiniteRationalSubdivision
/-! # FiniteRationalIntegralReplay -/

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private theorem sum_get_eq_map_sum
    {beta : Type*} (items : List beta) (g : beta → Real) :
    (∑ i : Fin items.length, g (items.get i)) = (items.map g).sum := by
  induction items with
  | nil => simp
  | cons item items ih =>
      simp [Fin.sum_univ_succ]

theorem RationalSubdivision.setIntegral_le_replayWeightRat_of_retainedLeaves_cover
    {n : Nat} {α X : Type*} [MeasurableSpace X]
    (μ : Measure X)
    (tree : RationalSubdivision n α) (box : RationalBox n)
    (payloadWeight : RationalBox n → α → Rat)
    (target : Set X)
    (cell : Fin (tree.retainedLeaves box).length → Set X)
    (f : X → Real)
    (htarget : MeasurableSet target)
    (hcellMeasurable : ∀ i, MeasurableSet (cell i))
    (hcellFinite : ∀ i, μ (cell i) ≠ ⊤)
    (hf : IntegrableOn f target μ)
    (hweightNonneg : ∀ i, 0 ≤ payloadWeight
      ((tree.retainedLeaves box).get i).1
      ((tree.retainedLeaves box).get i).2)
    (hcellVolume : ∀ i, μ.real (cell i) =
      (((tree.retainedLeaves box).get i).1.volumeRat : Real))
    (hcover : target ⊆ ⋃ i, cell i)
    (hbound : ∀ i, ∀ x ∈ target ∩ cell i, f x ≤
      (payloadWeight ((tree.retainedLeaves box).get i).1
        ((tree.retainedLeaves box).get i).2 : Real)) :
    (∫ x in target, f x ∂μ) ≤
      (tree.replayWeightRat box payloadWeight : Real) := by
  have hmajorant := setIntegral_le_finset_measureReal_mul_of_cover
    μ (Finset.univ : Finset (Fin (tree.retainedLeaves box).length))
    target cell f
    (fun i => (payloadWeight
      ((tree.retainedLeaves box).get i).1
      ((tree.retainedLeaves box).get i).2 : Real))
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
    (∫ x in target, f x ∂μ) ≤
        ∑ i ∈ (Finset.univ :
          Finset (Fin (tree.retainedLeaves box).length)),
          μ.real (cell i) *
            (payloadWeight
              ((tree.retainedLeaves box).get i).1
              ((tree.retainedLeaves box).get i).2 : Real) := hmajorant
    _ = ∑ i : Fin (tree.retainedLeaves box).length,
        ((((tree.retainedLeaves box).get i).1.volumeRat *
          payloadWeight
            ((tree.retainedLeaves box).get i).1
            ((tree.retainedLeaves box).get i).2 : Rat) : Real) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hcellVolume i, Rat.cast_mul]
    _ = ((tree.retainedLeaves box).map fun leaf =>
        ((leaf.1.volumeRat * payloadWeight leaf.1 leaf.2 : Rat) : Real)).sum :=
      sum_get_eq_map_sum (tree.retainedLeaves box)
        (fun leaf =>
          ((leaf.1.volumeRat * payloadWeight leaf.1 leaf.2 : Rat) : Real))
    _ = (tree.replayWeightRat box payloadWeight : Real) :=
      (tree.replayWeightRat_cast box payloadWeight).symm

end

end PrimesRestrictedDigits
