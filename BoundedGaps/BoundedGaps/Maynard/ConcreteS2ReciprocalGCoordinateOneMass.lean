import BoundedGaps.Maynard.ConcreteS2ReciprocalGShortBoundary
import BoundedGaps.Maynard.ConcreteFractionalTupleBox

noncomputable section

namespace BoundedGaps.Maynard

open scoped BigOperators

def engelsmaS2CoordinateOneReciprocalGMass
    (R D : ℕ) (m : BoundedGaps.engelsmaTuple) : ℝ :=
  ∑ r ∈ engelsmaS2CoordinateFiberCoordinateOneSupport R D m,
    1 / |∏ h : BoundedGaps.engelsmaTuple,
      (maynardS2G (r h) : ℝ)|

def engelsmaS2OffFaceReciprocalGMass
    (R D : ℕ) (m : BoundedGaps.engelsmaTuple) : ℝ :=
  ∑ u ∈ maynardDivisorTupleSupport
      (engelsmaOffFaceFinset m) R (primorial D),
    ∏ h : engelsmaOffFaceFinset m,
      maynardS2ReciprocalGSquarefreeAF (primorial D) (u h)

set_option maxRecDepth 8000 in
theorem engelsmaS2CoordinateOneReciprocalGMass_eq_offFace
    (R D : ℕ) (m : BoundedGaps.engelsmaTuple) :
    engelsmaS2CoordinateOneReciprocalGMass R D m =
      engelsmaS2OffFaceReciprocalGMass R D m := by
  classical
  unfold engelsmaS2CoordinateOneReciprocalGMass
    engelsmaS2OffFaceReciprocalGMass
  apply Finset.sum_bij (fun r _ => engelsmaOffFaceRestriction m r)
  · intro r hr
    have hrm := (Finset.mem_filter.mp hr).2
    exact (engelsmaOffFaceExtension_mem_maynardDivisorTupleSupport_iff
      R (primorial D) m (engelsmaOffFaceRestriction m r)).mp (by
        simpa [engelsmaOffFaceExtension_restriction m r hrm] using
          (Finset.mem_filter.mp hr).1)
  · intro r hr s hs hEq
    have hrm := (Finset.mem_filter.mp hr).2
    have hsm := (Finset.mem_filter.mp hs).2
    calc
      r = engelsmaOffFaceExtension m (engelsmaOffFaceRestriction m r) :=
        (engelsmaOffFaceExtension_restriction m r hrm).symm
      _ = engelsmaOffFaceExtension m (engelsmaOffFaceRestriction m s) := by
        rw [hEq]
      _ = s := engelsmaOffFaceExtension_restriction m s hsm
  · intro u hu
    let r := engelsmaOffFaceExtension m u
    have hr : r ∈ engelsmaS2CoordinateFiberCoordinateOneSupport R D m := by
      apply Finset.mem_filter.mpr
      exact ⟨(engelsmaOffFaceExtension_mem_maynardDivisorTupleSupport_iff
        R (primorial D) m u).mpr hu, engelsmaOffFaceExtension_at m u⟩
    refine ⟨r, hr, ?_⟩
    exact engelsmaOffFaceRestriction_extension m u
  · intro r hr
    have hrm := (Finset.mem_filter.mp hr).2
    have hu := (engelsmaOffFaceExtension_restriction m r hrm)
    have hweight := reciprocalG_full_weight_eq_offFace_product m
      ((engelsmaOffFaceExtension_mem_maynardDivisorTupleSupport_iff
        R (primorial D) m (engelsmaOffFaceRestriction m r)).mp (by
          simpa [hu] using (Finset.mem_filter.mp hr).1))
    rw [← hu]
    rw [engelsmaOffFaceRestriction_extension]
    exact hweight

set_option maxRecDepth 8000 in
theorem engelsmaS2OffFaceReciprocalGMass_le_box
    (R D : ℕ) (m : BoundedGaps.engelsmaTuple) :
    engelsmaS2OffFaceReciprocalGMass R D m ≤
      ∏ _h : engelsmaOffFaceFinset m,
        maynardS2ReciprocalGSquarefreeMean (primorial D) R := by
  classical
  unfold engelsmaS2OffFaceReciprocalGMass
  let H := engelsmaOffFaceFinset m
  let W := primorial D
  let Q := fun _ : H => R
  let box := squarefreeCoprimeTupleBox H W Q
  have hsubset : maynardDivisorTupleSupport H R W ⊆ box := by
    intro u hu
    change u ∈ squarefreeCoprimeTupleBox H W Q
    rw [squarefreeCoprimeTupleBox, Fintype.mem_piFinset]
    intro h
    apply Finset.mem_filter.mpr
    have huSupport := isMaynardDivisorTuple_of_mem_support hu
    have huBox := huSupport.mem_maynardDivisorTupleBox
    have huBounds := (mem_maynardDivisorTupleBox_iff.mp huBox) h
    exact ⟨Finset.mem_Icc.mpr ⟨huBounds.1, huBounds.2.le⟩,
      ⟨huSupport.coordinate_squarefree h,
        huSupport.coordinate_coprime_W h⟩⟩
  let f : (H → ℕ) → ℝ := fun u =>
    ∏ h : H, maynardS2ReciprocalGSquarefreeAF W (u h)
  have hsum : (∑ u ∈ maynardDivisorTupleSupport H R W, f u) ≤
      ∑ u ∈ box, f u := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro u hu hnot
    dsimp [f]
    exact Finset.prod_nonneg (fun h hh =>
      maynardS2ReciprocalGSquarefreeAF_nonneg W (u h))
  calc
    (∑ u ∈ maynardDivisorTupleSupport H R W,
        ∏ h : H, maynardS2ReciprocalGSquarefreeAF W (u h)) ≤
        ∑ u ∈ box, ∏ h : H, maynardS2ReciprocalGSquarefreeAF W (u h) := by
          simpa [f] using hsum
    _ = ∏ h : H, ∑ n ∈ squarefreeCoprimeCoordinateSupport W R,
        maynardS2ReciprocalGSquarefreeAF W n := by
      change (∑ u ∈ squarefreeCoprimeTupleBox H W Q,
        ∏ h : H, maynardS2ReciprocalGSquarefreeAF W (u h)) = _
      exact (Finset.prod_univ_sum
        (fun _ : H => squarefreeCoprimeCoordinateSupport W R)
        (fun _ : H => fun n => maynardS2ReciprocalGSquarefreeAF W n)).symm
    _ = ∏ h : H, maynardS2ReciprocalGSquarefreeMean W R := by
      apply Finset.prod_congr rfl
      intro h hh
      exact maynardS2ReciprocalGSquarefreeCoordinateSupport_sum_eq_mean W R

end BoundedGaps.Maynard
