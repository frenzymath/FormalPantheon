import BoundedGaps.Maynard.ImprovedGPY.S2ActualError
import BoundedGaps.Maynard.ImprovedGPY.S2Multiplicity
import BoundedGaps.Maynard.ImprovedGPY.S2ModulusSquarefree

noncomputable section

/-!
# Modulus-dependent S2 fiber bounds

Maynard2013v3, in the error part of `lmm:S2Expression1` (source lines
363--365), groups supported divisor pairs by their CRT modulus.  This file
proves the elementary arithmetic containment needed for a modulus-dependent
fiber bound.  The source's sharper `tau_{3k}` estimate remains a separate
analytic/combinatorial obligation.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators
local instance fiberBoundDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem divisorTupleCoordinate_dvd_divisorPairModulus
    {H : Finset ℕ} {W : ℕ} {d e : H → ℕ} (h : H) :
    d h ∣ divisorPairModulus H W d e := by
  unfold divisorPairModulus
  have hlcm : d h ∣ divisorTupleLcm H d e h :=
    Nat.dvd_lcm_left _ _
  have hprod : divisorTupleLcm H d e h ∣
      ∏ j : H, divisorTupleLcm H d e j :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ h)
  exact dvd_mul_of_dvd_right (hlcm.trans hprod) W

theorem divisorTupleCoordinate_right_dvd_divisorPairModulus
    {H : Finset ℕ} {W : ℕ} {d e : H → ℕ} (h : H) :
    e h ∣ divisorPairModulus H W d e := by
  unfold divisorPairModulus
  have hlcm : e h ∣ divisorTupleLcm H d e h :=
    Nat.dvd_lcm_right _ _
  have hprod : divisorTupleLcm H d e h ∣
      ∏ j : H, divisorTupleLcm H d e j :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ h)
  exact dvd_mul_of_dvd_right (hlcm.trans hprod) W

theorem squarefree_of_mem_compatiblePairShiftModulus_image
    {H : Finset ℕ} {D : Finset (H → ℕ)} {R W m : ℕ}
    (hW : Squarefree W)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (hm : m ∈ (compatiblePairShiftIndex H D).image
      (compatiblePairShiftModulus H W)) :
    Squarefree m := by
  classical
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
  have hiData := compatiblePairShiftIndex_data hi
  exact squarefree_divisorPairModulus hW
    (hD i.1.1 hiData.1) (hD i.1.2 hiData.2.1) hiData.2.2.1

def divisorPairShiftContainer (H : Finset ℕ) (m : ℕ) :
    Finset (((H → ℕ) × (H → ℕ)) × H) :=
  ((Fintype.piFinset (fun _ : H => m.divisors) ×ˢ
      Fintype.piFinset (fun _ : H => m.divisors)).product Finset.univ)

theorem compatiblePairShiftIndex_fiber_subset_divisorPairShiftContainer
    {H : Finset ℕ} {D : Finset (H → ℕ)} {R W m : ℕ} (hW : 0 < W)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d) :
    (compatiblePairShiftIndex H D).filter
        (fun i => compatiblePairShiftModulus H W i = m) ⊆
      divisorPairShiftContainer H m := by
  classical
  intro i hi
  obtain ⟨hiIndex, hiMod⟩ := Finset.mem_filter.mp hi
  have hiData := compatiblePairShiftIndex_data hiIndex
  have hd : IsMaynardDivisorTuple H R W i.1.1 := hD i.1.1 hiData.1
  have he : IsMaynardDivisorTuple H R W i.1.2 := hD i.1.2 hiData.2.1
  have hm : m ≠ 0 := by
    rw [← hiMod]
    exact (divisorPairModulus_pos hW hd he).ne'
  have hdPi : i.1.1 ∈ Fintype.piFinset (fun _ : H => m.divisors) := by
    rw [Fintype.mem_piFinset]
    intro h
    apply Nat.mem_divisors.mpr
    refine ⟨?_, ?_⟩
    · rw [← hiMod]
      exact divisorTupleCoordinate_dvd_divisorPairModulus h
    · exact hm
  have hePi : i.1.2 ∈ Fintype.piFinset (fun _ : H => m.divisors) := by
    rw [Fintype.mem_piFinset]
    intro h
    apply Nat.mem_divisors.mpr
    refine ⟨?_, ?_⟩
    · rw [← hiMod]
      exact divisorTupleCoordinate_right_dvd_divisorPairModulus h
    · exact hm
  exact Finset.mem_product.mpr
    ⟨Finset.mem_product.mpr ⟨hdPi, hePi⟩, Finset.mem_univ _⟩

theorem modulusFiberCard_le_divisorPairShiftContainer_card
    {H : Finset ℕ} {D : Finset (H → ℕ)} {R W m : ℕ} (hW : 0 < W)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d) :
    modulusFiberCard (compatiblePairShiftIndex H D)
        (compatiblePairShiftModulus H W) m ≤
      (divisorPairShiftContainer H m).card := by
  unfold modulusFiberCard
  apply Finset.card_le_card
  exact compatiblePairShiftIndex_fiber_subset_divisorPairShiftContainer hW hD

theorem divisorPairShiftContainer_card
    (H : Finset ℕ) (m : ℕ) :
    (divisorPairShiftContainer H m).card =
      (m.divisors.card) ^ (2 * Fintype.card H) * Fintype.card H := by
  classical
  simp [divisorPairShiftContainer, Fintype.card_piFinset,
    Finset.card_product, Fintype.card_coe, ← pow_add, two_mul]

theorem modulusFiberCard_le_divisorPairShiftContainer_card_explicit
    {H : Finset ℕ} {D : Finset (H → ℕ)} {R W m : ℕ} (hW : 0 < W)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d) :
    modulusFiberCard (compatiblePairShiftIndex H D)
        (compatiblePairShiftModulus H W) m ≤
      (m.divisors.card) ^ (2 * Fintype.card H) * Fintype.card H := by
  exact (modulusFiberCard_le_divisorPairShiftContainer_card hW hD).trans_eq
    (divisorPairShiftContainer_card H m)

theorem sum_maxProgressionDiscrepancy_comp_le_divisorPairShiftContainer
    {H : Finset ℕ} {D : Finset (H → ℕ)} {R W : ℕ} (hW : 0 < W)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d) (x : ℕ) :
    (∑ i ∈ compatiblePairShiftIndex H D,
        maxProgressionDiscrepancy x (compatiblePairShiftModulus H W i)) ≤
      ∑ m ∈ (compatiblePairShiftIndex H D).image
          (compatiblePairShiftModulus H W),
        (divisorPairShiftContainer H m).card *
          maxProgressionDiscrepancy x m := by
  rw [sum_comp_eq_sum_modulusFiberCard]
  apply Finset.sum_le_sum
  intro m hm
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast modulusFiberCard_le_divisorPairShiftContainer_card hW hD
  · exact maxProgressionDiscrepancy_nonneg x m

end BoundedGaps.Maynard
