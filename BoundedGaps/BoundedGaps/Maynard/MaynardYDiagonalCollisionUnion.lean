import BoundedGaps.Maynard.MaynardYDiagonalCollisionWeight

noncomputable section

namespace BoundedGaps.Maynard

open scoped BigOperators

/-! Cover collision tuples by ordered coordinate-pair/shared-prime supports. -/

theorem sum_biUnion_le_sum
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : α → Finset β) (f : β → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    (∑ y ∈ s.biUnion t, f y) ≤
      ∑ x ∈ s, ∑ y ∈ t x, f y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hinter : 0 ≤ ∑ y ∈ t a ∩ s.biUnion t, f y := by
        exact Finset.sum_nonneg fun y hy => hf y
      have hunion := Finset.sum_union_inter
        (s₁ := t a) (s₂ := s.biUnion t) (f := f)
      have hle : (∑ y ∈ t a ∪ s.biUnion t, f y) ≤
          (∑ y ∈ t a, f y) + ∑ y ∈ s.biUnion t, f y := by
        linarith
      rw [Finset.biUnion_insert]
      calc
        (∑ y ∈ t a ∪ s.biUnion t, f y) ≤
            (∑ y ∈ t a, f y) + ∑ y ∈ s.biUnion t, f y := hle
        _ ≤ (∑ y ∈ t a, f y) +
            ∑ x ∈ s, ∑ y ∈ t x, f y :=
          by linarith [add_le_add_left ih (∑ y ∈ t a, f y)]
        _ = ∑ x ∈ insert a s, ∑ y ∈ t x, f y := by
          rw [Finset.sum_insert ha]

def collisionPairPrimeIndex (H : Finset ℕ) (D R : ℕ) :
    Finset ((H × H) × ℕ) :=
  offDiagonalPairs H ×ˢ roughPrimeSupport D R

def collisionPairPrimeTupleSupport
    (H : Finset ℕ) (R W : ℕ) (x : (H × H) × ℕ) :
    Finset (H → ℕ) :=
  (preSievedSimplexTupleSupport H R W).filter fun u =>
    x.2 ∣ u x.1.1 ∧ x.2 ∣ u x.1.2

def collisionPairPrimeTupleUnion
    (H : Finset ℕ) (R D : ℕ) : Finset (H → ℕ) :=
  (collisionPairPrimeIndex H D R).biUnion fun x =>
    collisionPairPrimeTupleSupport H R (primorial D) x

theorem collisionSupport_subset_pairPrimeUnion
    (H : Finset ℕ) (R D : ℕ) :
    preSievedSimplexCollisionSupport H R (primorial D) ⊆
      collisionPairPrimeTupleUnion H R D := by
  classical
  intro u hu
  have huData := Finset.mem_filter.mp hu
  have huIndependent := huData.1
  have huNot : u ∉ maynardDivisorTupleSupport H R (primorial D) := by
    intro huMaynard
    exact huData.2 (isMaynardDivisorTuple_of_mem_support huMaynard).2.2
  obtain ⟨a, b, p, hab, hp, hpGt, hpa, hpb⟩ :=
    exists_shared_prime_gt_of_independent_not_maynard huIndependent huNot
  have hcoordPos := (preSievedSimplexTupleSupport_coordinate huIndependent a).1
  have hprodPos : 0 < divisorTupleProduct H u := by
    unfold divisorTupleProduct
    apply Finset.prod_pos
    intro h hh
    exact (preSievedSimplexTupleSupport_coordinate huIndependent h).1
  have hpLeCoord : p ≤ u a := Nat.le_of_dvd hcoordPos hpa
  have hcoordLeProd : u a ≤ divisorTupleProduct H u :=
    Nat.le_of_dvd hprodPos (divisorTupleCoordinate_dvd_product u a)
  have hpLeR : p ≤ R :=
    (hpLeCoord.trans hcoordLeProd).trans
      (mem_preSievedSimplexTupleSupport_iff.mp huIndependent).2.le
  have habMem : (a, b) ∈ offDiagonalPairs H := by
    rw [offDiagonalPairs, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hab⟩
  have hpMem : p ∈ roughPrimeSupport D R := by
    rw [roughPrimeSupport, Finset.mem_filter]
    exact ⟨Finset.mem_Icc.mpr ⟨by omega, hpLeR⟩, hp⟩
  rw [collisionPairPrimeTupleUnion, Finset.mem_biUnion]
  refine ⟨((a, b), p), Finset.mem_product.mpr ⟨habMem, hpMem⟩, ?_⟩
  rw [collisionPairPrimeTupleSupport, Finset.mem_filter]
  exact ⟨huIndependent, hpa, hpb⟩

theorem collisionWeightSum_le_pairPrimeSum
    (H : Finset ℕ) (R D : ℕ) :
    (∑ u ∈ preSievedSimplexCollisionSupport H R (primorial D),
      reciprocalTotientTupleWeight H u) ≤
      ∑ x ∈ collisionPairPrimeIndex H D R,
        ∑ u ∈ collisionPairPrimeTupleSupport H R (primorial D) x,
          reciprocalTotientTupleWeight H u := by
  calc
    (∑ u ∈ preSievedSimplexCollisionSupport H R (primorial D),
      reciprocalTotientTupleWeight H u) ≤
        ∑ u ∈ collisionPairPrimeTupleUnion H R D,
          reciprocalTotientTupleWeight H u := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (collisionSupport_subset_pairPrimeUnion H R D)
      intro u hu huNot
      unfold reciprocalTotientTupleWeight
      positivity
    _ ≤ ∑ x ∈ collisionPairPrimeIndex H D R,
        ∑ u ∈ collisionPairPrimeTupleSupport H R (primorial D) x,
          reciprocalTotientTupleWeight H u := by
      unfold collisionPairPrimeTupleUnion
      exact sum_biUnion_le_sum _ _ _ (fun u => by
        unfold reciprocalTotientTupleWeight
        positivity)

end BoundedGaps.Maynard
