import PrimesRestrictedDigits.SieveDecomposition.BuchstabIdentity

/-!
# Repeated-prime correction for Buchstab fibers

This exposes the square correction omitted by the strict-fiber recurrences in
`MAYNARD-PRD-PUBLISHED`, Section 6.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- A weak least-`p` fiber is the disjoint sum of the strict cofactor fiber
and the weak fiber remaining after extracting a second copy of `p`. -/
theorem sum_weakPrimeThresholdFiber_eq_strict_add_repeatedDilation
    {M : Type*} [AddCommMonoid M]
    (C : Finset Nat) {p : Nat} (hp : p.Prime) (w : Nat -> M) :
    (∑ n ∈ weakPrimeThresholdFiber C p, w n) =
      (∑ m ∈ strictSiftedCarrier
          (sieveDilation C ⟨p, hp.pos⟩) (p : Real), w (m * p)) +
        ∑ k ∈ weakSiftedCarrier
          (sieveDilation
            (sieveDilation C ⟨p, hp.pos⟩) ⟨p, hp.pos⟩) (p : Real),
          w ((k * p) * p) := by
  let Cp := sieveDilation C ⟨p, hp.pos⟩
  have hsubset :
      strictSiftedCarrier Cp (p : Real) ⊆
        weakSiftedCarrier Cp (p : Real) :=
    strictSiftedCarrier_subset_weakSiftedCarrier Cp (p : Real)
  calc
    (∑ n ∈ weakPrimeThresholdFiber C p, w n) =
        ∑ m ∈ weakSiftedCarrier Cp (p : Real), w (m * p) := by
      simpa only [Cp] using sum_weakPrimeThresholdFiber_eq_dilation C hp w
    _ = ∑ m ∈ strictSiftedCarrier Cp (p : Real) ∪
          (weakSiftedCarrier Cp (p : Real) \
            strictSiftedCarrier Cp (p : Real)), w (m * p) := by
      rw [Finset.union_sdiff_of_subset hsubset]
    _ = (∑ m ∈ strictSiftedCarrier Cp (p : Real), w (m * p)) +
          ∑ m ∈ weakPrimeThresholdFiber Cp p, w (m * p) := by
      rw [Finset.sum_union Finset.disjoint_sdiff]
      rfl
    _ = (∑ m ∈ strictSiftedCarrier Cp (p : Real), w (m * p)) +
          ∑ k ∈ weakSiftedCarrier
            (sieveDilation Cp ⟨p, hp.pos⟩) (p : Real),
            w ((k * p) * p) := by
      rw [sum_weakPrimeThresholdFiber_eq_dilation Cp hp (fun m => w (m * p))]
    _ = _ := by rfl

end PrimesRestrictedDigits
