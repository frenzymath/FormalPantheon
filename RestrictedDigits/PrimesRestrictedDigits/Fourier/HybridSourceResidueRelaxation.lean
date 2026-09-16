import PrimesRestrictedDigits.Fourier.HybridSourceResidueReindex

/-!
# Relaxing the third mixed-radix coordinate

The source drops the full `b3` gcd condition before estimating the two
remaining residue fibers.  This file records that step as an exact finite-set
inclusion and a nonnegative sum inequality.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

def hybridFullReducedCarrier (d₁ d₂ d₃ : Nat) :
    Finset ((Fin d₁ × Fin d₂) × Fin d₃) :=
  Finset.univ.filter (fun x =>
    (mixedRadixTripleEquiv d₁ d₂ d₃ x).val.Coprime (d₁ * d₂ * d₃))

def hybridPairReducedCarrier (d₁ d₂ : Nat) : Finset (Fin d₁ × Fin d₂) :=
  Finset.univ.filter (fun x =>
    (lowHighFinEquiv d₁ d₂ x).val.Coprime (d₁ * d₂))

theorem hybridFullReduced_implies_pairReduced
    {d₁ d₂ d₃ : Nat} {b₁ : Fin d₁} {b₂ : Fin d₂} {b₃ : Fin d₃}
    (hfull :
      (mixedRadixTripleEquiv d₁ d₂ d₃ ((b₁, b₂), b₃)).val.Coprime
        (d₁ * d₂ * d₃)) :
    (lowHighFinEquiv d₁ d₂ (b₁, b₂)).val.Coprime (d₁ * d₂) := by
  let n := d₁ * d₂
  let full := (mixedRadixTripleEquiv d₁ d₂ d₃ ((b₁, b₂), b₃)).val
  let pair := (lowHighFinEquiv d₁ d₂ (b₁, b₂)).val
  have hzero : n * b₃.val ≡ 0 [MOD n] :=
    Nat.modEq_zero_iff_dvd.mpr (Nat.dvd_mul_right n b₃.val)
  have hmod : full ≡ pair [MOD n] := by
    have hadd := (Nat.ModEq.refl (n := n) pair).add hzero
    simpa [full, pair, n, mixedRadixTripleEquiv_val,
      lowHighFinEquiv_val, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hadd
  have hcop : full.Coprime n := by
    apply hfull.coprime_dvd_right
    exact ⟨d₃, by simp [n, Nat.mul_assoc]⟩
  apply Nat.coprime_iff_gcd_eq_one.mpr
  rw [← hmod.gcd_eq]
  exact hcop.gcd_eq_one

theorem hybridFullReducedCarrier_subset_pairProduct
    (d₁ d₂ d₃ : Nat) :
    hybridFullReducedCarrier d₁ d₂ d₃ ⊆
      hybridPairReducedCarrier d₁ d₂ ×ˢ (Finset.univ : Finset (Fin d₃)) := by
  intro x hx
  have hfull := (Finset.mem_filter.mp hx).2
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Finset.mem_univ _⟩
  exact hybridFullReduced_implies_pairReduced hfull

theorem sum_hybridFullReducedCarrier_le_sum_pairProduct
    {d₁ d₂ d₃ : Nat} (f : ((Fin d₁ × Fin d₂) × Fin d₃) → Real)
    (hf : ∀ x, 0 ≤ f x) :
    (∑ x ∈ hybridFullReducedCarrier d₁ d₂ d₃, f x) ≤
      (∑ x ∈ hybridPairReducedCarrier d₁ d₂ ×ˢ
        (Finset.univ : Finset (Fin d₃)), f x) := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (hybridFullReducedCarrier_subset_pairProduct d₁ d₂ d₃)
  intro x _ _
  exact hf x

end PrimesRestrictedDigits
