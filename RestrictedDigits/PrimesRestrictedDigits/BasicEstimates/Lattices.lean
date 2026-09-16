import Mathlib.Data.Int.Interval
import Mathlib.Data.Pi.Interval
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Tactic.Ring

/-!
# Elementary lattice-coordinate counting

This isolates the exact coefficient-box count in `MAYNARD-PRD-PUBLISHED`,
Lemma 13.2 proof, p. 194. Reduced-basis existence and norm/determinant
comparisons remain separate inputs.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

variable {ι M : Type*} [Fintype ι] [AddCommGroup M] [Module ℤ M]

theorem card_le_prod_two_mul_add_one_of_basis_repr_le
    (b : Module.Basis ι ℤ M) (R : ι → ℕ) (s : Finset M)
    (hs : ∀ x ∈ s, ∀ i, |b.repr x i| ≤ (R i : ℤ)) :
    s.card ≤ ∏ i, (2 * R i + 1) := by
  classical
  let coordinates : M → ι → ℤ := fun x => b.equivFun x
  let box : Finset (ι → ℤ) :=
    Fintype.piFinset fun i => Finset.Icc (-(R i : ℤ)) (R i : ℤ)
  have hcoordinates : Function.Injective coordinates := b.equivFun.injective
  have himage : s.image coordinates ⊆ box := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    simpa [coordinates, abs_le] using hs x hx i
  calc
    s.card = (s.image coordinates).card :=
      (Finset.card_image_of_injective s hcoordinates).symm
    _ ≤ box.card := Finset.card_le_card himage
    _ = ∏ i, (2 * R i + 1) := by
      rw [show box.card =
          ∏ i, (Finset.Icc (-(R i : ℤ)) (R i : ℤ)).card by
        simp [box]]
      apply Finset.prod_congr rfl
      intro i _
      rw [Int.card_Icc]
      have hcast :
          (R i : ℤ) + 1 + (R i : ℤ) = ((2 * R i + 1 : ℕ) : ℤ) := by
        push_cast
        ring
      rw [sub_neg_eq_add, hcast, Int.toNat_natCast]

end PrimesRestrictedDigits
