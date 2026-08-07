import Mathlib.NumberTheory.ArithmeticFunction.Moebius

import BoundedGaps.Maynard.ImprovedGPY.SquareWeights

/-!
# Arithmetic support of Maynard divisor tuples

Maynard2013v3, Section 5 (source lines 262--265), restricts the tuple product
to be below `R`, coprime to `W`, and squarefree.
-/

namespace BoundedGaps.Maynard

open scoped ArithmeticFunction.Moebius BigOperators

/-- Product of all divisor coordinates indexed by the finite shift set. -/
def divisorTupleProduct (H : Finset ℕ) (d : H → ℕ) : ℕ :=
  ∏ h : H, d h

/-- The exact cutoff, small-prime coprimality, and squarefree support from
Maynard2013v3, Section 5. -/
def IsMaynardDivisorTuple (H : Finset ℕ) (R W : ℕ) (d : H → ℕ) : Prop :=
  divisorTupleProduct H d < R ∧
    Nat.Coprime (divisorTupleProduct H d) W ∧
    Squarefree (divisorTupleProduct H d)

theorem squarefree_iff_moebius_sq_eq_one (n : ℕ) :
    Squarefree n ↔ ArithmeticFunction.moebius n ^ 2 = 1 := by
  rw [ArithmeticFunction.moebius_sq]
  by_cases h : Squarefree n <;> simp [h]

theorem isMaynardDivisorTuple_iff_moebius_sq
    (H : Finset ℕ) (R W : ℕ) (d : H → ℕ) :
    IsMaynardDivisorTuple H R W d ↔
      divisorTupleProduct H d < R ∧
        Nat.Coprime (divisorTupleProduct H d) W ∧
        ArithmeticFunction.moebius (divisorTupleProduct H d) ^ 2 = 1 := by
  simp only [IsMaynardDivisorTuple, squarefree_iff_moebius_sq_eq_one]

theorem divisorTupleCoordinate_dvd_product {H : Finset ℕ}
    (d : H → ℕ) (h : H) :
    d h ∣ divisorTupleProduct H d := by
  unfold divisorTupleProduct
  exact Finset.dvd_prod_of_mem d (Finset.mem_univ h)

private theorem two_divisorTupleCoordinates_mul_dvd_product
    {H : Finset ℕ} (d : H → ℕ) {a b : H} (hab : a ≠ b) :
    d a * d b ∣ divisorTupleProduct H d := by
  classical
  let s : Finset H := Finset.univ.erase a
  have hb : b ∈ s := by simp [s, Ne.symm hab]
  refine ⟨∏ h ∈ s.erase b, d h, ?_⟩
  unfold divisorTupleProduct
  rw [← Finset.prod_erase_mul Finset.univ d (Finset.mem_univ a)]
  rw [← Finset.prod_erase_mul s d hb]
  ring

theorem IsMaynardDivisorTuple.coordinate_coprime_W
    {H : Finset ℕ} {R W : ℕ} {d : H → ℕ}
    (hd : IsMaynardDivisorTuple H R W d) (h : H) :
    Nat.Coprime (d h) W :=
  Nat.Coprime.of_dvd_left (divisorTupleCoordinate_dvd_product d h) hd.2.1

theorem IsMaynardDivisorTuple.coordinate_squarefree
    {H : Finset ℕ} {R W : ℕ} {d : H → ℕ}
    (hd : IsMaynardDivisorTuple H R W d) (h : H) :
    Squarefree (d h) :=
  hd.2.2.squarefree_of_dvd (divisorTupleCoordinate_dvd_product d h)

theorem IsMaynardDivisorTuple.coordinates_coprime
    {H : Finset ℕ} {R W : ℕ} {d : H → ℕ}
    (hd : IsMaynardDivisorTuple H R W d) {a b : H} (hab : a ≠ b) :
    Nat.Coprime (d a) (d b) := by
  apply Nat.coprime_of_squarefree_mul
  exact hd.2.2.squarefree_of_dvd
    (two_divisorTupleCoordinates_mul_dvd_product d hab)

end BoundedGaps.Maynard
