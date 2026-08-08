import Waring.Analytic.ChenSevenResidue

/-!
# Positive residue representatives in Chen's Lemma 7

This file reindexes one residue-class contribution from the interval
`1, ..., P` by its unique progression `r + q * k`, where the zero residue
uses the positive representative `r = q`.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Waring.Analytic

open scoped BigOperators ComplexConjugate

/-- The representative of `y : ZMod q` in the interval `1, ..., q`. -/
def positiveResidueRepresentative
    (q : Nat) [NeZero q] (y : ZMod q) : Nat :=
  if y = 0 then q else y.val

@[simp] theorem positiveResidueRepresentative_zero
    (q : Nat) [NeZero q] :
    positiveResidueRepresentative q (0 : ZMod q) = q := by
  simp [positiveResidueRepresentative]

/-- The positive representative is at least one. -/
theorem positiveResidueRepresentative_pos
    (q : Nat) [NeZero q] (y : ZMod q) :
    0 < positiveResidueRepresentative q y := by
  by_cases hy : y = 0
  · simp [positiveResidueRepresentative, hy,
      Nat.pos_of_ne_zero (NeZero.ne q)]
  · have hyVal : y.val ≠ 0 := by
      intro hyVal
      apply hy
      rw [← ZMod.natCast_zmod_val y, hyVal]
      simp
    simp [positiveResidueRepresentative, hy, Nat.pos_of_ne_zero hyVal]

/-- The positive representative is at most the modulus. -/
theorem positiveResidueRepresentative_le
    (q : Nat) [NeZero q] (y : ZMod q) :
    positiveResidueRepresentative q y ≤ q := by
  by_cases hy : y = 0
  · simp [positiveResidueRepresentative, hy]
  · simpa [positiveResidueRepresentative, hy] using Nat.le_of_lt y.val_lt

/-- Casting the positive representative recovers the original residue. -/
@[simp] theorem positiveResidueRepresentative_cast
    (q : Nat) [NeZero q] (y : ZMod q) :
    ((positiveResidueRepresentative q y : Nat) : ZMod q) = y := by
  by_cases hy : y = 0
  · simp [positiveResidueRepresentative, hy]
  · simp [positiveResidueRepresentative, hy]

/-- Positive natural representatives of `y` are exactly `r + q * k`. -/
theorem natCast_eq_residue_iff_eq_positiveRepresentative_add_mul
    (q x : Nat) [NeZero q] (y : ZMod q) (hx : 0 < x) :
    ((x : Nat) : ZMod q) = y ↔
      ∃ k : Nat,
        x = positiveResidueRepresentative q y + q * k := by
  let r := positiveResidueRepresentative q y
  have hrLe : r ≤ q := positiveResidueRepresentative_le q y
  have hrCast : ((r : Nat) : ZMod q) = y :=
    positiveResidueRepresentative_cast q y
  constructor
  · intro hxy
    have hmod : x ≡ r [MOD q] :=
      (ZMod.natCast_eq_natCast_iff x r q).mp (hxy.trans hrCast.symm)
    have hrx : r ≤ x := by
      by_cases hrq : r = q
      · have hrmod : r ≡ 0 [MOD q] := by
          rw [hrq]
          exact dvd_rfl.modEq_zero_nat
        have hdiv : q ∣ x :=
          Nat.modEq_zero_iff_dvd.mp (hmod.trans hrmod)
        simpa [hrq] using Nat.le_of_dvd hx hdiv
      · have hrLt : r < q := lt_of_le_of_ne hrLe hrq
        have hmodEq : x % q = r := by
          change x % q = r % q at hmod
          rwa [Nat.mod_eq_of_lt hrLt] at hmod
        rw [← hmodEq]
        exact Nat.mod_le x q
    have hdiv : q ∣ x - r :=
      (Nat.modEq_iff_dvd' hrx).mp hmod.symm
    obtain ⟨k, hk⟩ := hdiv
    exact ⟨k, by omega⟩
  · rintro ⟨k, rfl⟩
    calc
      (((r + q * k : Nat) : Nat) : ZMod q) = (r : ZMod q) := by
        push_cast
        simp
      _ = y := hrCast

/-- Naturals in `1, ..., P` that represent `y : ZMod q`. -/
def positiveResidueFinset
    (q : Nat) [NeZero q] (P : Nat) (y : ZMod q) : Finset Nat :=
  (Finset.Icc 1 P).filter (fun x => ((x : Nat) : ZMod q) = y)

/-- The progression endpoint is equivalent to membership in its index range. -/
theorem mem_residueIndexRange_iff_add_mul_le
    (q P k : Nat) [NeZero q] (y : ZMod q)
    (hrP : positiveResidueRepresentative q y ≤ P) :
    k < (P - positiveResidueRepresentative q y) / q + 1 ↔
      positiveResidueRepresentative q y + q * k ≤ P := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  let r := positiveResidueRepresentative q y
  change k < (P - r) / q + 1 ↔ r + q * k ≤ P
  constructor
  · intro hk
    have hkLe : k ≤ (P - r) / q := by omega
    have hmul : k * q ≤ P - r :=
      (Nat.le_div_iff_mul_le hq).mp hkLe
    calc
      r + q * k = r + k * q := by rw [mul_comm q k]
      _ ≤ r + (P - r) := Nat.add_le_add_left hmul r
      _ = P := Nat.add_sub_of_le hrP
  · intro hk
    have hmul : k * q ≤ P - r := by
      rw [mul_comm k q]
      exact Nat.le_sub_of_add_le' hk
    have hkLe : k ≤ (P - r) / q :=
      (Nat.le_div_iff_mul_le hq).mpr hmul
    omega

/-- A filtered sum over one positive residue class is its progression sum. -/
theorem sum_positiveResidueFinset_eq_sum_range
    {M : Type*} [AddCommMonoid M]
    (q P : Nat) [NeZero q] (y : ZMod q) (f : Nat → M)
    (hrP : positiveResidueRepresentative q y ≤ P) :
    (∑ x ∈ positiveResidueFinset q P y, f x) =
      ∑ k ∈ Finset.range
          ((P - positiveResidueRepresentative q y) / q + 1),
        f (positiveResidueRepresentative q y + q * k) := by
  let r := positiveResidueRepresentative q y
  have hrPos : 0 < r := positiveResidueRepresentative_pos q y
  symm
  refine Finset.sum_bij (fun k _ => r + q * k) ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_range] at hk
    simp only [positiveResidueFinset, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, ?_⟩, ?_⟩
    · exact (mem_residueIndexRange_iff_add_mul_le q P k y hrP).mp hk
    · exact (natCast_eq_residue_iff_eq_positiveRepresentative_add_mul
        q (r + q * k) y (by omega)).mpr ⟨k, rfl⟩
  · intro k1 hk1 k2 hk2 heq
    have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
    have hmul : q * k1 = q * k2 := Nat.add_left_cancel heq
    exact Nat.mul_left_cancel hq hmul
  · intro x hx
    simp only [positiveResidueFinset, Finset.mem_filter,
      Finset.mem_Icc] at hx
    obtain ⟨⟨hxOne, hxP⟩, hxResidue⟩ := hx
    have hxPos : 0 < x := by omega
    obtain ⟨k, hk⟩ :=
      (natCast_eq_residue_iff_eq_positiveRepresentative_add_mul
        q x y hxPos).mp hxResidue
    refine ⟨k, ?_, hk.symm⟩
    rw [Finset.mem_range]
    apply (mem_residueIndexRange_iff_add_mul_le q P k y hrP).mpr
    omega
  · intro k hk
    rfl

/-- If `P < r`, the selected positive residue finset is empty. -/
theorem positiveResidueFinset_eq_empty_of_lt
    (q P : Nat) [NeZero q] (y : ZMod q)
    (hP : P < positiveResidueRepresentative q y) :
    positiveResidueFinset q P y = ∅ := by
  apply Finset.ext
  intro x
  simp
  intro hx
  simp only [positiveResidueFinset, Finset.mem_filter, Finset.mem_Icc] at hx
  obtain ⟨⟨hxOne, hxP⟩, hxResidue⟩ := hx
  have hxPos : 0 < x := by omega
  obtain ⟨k, hk⟩ :=
    (natCast_eq_residue_iff_eq_positiveRepresentative_add_mul
      q x y hxPos).mp hxResidue
  have hrPos := positiveResidueRepresentative_pos q y
  omega

/-- If `P < r`, every filtered sum over the residue class vanishes. -/
theorem sum_positiveResidueFinset_eq_zero_of_lt
    {M : Type*} [AddCommMonoid M]
    (q P : Nat) [NeZero q] (y : ZMod q) (f : Nat → M)
    (hP : P < positiveResidueRepresentative q y) :
    (∑ x ∈ positiveResidueFinset q P y, f x) = 0 := by
  rw [positiveResidueFinset_eq_empty_of_lt q P y hP]
  simp

/-- The offset definition of the one-class sum equals a sum over actual `x`. -/
theorem residueFifthPerturbationSum_eq_sum_positiveResidueFinset
    (q : Nat) [NeZero q] (z : Real) (P : Nat) (y : ZMod q) :
    residueFifthPerturbationSum q z P y =
      ∑ x ∈ positiveResidueFinset q P y,
        Complex.exp (Complex.I * fifthPerturbationPhase z x 0) := by
  unfold residueFifthPerturbationSum
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun x _ => x - 1) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [positiveResidueFinset, Finset.mem_filter,
      Finset.mem_Icc] at hx
    obtain ⟨⟨hxOne, hxP⟩, hxResidue⟩ := hx
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · omega
    · simpa [Nat.add_sub_of_le hxOne] using hxResidue
  · intro x1 hx1 x2 hx2 heq
    simp only [positiveResidueFinset, Finset.mem_filter,
      Finset.mem_Icc] at hx1 hx2
    omega
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨hiP, hiResidue⟩ := hi
    refine ⟨1 + i, ?_, by simp⟩
    simp only [positiveResidueFinset, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, hiResidue⟩
  · intro x hx
    simp only [positiveResidueFinset, Finset.mem_filter,
      Finset.mem_Icc] at hx
    obtain ⟨⟨hxOne, hxP⟩, hxResidue⟩ := hx
    simp [fifthPerturbationPhase, Nat.add_sub_of_le hxOne]

/-- For `r ≤ P`, the one-class perturbation sum is indexed by `r + q * k`. -/
theorem residueFifthPerturbationSum_eq_sum_range
    (q : Nat) [NeZero q] (z : Real) (P : Nat) (y : ZMod q)
    (hrP : positiveResidueRepresentative q y ≤ P) :
    residueFifthPerturbationSum q z P y =
      ∑ k ∈ Finset.range
          ((P - positiveResidueRepresentative q y) / q + 1),
        Complex.exp
          (Complex.I * fifthPerturbationPhase z
            (positiveResidueRepresentative q y + q * k) 0) := by
  rw [residueFifthPerturbationSum_eq_sum_positiveResidueFinset]
  exact sum_positiveResidueFinset_eq_sum_range q P y
    (fun x => Complex.exp (Complex.I * fifthPerturbationPhase z x 0)) hrP

/-- For `P < r`, the one-class perturbation sum is zero. -/
theorem residueFifthPerturbationSum_eq_zero_of_lt
    (q : Nat) [NeZero q] (z : Real) (P : Nat) (y : ZMod q)
    (hP : P < positiveResidueRepresentative q y) :
    residueFifthPerturbationSum q z P y = 0 := by
  rw [residueFifthPerturbationSum_eq_sum_positiveResidueFinset]
  exact sum_positiveResidueFinset_eq_zero_of_lt q P y
    (fun x => Complex.exp (Complex.I * fifthPerturbationPhase z x 0)) hP

/-- Conjugating a residue-class perturbation sum reverses the sign of its
real phase. -/
theorem conj_residueFifthPerturbationSum
    (q : Nat) [NeZero q] (z : Real) (P : Nat) (y : ZMod q) :
    conj (residueFifthPerturbationSum q z P y) =
      residueFifthPerturbationSum q (-z) P y := by
  unfold residueFifthPerturbationSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs
  · rw [← Complex.exp_conj]
    congr 1
    apply Complex.ext <;> simp [fifthPerturbationPhase]
  · simp

-- These constructors retain the nonzero modulus in their reviewed residue
-- interface; later positivity and reindexing lemmas use that common contract.
attribute [nolint unusedArguments]
  positiveResidueRepresentative positiveResidueFinset

end Waring.Analytic
