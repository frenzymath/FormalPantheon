import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Order.Interval.Finset.Nat

/-!
# Partial sums of nonprincipal Dirichlet characters

This proves the complete-period cancellation estimate used in the
partial-summation argument of `MONTGOMERY-VAUGHAN-MNT-I`, Chapter 10,
Lemma 10.15, p. 350.
-/

open Finset

namespace PrimesRestrictedDigits

private lemma finEquiv_apply_eq_natCast_val {q : Nat} [NeZero q] (i : Fin q) :
    (ZMod.finEquiv q) i = (i.val : ZMod q) := by
  apply ZMod.val_injective q
  rw [ZMod.val_natCast_of_lt i.isLt]
  cases q with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ q => rfl

private lemma sum_range_dirichletCharacter_eq_zero {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (hchi : chi ≠ 1) :
    ∑ n ∈ range q, chi n = 0 := by
  calc
    ∑ n ∈ range q, chi n = ∑ i : Fin q, chi (i.val : ZMod q) :=
      (Fin.sum_univ_eq_sum_range (fun n => chi n) q).symm
    _ = ∑ i : Fin q, chi ((ZMod.finEquiv q) i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [finEquiv_apply_eq_natCast_val]
    _ = ∑ a : ZMod q, chi a := (ZMod.finEquiv q).toEquiv.sum_comp chi
    _ = 0 := chi.sum_eq_zero_of_ne_one hchi

private lemma periodic_apply_mul_add {f : Nat → Complex} {q : Nat}
    (hf : Function.Periodic f q) (k n : Nat) :
    f (q * k + n) = f n := by
  simpa only [Nat.nsmul_eq_mul, Nat.mul_comm, Nat.add_comm] using hf.nsmul k n

private lemma sum_range_mul_eq_nsmul_sum_range_of_periodic
    {f : Nat → Complex} {q : Nat} (hf : Function.Periodic f q) (m : Nat) :
    ∑ n ∈ range (q * m), f n = m • ∑ n ∈ range q, f n := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.mul_succ, sum_range_add, ih, succ_nsmul]
      congr 1
      apply Finset.sum_congr rfl
      intro n _
      exact periodic_apply_mul_add hf m n

private lemma sum_range_dirichletCharacter_eq_sum_range_mod
    {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
    (hchi : chi ≠ 1) (n : Nat) :
    ∑ k ∈ range n, chi k = ∑ k ∈ range (n % q), chi k := by
  have hperiodic : Function.Periodic (fun k : Nat => chi k) q := by
    intro k
    simp only [Nat.cast_add, ZMod.natCast_self, add_zero]
  conv_lhs => rw [← Nat.div_add_mod n q]
  rw [sum_range_add,
    sum_range_mul_eq_nsmul_sum_range_of_periodic hperiodic,
    sum_range_dirichletCharacter_eq_zero chi hchi, smul_zero, zero_add]
  apply Finset.sum_congr rfl
  intro k _
  exact periodic_apply_mul_add hperiodic (n / q) k

private lemma norm_sum_range_dirichletCharacter_le_level
    {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
    (hchi : chi ≠ 1) (n : Nat) :
    norm (∑ k ∈ range n, chi k) ≤ (q : Real) := by
  rw [sum_range_dirichletCharacter_eq_sum_range_mod chi hchi]
  calc
    norm (∑ k ∈ range (n % q), chi k) ≤
        ∑ k ∈ range (n % q), norm (chi k) := norm_sum_le _ _
    _ ≤ ∑ _k ∈ range (n % q), (1 : Real) := by
      gcongr with k hk
      exact chi.norm_le_one k
    _ = ((n % q : Nat) : Real) := by simp
    _ ≤ (q : Real) := by
      exact_mod_cast (Nat.mod_lt n (Nat.pos_of_ne_zero (NeZero.ne q))).le

/-- A partial sum of a nonprincipal Dirichlet character has norm at most its
level. This is an exact project form of the complete-period cancellation input to
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 10, Lemma 10.15, p. 350. -/
theorem norm_sum_dirichletCharacter_Icc_le_level
    {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
    (hchi : chi ≠ 1) (n : Nat) :
    norm (∑ k ∈ Icc 1 n, chi k) ≤ (q : Real) := by
  have hq : q ≠ 1 := by
    intro h
    exact hchi (chi.level_one' h)
  have hzero : chi (0 : Nat) = 0 := by
    simpa only [Nat.cast_zero] using chi.map_zero' hq
  have hsum : ∑ k ∈ Icc 1 n, chi k = ∑ k ∈ Icc 0 n, chi k := by
    rw [← insert_Icc_add_one_left_eq_Icc n.zero_le, sum_insert (by aesop),
      hzero, zero_add]
    simp only [zero_add]
  rw [hsum, ← Nat.range_succ_eq_Icc_zero]
  exact norm_sum_range_dirichletCharacter_le_level chi hchi (n + 1)

end PrimesRestrictedDigits
