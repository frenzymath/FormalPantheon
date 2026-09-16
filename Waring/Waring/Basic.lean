import Waring.Statement

/-!
# Representation conventions

This file relates the fixed, zero-padded slots in the public statement to an
explicit list containing at most the allowed number of positive bases.
-/

namespace Waring

open scoped BigOperators
open Statement

/-- `n` is a sum of the `k`th powers of at most `s` positive natural numbers. -/
def HasAtMostPositivePowerSumRepresentation (k s n : Nat) : Prop :=
  ∃ xs : List Nat,
    xs.length ≤ s ∧
      (∀ x ∈ xs, 0 < x) ∧
        n = (xs.map fun x ↦ x ^ k).sum

private lemma sum_pow_filter_ne_zero (k : Nat) (hk : 0 < k) (xs : List Nat) :
    ((xs.filter fun x ↦ x != 0).map fun x ↦ x ^ k).sum =
      (xs.map fun x ↦ x ^ k).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      by_cases hx : x = 0
      · subst x
        simp [hk, ih]
      · simp [hx, ih]

/-- For a positive exponent, fixed zero-padded slots are equivalent to a list of
at most the same number of positive bases. -/
theorem hasPowerSumRepresentation_iff_atMostPositive {k s n : Nat} (hk : 0 < k) :
    HasPowerSumRepresentation k s n ↔
      HasAtMostPositivePowerSumRepresentation k s n := by
  constructor
  · rintro ⟨x, hx⟩
    let allEntries := List.ofFn x
    let positiveEntries := allEntries.filter fun u ↦ u != 0
    refine ⟨positiveEntries, ?_, ?_, ?_⟩
    · simpa [positiveEntries, allEntries] using
        List.length_filter_le (fun u : Nat ↦ u != 0) allEntries
    · intro u hu
      have hu' : u ∈ allEntries.filter (fun v ↦ v != 0) := by
        simpa [positiveEntries] using hu
      have htest : (u != 0) = true := (List.mem_filter.mp hu').2
      have hne : u ≠ 0 := by simpa using htest
      exact Nat.pos_of_ne_zero hne
    · calc
        n = ∑ i, x i ^ k := hx
        _ = (allEntries.map fun u ↦ u ^ k).sum := by
          rw [← List.ofFn_comp', List.sum_ofFn]
        _ = (positiveEntries.map fun u ↦ u ^ k).sum :=
          (sum_pow_filter_ne_zero k hk allEntries).symm
  · rintro ⟨xs, hlength, _hpositive, hx⟩
    let padded := xs ++ List.replicate (s - xs.length) 0
    have hpaddedLength : padded.length = s := by
      simp [padded, Nat.add_sub_of_le hlength]
    let x : Fin s → Nat := fun i ↦ padded.get (Fin.cast hpaddedLength.symm i)
    have hofFn : List.ofFn x = padded := by
      simpa only [List.ofFn_get, x] using
        (List.ofFn_congr hpaddedLength padded.get).symm
    refine ⟨x, ?_⟩
    calc
      n = (xs.map fun u ↦ u ^ k).sum := hx
      _ = (padded.map fun u ↦ u ^ k).sum := by simp [padded, hk]
      _ = ((List.ofFn x).map fun u ↦ u ^ k).sum := by rw [hofFn]
      _ = ∑ i, x i ^ k := by rw [← List.ofFn_comp', List.sum_ofFn]

/-- Concatenating two fixed-slot representations represents the sum of their
targets in the sum of their slot counts. -/
theorem HasPowerSumRepresentation.add {k s t n m : Nat}
    (hn : HasPowerSumRepresentation k s n)
    (hm : HasPowerSumRepresentation k t m) :
    HasPowerSumRepresentation k (s + t) (n + m) := by
  obtain ⟨x, hx⟩ := hn
  obtain ⟨y, hy⟩ := hm
  refine ⟨Fin.append x y, ?_⟩
  rw [Fin.sum_univ_add]
  simp [hx, hy]

end Waring
