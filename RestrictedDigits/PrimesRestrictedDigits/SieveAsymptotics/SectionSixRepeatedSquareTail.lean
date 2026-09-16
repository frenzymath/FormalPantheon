import PrimesRestrictedDigits.SieveAsymptotics.SectionSixRepeatedSquareCharge
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Reciprocal square tail for repeated primes

The main term in the repeated-square charge is controlled by an elementary telescoping sum
over all naturals. This file makes no prime-distribution claim.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private theorem reciprocal_square_le_adjacent_difference
    {n : Nat} (hn : 0 < n) :
    1 / ((n + 1 : Nat) : Real) ^ (2 : Nat) ≤
      1 / (n : Real) - 1 / ((n + 1 : Nat) : Real) := by
  have hnReal : 0 < (n : Real) := by exact_mod_cast hn
  have hnSuccReal : 0 < ((n + 1 : Nat) : Real) := by positivity
  have hsq : 0 < ((n + 1 : Nat) : Real) ^ (2 : Nat) := by positivity
  field_simp
  norm_num [Nat.cast_add] at *

private theorem sum_Icc_reciprocal_square_le
    {N t : Nat} (hN : 0 < N) :
    (∑ n ∈ Finset.Icc (N + 1) (N + 1 + t),
        1 / ((n : Nat) : Real) ^ (2 : Nat)) ≤
      1 / (N : Real) - 1 / ((N + 1 + t : Nat) : Real) := by
  induction t with
  | zero =>
      have hsingle : Finset.Icc (N + 1) (N + 1) = {N + 1} := by
        simp
      rw [hsingle]
      simp only [Finset.sum_singleton]
      have hstep := reciprocal_square_le_adjacent_difference hN
      simpa [Nat.cast_add, add_assoc] using hstep
  | succ t iht =>
      rw [show N + 1 + (Nat.succ t) = (N + 1 + t) + 1 by omega]
      rw [Finset.sum_Icc_succ_top (by omega)]
      calc
        (∑ n ∈ Finset.Icc (N + 1) (N + 1 + t),
            1 / ((n : Nat) : Real) ^ (2 : Nat)) +
            1 / ((N + 1 + t + 1 : Nat) : Real) ^ (2 : Nat) =
          1 / ((N + 1 + t + 1 : Nat) : Real) ^ (2 : Nat) +
            (∑ n ∈ Finset.Icc (N + 1) (N + 1 + t),
              1 / ((n : Nat) : Real) ^ (2 : Nat) : Real) := by
                ring
        _ ≤ 1 / ((N + 1 + t + 1 : Nat) : Real) ^ (2 : Nat) +
            (1 / (N : Real) - 1 / ((N + 1 + t : Nat) : Real)) :=
          add_le_add_right iht _
        _ ≤ 1 / (N : Real) -
            1 / ((N + 1 + t + 1 : Nat) : Real) := by
          have hstep := reciprocal_square_le_adjacent_difference
            (show 0 < N + 1 + t by omega)
          have hstep' := add_le_add_left hstep
            (1 / (N : Real) - 1 / ((N + 1 + t : Nat) : Real))
          convert hstep' using 1
          ring

/-- The reciprocal square sum over any finite source prime interval is at
most `2/y` once its lower endpoint is at least two. -/
theorem sum_reciprocal_square_sievePrimeInterval_le
    {y z : Real} (hy : 2 ≤ y) :
    (∑ q ∈ sievePrimeInterval y z,
        1 / (q : Real) ^ (2 : Nat)) ≤ 2 / y := by
  classical
  let N : Nat := Nat.floor y
  let M : Nat := Nat.ceil z
  have hy0 : 0 ≤ y := by linarith
  have hNpos : 0 < N := by
    dsimp only [N]
    rw [Nat.floor_pos]
    linarith
  have hsubset : sievePrimeInterval y z ⊆ Finset.Icc (N + 1) M := by
    intro q hq
    have hqData := mem_sievePrimeInterval.mp hq
    have hfloor : N < q := by
      dsimp only [N]
      exact (Nat.floor_lt hy0).mpr hqData.2.1
    have hupperReal : (q : Real) ≤ (M : Real) :=
      hqData.2.2.trans (Nat.le_ceil z)
    have hupper : q ≤ M := by exact_mod_cast hupperReal
    exact Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt hfloor, hupper⟩
  have hsumSubset :
      (∑ q ∈ sievePrimeInterval y z,
          1 / (q : Real) ^ (2 : Nat)) ≤
        ∑ q ∈ Finset.Icc (N + 1) M,
          1 / (q : Real) ^ (2 : Nat) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun q hq _ => by positivity)
  have htail :
      (∑ q ∈ Finset.Icc (N + 1) M,
          1 / (q : Real) ^ (2 : Nat)) ≤ 1 / (N : Real) := by
    by_cases hNM : N + 1 ≤ M
    · let t : Nat := M - (N + 1)
      have hM : M = N + 1 + t := by
        dsimp only [t]
        omega
      rw [hM]
      have htel := sum_Icc_reciprocal_square_le hNpos (N := N) (t := t)
      have hnonneg : 0 ≤ 1 / ((N + 1 + t : Nat) : Real) := by positivity
      linarith
    · rw [Finset.Icc_eq_empty hNM]
      simp
  have hfloorLower : y / 2 ≤ (N : Real) := by
    have hfloorUpper : y < (N : Real) + 1 := by
      dsimp only [N]
      exact Nat.lt_floor_add_one y
    linarith
  have hNReal : 0 < (N : Real) := by exact_mod_cast hNpos
  have hyPos : 0 < y := by linarith
  have hinv : 1 / (N : Real) ≤ 2 / y := by
    apply (div_le_div_iff₀ hNReal hyPos).2
    nlinarith
  exact hsumSubset.trans (htail.trans hinv)

end

end PrimesRestrictedDigits
