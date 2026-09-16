import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# Finite element-incidence aggregation

This is the correct finite interface for summing repeated Buchstab states. Unlike a fiber
indexed only by the repeated prime, it counts incidences of a state with an actual integer in
a common carrier.
-/

namespace PrimesRestrictedDigits

noncomputable section

open scoped BigOperators

theorem sum_card_le_of_element_fiber_card
    {alpha beta : Type*} [DecidableEq alpha] [DecidableEq beta]
    (states : Finset alpha) (ambient : Finset beta)
    (carrier : alpha -> Finset beta) (K : Nat)
    (hsub : forall s, s ∈ states -> carrier s ⊆ ambient)
    (hfiber : forall n, n ∈ ambient ->
      (states.filter (fun s => n ∈ carrier s)).card ≤ K) :
    (∑ s ∈ states, (carrier s).card) ≤ K * ambient.card := by
  have hstate (s : alpha) (hs : s ∈ states) :
      (carrier s).card =
        ∑ n ∈ ambient, if n ∈ carrier s then 1 else 0 := by
    have hfilter : ambient.filter (fun n => n ∈ carrier s) = carrier s := by
      ext n
      constructor
      · exact fun hn => (Finset.mem_filter.mp hn).2
      · intro hn
        exact Finset.mem_filter.mpr ⟨hsub s hs hn, hn⟩
    calc
      (carrier s).card = (ambient.filter (fun n => n ∈ carrier s)).card := by
        rw [hfilter]
      _ = ∑ n ∈ ambient, if n ∈ carrier s then 1 else 0 := by
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have helement (n : beta) :
      (∑ s ∈ states, if n ∈ carrier s then 1 else 0) =
        (states.filter (fun s => n ∈ carrier s)).card := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  calc
    (∑ s ∈ states, (carrier s).card) =
        ∑ s ∈ states, ∑ n ∈ ambient,
          if n ∈ carrier s then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      exact hstate s hs
    _ = ∑ n ∈ ambient, ∑ s ∈ states,
        if n ∈ carrier s then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ n ∈ ambient,
        (states.filter (fun s => n ∈ carrier s)).card := by
      apply Finset.sum_congr rfl
      intro n hn
      exact helement n
    _ ≤ ∑ _n ∈ ambient, K := by
      apply Finset.sum_le_sum
      intro n hn
      exact hfiber n hn
    _ = K * ambient.card := by simp [mul_comm]

theorem sum_card_le_of_element_fiber_card_real
    {alpha beta : Type*} [DecidableEq alpha] [DecidableEq beta]
    (states : Finset alpha) (ambient : Finset beta)
    (carrier : alpha -> Finset beta) (K : Nat)
    (hsub : forall s, s ∈ states -> carrier s ⊆ ambient)
    (hfiber : forall n, n ∈ ambient ->
      (states.filter (fun s => n ∈ carrier s)).card ≤ K) :
    (∑ s ∈ states, ((carrier s).card : Real)) ≤
      (K : Real) * (ambient.card : Real) := by
  have h := sum_card_le_of_element_fiber_card states ambient carrier K hsub hfiber
  have hreal :
      (((∑ s ∈ states, (carrier s).card : Nat) : Real)) ≤
        (((K * ambient.card : Nat) : Real)) := by
    exact_mod_cast h
  simp only [Nat.cast_sum, Nat.cast_mul] at hreal
  exact hreal

end

end PrimesRestrictedDigits
