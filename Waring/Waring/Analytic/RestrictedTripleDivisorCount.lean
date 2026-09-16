import Waring.Analytic.ThreeVariableAMGM
import Waring.Analytic.TripleDivisorCount

/-!
# Restricted triple-product counts

This file defines Chen's restricted `tau₃` count through nested divisors and
proves its comparison with `d₃` and its `P^3/27` support bound.
-/

namespace Waring.Analytic

/-- Nested divisor choices whose decoded positive triple has sum at most
`P`. -/
def restrictedTripleDivisorChoices (P n : Nat) :
    Finset (Sigma fun _ : Nat ↦ Nat) :=
  (tripleDivisorChoices n).filter fun x ↦
    x.2 + x.1 / x.2 + n / x.1 ≤ P

/-- Chen's restricted ordered triple-product count. -/
def restrictedTripleDivisorCount (P n : Nat) : Nat :=
  (restrictedTripleDivisorChoices P n).card

/-- Membership in the restricted choice set exposes the two exact divisor
conditions and the decoded sum bound. -/
theorem restrictedTripleDivisorChoice_data {P n : Nat}
    {x : Sigma fun _ : Nat ↦ Nat}
    (hx : x ∈ restrictedTripleDivisorChoices P n) :
    (x.1 ∣ n ∧ x.2 ∣ x.1) ∧
      x.2 + x.1 / x.2 + n / x.1 ≤ P := by
  rcases x with ⟨d, a⟩
  have hxData :
      (d ∈ n.divisors ∧ a ∈ d.divisors) ∧
        a + d / a + n / d ≤ P := by
    simpa [restrictedTripleDivisorChoices, tripleDivisorChoices] using hx
  exact ⟨⟨Nat.dvd_of_mem_divisors hxData.1.1,
    Nat.dvd_of_mem_divisors hxData.1.2⟩, hxData.2⟩

/-- The three positive factors decoded from a restricted nested-divisor
choice have product equal to the indexed integer. -/
theorem restrictedTripleDivisorChoice_product {P n : Nat}
    {x : Sigma fun _ : Nat ↦ Nat}
    (hx : x ∈ restrictedTripleDivisorChoices P n) :
    x.2 * (x.1 / x.2) * (n / x.1) = n := by
  have hxData := restrictedTripleDivisorChoice_data hx
  rw [Nat.mul_div_cancel' hxData.1.2, Nat.mul_div_cancel' hxData.1.1]

/-- The restricted triple count is bounded by the full triple-divisor
count. -/
theorem restrictedTripleDivisorCount_le (P n : Nat) :
    restrictedTripleDivisorCount P n ≤ tripleDivisorCount n := by
  rw [restrictedTripleDivisorCount, ← card_tripleDivisorChoices]
  exact Finset.card_filter_le _ _

/-- A product represented by a positive restricted count satisfies the exact
division-free support bound `27*n ≤ P^3`. -/
theorem restrictedTripleDivisorCount_support {P n : Nat}
    (hcount : 0 < restrictedTripleDivisorCount P n) :
    27 * n ≤ P ^ 3 := by
  have hnonempty : (restrictedTripleDivisorChoices P n).Nonempty :=
    Finset.card_pos.mp hcount
  obtain ⟨x, hx⟩ := hnonempty
  rcases x with ⟨d, a⟩
  have hxData := restrictedTripleDivisorChoice_data hx
  have hd : d ∣ n := hxData.1.1
  have ha : a ∣ d := hxData.1.2
  have hproduct : a * (d / a) * (n / d) = n := by
    rw [Nat.mul_div_cancel' ha, Nat.mul_div_cancel' hd]
  have hamgm :
      27 * (a : Real) * (d / a : Nat) * (n / d : Nat) ≤
        ((a : Real) + (d / a : Nat) + (n / d : Nat)) ^ 3 :=
    twentySeven_mul_le_sum_cube (by positivity) (by positivity) (by positivity)
  have hsum :
      (a : Real) + (d / a : Nat) + (n / d : Nat) ≤ P := by
    exact_mod_cast hxData.2
  have hcube :
      ((a : Real) + (d / a : Nat) + (n / d : Nat)) ^ 3 ≤
        (P : Real) ^ 3 := by
    exact pow_le_pow_left₀ (by positivity) hsum 3
  have hreal : (27 * n : Nat) ≤ (P ^ 3 : Nat) := by
    exact_mod_cast (show (27 : Real) * n ≤ (P : Real) ^ 3 by
      calc
        (27 : Real) * n =
            27 * (a : Real) * (d / a : Nat) * (n / d : Nat) := by
          have hscaled :
              27 * n = 27 * a * (d / a) * (n / d) := by
            calc
              27 * n = 27 * (a * (d / a) * (n / d)) :=
                congrArg (fun t : Nat ↦ 27 * t) hproduct.symm
              _ = 27 * a * (d / a) * (n / d) := by ring
          exact_mod_cast hscaled
        _ ≤ ((a : Real) + (d / a : Nat) + (n / d : Nat)) ^ 3 := hamgm
        _ ≤ (P : Real) ^ 3 := hcube)
  exact hreal

end Waring.Analytic
