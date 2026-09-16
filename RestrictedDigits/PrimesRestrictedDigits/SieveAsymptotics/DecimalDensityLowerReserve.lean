import PrimesRestrictedDigits.SieveAsymptotics.RosserFailureSmallLogCarrierCap

/-!
# Reciprocal-prime density lower reserve

Every selected prime is at least two, so each reciprocal-prime Euler factor is at least one
half. This elementary finite reserve composes with the small-log carrier cap; it is not the
source factorial estimate.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

private theorem finset_prod_lower_pow
    (S : Finset Nat) (f : Nat -> Real) (n : Real)
    (hn : 0 <= n) (hf : forall p, p ∈ S -> n <= f p) :
    n ^ S.card <= ∏ p ∈ S, f p := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
      have hfp : n <= f p := hf p (Finset.mem_insert_self p S)
      have hfS : forall q, q ∈ S -> n <= f q := by
        intro q hq
        exact hf q (Finset.mem_insert_of_mem hq)
      have ih' := ih hfS
      rw [Finset.prod_insert hp, Finset.card_insert_of_notMem hp]
      calc
        n ^ (S.card + 1) = n * n ^ S.card := by rw [pow_succ]; ring
        _ <= f p * (∏ q ∈ S, f q) := by
          exact mul_le_mul hfp ih' (pow_nonneg hn _) (by
            have hfpNonneg : 0 <= f p := hn.trans hfp
            exact hfpNonneg)

theorem sieveDensityBelow_reciprocal_ge_half_pow_length
    (P : Finset Nat) (z : Real)
    (hprime : forall p, p ∈ P -> p.Prime) :
    (1 / 2 : Real) ^ (sieveFactorsBelow P z).length <=
      sieveDensityBelow P (fun p => (p : Real)⁻¹) z := by
  let S := P.filter (fun p : Nat => (p : Real) < z)
  have hfactor : forall p, p ∈ S -> (1 / 2 : Real) <=
      1 - (p : Real)⁻¹ := by
    intro p hp
    have hpPrime := hprime p (Finset.mem_filter.mp hp).1
    have hpTwo : (2 : Real) <= p := by exact_mod_cast hpPrime.two_le
    have hinv : (p : Real)⁻¹ <= (1 / 2 : Real) := by
      simpa only [one_div] using
        (one_div_le_one_div_of_le (by norm_num) hpTwo)
    linarith
  have hprod := finset_prod_lower_pow S
    (fun p => 1 - (p : Real)⁻¹) (1 / 2 : Real)
    (by norm_num) hfactor
  have hcard : S.card = (sieveFactorsBelow P z).length := by
    dsimp [S, sieveFactorsBelow]
    rw [Finset.length_sort]
  have hprodEq : (∏ p ∈ S, (1 - (p : Real)⁻¹)) =
      sieveDensityBelow P (fun p => (p : Real)⁻¹) z := by
    rfl
  rw [← hprodEq, ← hcard]
  exact hprod

end PrimesRestrictedDigits
