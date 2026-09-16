import PrimesRestrictedDigits.BasicEstimates.BuchstabPrimeSum
import PrimesRestrictedDigits.PrimeNumberTheorem.PrimeCountingLogSquare

/-!
# Unconditional weighted-prime input for Buchstab induction

This closes the global log-square PNT premise in the conditional Eq. (7.45)
estimate. The coefficient is selected before every slab parameter, as required
by `MONTGOMERY-VAUGHAN-MNT-I`, Chapter 7, Theorem 7.11.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

/-- The weighted-prime estimate has one absolute coefficient, obtained by
instantiating the global log-square prime-counting remainder. -/
theorem exists_buchstabPrimeWeight_error_bound :
    ∃ B : Real, 0 < B ∧
      ∀ (m : Nat) (x u : Real),
        1 < x → 2 ≤ m →
        (m : Real) ≤ u → u ≤ (m : Real) + 1 →
        2 ≤ x ^ (1 / u) →
          |(∑ p ∈
              (naturalLeftClosedRightOpenInterval (x ^ (1 / u))
                (x ^ (1 / (m : Real)))).filter Nat.Prime,
              buchstabPrimeWeight x p) -
            x / Real.log x *
              (u * buchstabFunction u -
                (m : Real) * buchstabFunction (m : Real))| ≤
            B * ((m : Real) + 1) ^ 2 *
              (x / Real.log x ^ 2) := by
  obtain ⟨C, hC, hPNT⟩ := primeCounting_log_sq_error
  let B : Real := 2 + C / 2 + 3 * C / Real.log 2
  have hB : 0 < B := by
    dsimp [B]
    have hlog2 : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
    positivity
  refine ⟨B, hB, ?_⟩
  intro m x u hx hm hmu hu hlower
  apply (abs_sum_prime_buchstabPrimeWeight_sub_buchstabDifference_le
    (m := m) (x := x) (u := u) (C := C) hx hm hmu hu hlower hC.le ?_).trans
  · dsimp [B]
    apply le_of_eq
    ring
  · intro t ht
    simpa only [primeRemainder] using hPNT t ht

end PrimesRestrictedDigits
