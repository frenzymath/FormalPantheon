import PrimesRestrictedDigits.SieveAsymptotics.DecimalAmbientBoundingSieve
import PrimesRestrictedDigits.SieveAsymptotics.FundamentalRemainderBridge
import PrimesRestrictedDigits.SieveDecomposition.RosserWeightSupport

/-!
# Absolute Rosser error budget for the coprime ambient sieve

Both Rosser error supports inject into the weak-smooth Type-I carrier, and their remainders
are the elementary ambient progression errors.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

theorem ambientBoundingSieve_rem_nat_eq_progressionError
    (length : Nat) (outer_d : PNat) (z : Real)
    {e : Nat} (he : e ∈ Nat.divisors (decimalSievePrimeProduct z)) :
    (ambientBoundingSieve length outer_d z).rem e =
      ambientSieveProgressionError length ((outer_d : Nat) * e) := by
  have he0 : e ≠ 0 :=
    ne_zero_of_dvd_ne_zero (decimalSievePrimeProduct_ne_zero z)
      (Nat.mem_divisors.mp he).1
  let ep : PNat := ⟨e, Nat.pos_of_ne_zero he0⟩
  have hrem := ambientBoundingSieve_rem_eq length outer_d ep z
  simpa [ep] using hrem

private theorem mem_fundamentalSmoothModuli_of_ambientDivisor
    {X epsilon delta : Real} {e : Nat}
    (he : e ∈ Nat.divisors (decimalSievePrimeProduct (X ^ delta)))
    (hlevel : (e : Real) < X ^ (epsilon / 2)) :
    e ∈ fundamentalSmoothModuli X epsilon delta := by
  have hdata := mem_divisors_decimalSievePrimeProduct_iff.mp he
  rw [mem_fundamentalSmoothModuli]
  exact ⟨hlevel, hdata.2.2.1, hdata.2.2.2⟩

theorem ambientBoundingSieve_errSum_upper_le_fundamental
    (length : Nat) (outer_d : PNat) {X epsilon delta : Real}
    (hlevel : 1 < X ^ (epsilon / 2)) :
    (ambientBoundingSieve length outer_d (X ^ delta)).errSum
        (upperRosserWeight (X ^ (epsilon / 2))) <=
      ∑ e ∈ fundamentalSmoothModuli X epsilon delta,
        |ambientSieveProgressionError length ((outer_d : Nat) * e)| := by
  let sieve := ambientBoundingSieve length outer_d (X ^ delta)
  have hsupport := errSum_upperRosserWeight_le_level sieve hlevel
  calc
    sieve.errSum (upperRosserWeight (X ^ (epsilon / 2))) <=
        ∑ e ∈ (Nat.divisors sieve.prodPrimes).filter
          (fun e : Nat => (e : Real) < X ^ (epsilon / 2)), |sieve.rem e| :=
      hsupport
    _ = ∑ e ∈ (Nat.divisors sieve.prodPrimes).filter
          (fun e : Nat => (e : Real) < X ^ (epsilon / 2)),
          |ambientSieveProgressionError length ((outer_d : Nat) * e)| := by
      apply Finset.sum_congr rfl
      intro e he
      rw [ambientBoundingSieve_rem_nat_eq_progressionError length outer_d
        (X ^ delta) (Finset.mem_filter.mp he).1]
    _ <= ∑ e ∈ fundamentalSmoothModuli X epsilon delta,
          |ambientSieveProgressionError length ((outer_d : Nat) * e)| := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro e he
        have heData := Finset.mem_filter.mp he
        exact mem_fundamentalSmoothModuli_of_ambientDivisor
          (X := X) (epsilon := epsilon) (delta := delta)
          heData.1 heData.2
      · intro e _ _
        exact abs_nonneg _

theorem ambientBoundingSieve_errSum_lower_le_fundamental
    (length : Nat) (outer_d : PNat) {X epsilon delta : Real}
    (hlevel : 1 < X ^ (epsilon / 2))
    (hcutoff : ∀ p, p.Prime ->
      p ∣ decimalSievePrimeProduct (X ^ delta) ->
      (p : Real) < X ^ (epsilon / 2)) :
    (ambientBoundingSieve length outer_d (X ^ delta)).errSum
        (lowerRosserWeight (X ^ (epsilon / 2))) <=
      ∑ e ∈ fundamentalSmoothModuli X epsilon delta,
        |ambientSieveProgressionError length ((outer_d : Nat) * e)| := by
  let sieve := ambientBoundingSieve length outer_d (X ^ delta)
  have hprimeCutoff : ∀ p, p.Prime -> p ∣ sieve.prodPrimes ->
      (p : Real) < X ^ (epsilon / 2) := by
    intro p hp hpd
    exact hcutoff p hp (by simpa [sieve] using hpd)
  have hsupport := errSum_lowerRosserWeight_le_level sieve hlevel hprimeCutoff
  calc
    sieve.errSum (lowerRosserWeight (X ^ (epsilon / 2))) <=
        ∑ e ∈ (Nat.divisors sieve.prodPrimes).filter
          (fun e : Nat => (e : Real) < X ^ (epsilon / 2)), |sieve.rem e| :=
      hsupport
    _ = ∑ e ∈ (Nat.divisors sieve.prodPrimes).filter
          (fun e : Nat => (e : Real) < X ^ (epsilon / 2)),
          |ambientSieveProgressionError length ((outer_d : Nat) * e)| := by
      apply Finset.sum_congr rfl
      intro e he
      rw [ambientBoundingSieve_rem_nat_eq_progressionError length outer_d
        (X ^ delta) (Finset.mem_filter.mp he).1]
    _ <= ∑ e ∈ fundamentalSmoothModuli X epsilon delta,
          |ambientSieveProgressionError length ((outer_d : Nat) * e)| := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro e he
        have heData := Finset.mem_filter.mp he
        exact mem_fundamentalSmoothModuli_of_ambientDivisor
          (X := X) (epsilon := epsilon) (delta := delta)
          heData.1 heData.2
      · intro e _ _
        exact abs_nonneg _

end

end PrimesRestrictedDigits
