import PrimesRestrictedDigits.SieveAsymptotics.DecimalSourceBoundingSieve
import PrimesRestrictedDigits.SieveDecomposition.RosserWeightSupport

/-!
# Absolute Rosser error budget for the decimal source

Rosser error sums are supported on divisors below the level. This file injects that squarefree
divisor support into Maynard's larger smooth Type-I carrier and rewrites every remainder to
the exact progression error.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- Rewrite a natural divisor-indexed remainder to the Type-I error. -/
theorem sourceBoundingSieve_rem_nat_eq_realTypeI
    (digit : Fin 10) (length : Nat) (outer_d : PNat) (z : Real)
    {e : Nat} (he : e ∈ Nat.divisors (decimalSievePrimeProduct z)) :
    (sourceBoundingSieve digit length outer_d z).rem e =
      realTypeIProgressionError digit length ((outer_d : Nat) * e) := by
  have he0 : e ≠ 0 :=
    ne_zero_of_dvd_ne_zero (decimalSievePrimeProduct_ne_zero z)
      (Nat.mem_divisors.mp he).1
  let ep : PNat := ⟨e, Nat.pos_of_ne_zero he0⟩
  have hrem := sourceBoundingSieve_rem_eq digit length outer_d ep z
  rw [sourceSieveRemainder_eq_realTypeIProgressionError] at hrem
  simpa [ep] using hrem

private theorem mem_fundamentalSmoothModuli_of_sourceDivisor
    {X epsilon delta : Real} {en : Nat}
    (he : en ∈ Nat.divisors (decimalSievePrimeProduct (X ^ delta)))
    (hlevel : (en : Real) < X ^ (epsilon / 2)) :
    en ∈ fundamentalSmoothModuli X epsilon delta := by
  have hdata := mem_divisors_decimalSievePrimeProduct_iff.mp he
  rw [mem_fundamentalSmoothModuli]
  exact ⟨hlevel, hdata.2.2.1, hdata.2.2.2⟩

theorem sourceBoundingSieve_errSum_upper_le_fundamental
    (digit : Fin 10) (length : Nat) (outer_d : PNat)
    {X epsilon delta : Real}
    (hlevel : 1 < X ^ (epsilon / 2)) :
    (sourceBoundingSieve digit length outer_d (X ^ delta)).errSum
        (upperRosserWeight (X ^ (epsilon / 2))) <=
      ∑ e ∈ fundamentalSmoothModuli X epsilon delta,
        |realTypeIProgressionError digit length ((outer_d : Nat) * e)| := by
  let sieve := sourceBoundingSieve digit length outer_d (X ^ delta)
  have hsupport := errSum_upperRosserWeight_le_level sieve hlevel
  calc
    sieve.errSum (upperRosserWeight (X ^ (epsilon / 2))) <=
        ∑ e ∈ (Nat.divisors sieve.prodPrimes).filter
          (fun e : Nat => (e : Real) < X ^ (epsilon / 2)), |sieve.rem e| :=
      hsupport
    _ = ∑ e ∈ (Nat.divisors sieve.prodPrimes).filter
          (fun e : Nat => (e : Real) < X ^ (epsilon / 2)),
          |realTypeIProgressionError digit length ((outer_d : Nat) * e)| := by
      apply Finset.sum_congr rfl
      intro e he
      rw [sourceBoundingSieve_rem_nat_eq_realTypeI digit length outer_d
        (X ^ delta) (Finset.mem_filter.mp he).1]
    _ <= ∑ e ∈ fundamentalSmoothModuli X epsilon delta,
          |realTypeIProgressionError digit length ((outer_d : Nat) * e)| := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro e he
        have heData := Finset.mem_filter.mp he
        exact mem_fundamentalSmoothModuli_of_sourceDivisor
          (X := X) (epsilon := epsilon) (delta := delta)
          heData.1 heData.2
      · intro e _ _
        exact abs_nonneg _

theorem sourceBoundingSieve_errSum_lower_le_fundamental
    (digit : Fin 10) (length : Nat) (outer_d : PNat)
    {X epsilon delta : Real}
    (hlevel : 1 < X ^ (epsilon / 2))
    (hcutoff : ∀ p, p.Prime ->
      p ∣ decimalSievePrimeProduct (X ^ delta) ->
      (p : Real) < X ^ (epsilon / 2)) :
    (sourceBoundingSieve digit length outer_d (X ^ delta)).errSum
        (lowerRosserWeight (X ^ (epsilon / 2))) <=
      ∑ e ∈ fundamentalSmoothModuli X epsilon delta,
        |realTypeIProgressionError digit length ((outer_d : Nat) * e)| := by
  let sieve := sourceBoundingSieve digit length outer_d (X ^ delta)
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
          |realTypeIProgressionError digit length ((outer_d : Nat) * e)| := by
      apply Finset.sum_congr rfl
      intro e he
      rw [sourceBoundingSieve_rem_nat_eq_realTypeI digit length outer_d
        (X ^ delta) (Finset.mem_filter.mp he).1]
    _ <= ∑ e ∈ fundamentalSmoothModuli X epsilon delta,
          |realTypeIProgressionError digit length ((outer_d : Nat) * e)| := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro e he
        have heData := Finset.mem_filter.mp he
        exact mem_fundamentalSmoothModuli_of_sourceDivisor
          (X := X) (epsilon := epsilon) (delta := delta)
          heData.1 heData.2
      · intro e _ _
        exact abs_nonneg _

end

end PrimesRestrictedDigits
