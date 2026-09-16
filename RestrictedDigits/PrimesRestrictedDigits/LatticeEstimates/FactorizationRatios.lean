import PrimesRestrictedDigits.LatticeEstimates.RationalFactorization

/-!
# Ratio identities for the Lemma 14.3 factorization

These identities transport the simultaneous approximation errors from the common denominator
`q` to the two individually reduced denominators used by the hybrid sums.
-/

namespace PrimesRestrictedDigits

/-- Cancelling a positive first-coordinate factor preserves nonnegativity of
the reduced numerator. -/
theorem LatticeRationalFactorization.b1Prime_nonneg
    {b1 b2 : Int} {q : Nat}
    (f : LatticeRationalFactorization b1 b2 q) (hb1 : 0 <= b1) :
    0 <= f.b1Prime := by
  by_contra hnonneg
  have hb1PrimeNeg : f.b1Prime < 0 := lt_of_not_ge hnonneg
  have hfactorPos : (0 : Int) < (f.d1 : Int) * f.g1Prime := by
    exact_mod_cast Nat.mul_pos f.d1_pos f.g1Prime_pos
  have hproductNeg : f.b1Prime * ((f.d1 : Int) * f.g1Prime) < 0 :=
    mul_neg_of_neg_of_pos hb1PrimeNeg hfactorPos
  rw [← f.firstNumerator_eq] at hproductNeg
  exact (not_lt_of_ge hb1) hproductNeg

/-- Cancelling a positive second-coordinate factor preserves nonnegativity of
the reduced numerator. -/
theorem LatticeRationalFactorization.b2Prime_nonneg
    {b1 b2 : Int} {q : Nat}
    (f : LatticeRationalFactorization b1 b2 q) (hb2 : 0 <= b2) :
    0 <= f.b2Prime := by
  by_contra hnonneg
  have hb2PrimeNeg : f.b2Prime < 0 := lt_of_not_ge hnonneg
  have hfactorPos : (0 : Int) < f.g2 := by exact_mod_cast f.g2_pos
  have hproductNeg : f.b2Prime * (f.g2 : Int) < 0 :=
    mul_neg_of_neg_of_pos hb2PrimeNeg hfactorPos
  rw [← f.secondNumerator_eq] at hproductNeg
  exact (not_lt_of_ge hb2) hproductNeg

/-- The first source ratio has denominator `d0*qPrime*g2` after cancelling
the first coordinate gcd. -/
theorem LatticeRationalFactorization.first_ratio_eq
    {b1 b2 : Int} {q : Nat}
    (f : LatticeRationalFactorization b1 b2 q) :
    (b1 : Real) / (q : Real) =
      (f.b1Prime : Real) / ((f.d0 * f.qPrime * f.g2 : Nat) : Real) := by
  have hqPos : 0 < q := by
    calc
      0 < f.g1Prime * f.g2 * f.d0 * f.d1 * f.qPrime :=
        Nat.mul_pos
          (Nat.mul_pos
            (Nat.mul_pos (Nat.mul_pos f.g1Prime_pos f.g2_pos) f.d0_pos)
            f.d1_pos)
          f.qPrime_pos
      _ = q := f.denominator_eq.symm
  have hmPos : 0 < f.d0 * f.qPrime * f.g2 :=
    Nat.mul_pos (Nat.mul_pos f.d0_pos f.qPrime_pos) f.g2_pos
  apply (div_eq_div_iff (by exact_mod_cast hqPos.ne')
    (by exact_mod_cast hmPos.ne')).2
  have hdenominator : (q : Real) =
      (f.g1Prime : Real) * f.g2 * f.d0 * f.d1 * f.qPrime := by
    exact_mod_cast f.denominator_eq
  have hnumerator : (b1 : Real) =
      (f.b1Prime : Real) * ((f.d1 : Real) * f.g1Prime) := by
    exact_mod_cast f.firstNumerator_eq
  rw [hdenominator, hnumerator]
  push_cast
  ring

/-- The second source ratio has denominator
`d0*d1*qPrime*g1Prime` after cancelling the second coordinate gcd. -/
theorem LatticeRationalFactorization.second_ratio_eq
    {b1 b2 : Int} {q : Nat}
    (f : LatticeRationalFactorization b1 b2 q) :
    (b2 : Real) / (q : Real) =
      (f.b2Prime : Real) /
        ((f.d0 * f.d1 * f.qPrime * f.g1Prime : Nat) : Real) := by
  have hqPos : 0 < q := by
    calc
      0 < f.g1Prime * f.g2 * f.d0 * f.d1 * f.qPrime :=
        Nat.mul_pos
          (Nat.mul_pos
            (Nat.mul_pos (Nat.mul_pos f.g1Prime_pos f.g2_pos) f.d0_pos)
            f.d1_pos)
          f.qPrime_pos
      _ = q := f.denominator_eq.symm
  have hmPos : 0 < f.d0 * f.d1 * f.qPrime * f.g1Prime :=
    Nat.mul_pos
      (Nat.mul_pos (Nat.mul_pos f.d0_pos f.d1_pos) f.qPrime_pos)
      f.g1Prime_pos
  apply (div_eq_div_iff (by exact_mod_cast hqPos.ne')
    (by exact_mod_cast hmPos.ne')).2
  have hdenominator : (q : Real) =
      (f.g1Prime : Real) * f.g2 * f.d0 * f.d1 * f.qPrime := by
    exact_mod_cast f.denominator_eq
  have hnumerator : (b2 : Real) =
      (f.b2Prime : Real) * f.g2 := by
    exact_mod_cast f.secondNumerator_eq
  rw [hdenominator, hnumerator]
  push_cast
  ring

end PrimesRestrictedDigits
