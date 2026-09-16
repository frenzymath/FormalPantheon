import Waring.Analytic.ChenFive
import Waring.Analytic.ChenSevenPartition
import Waring.Analytic.ChenSevenResidueApproximation

/-!
# Chen's Lemma 7

This file joins the three denominator ranges in Chen's first minor-arc
estimate [CHEN1964-EN, pp. 1551-1552; CHEN1964-ZH, pp. 718-719].
-/

namespace Waring.Analytic

open scoped BigOperators

/-- The three-range conclusion assuming the completed polynomial-sum estimate
used by the large and middle ranges. -/
theorem chenSeven_bound_of_completeSum
    (q : Nat) [NeZero q] (a : Nat) (z : Real) (P : Nat)
    (hPThreshold : (10 : Real) ^ 150 <= P)
    (hqLower : (P : Real) ^ (1 / 2 : Real) <= q)
    (hqUpper : (q : Real) <= (P : Real) ^ (26 / 25 : Real))
    (ha : IsUnit (a : ZMod q))
    (hz : |z| <= 1 / (10 * (q : Real) * (P : Real) ^ 4))
    (hcomplete : forall h : ZMod q,
      ‖polynomialCompleteSum (a : ZMod q) 0 0 0 h‖ <=
        10 ^ 15 * (q : Real) ^ (4 / 5 : Real)) :
    ‖∑ i ∈ Finset.range P,
        Complex.exp
          (2 * Real.pi * Complex.I *
            (((a : Real) / q + z) * (((1 + i : Nat) : Real) ^ 5)))‖ <=
      (P : Real) ^ (24 / 25 : Real) := by
  by_cases hqSmall : (q : Real) <= (P : Real) ^ (19 / 20 : Real)
  · exact chenSeven_smallDenominator_bound q a z P hPThreshold
      hqLower hqSmall ha hz
  have hqMiddleLower :
      (P : Real) ^ (19 / 20 : Real) <= (q : Real) :=
    (lt_of_not_ge hqSmall).le
  by_cases hPq : P <= 2 * q
  · exact chenSeven_largeDenominator_bound q a z P hPThreshold
      hPq hqUpper hz hcomplete
  have hqP : (q : Real) <= (P : Real) := by
    have hqPNat : q <= P := by omega
    exact_mod_cast hqPNat
  exact chenSeven_middleDenominator_bound q a z P hPThreshold
    hqMiddleLower hqP hz hcomplete

/-- Chen's Lemma 7, conditional only on the two explicit analytic inputs still
required by the source-shaped Lemma 5 theorem. -/
theorem chen_lemma_seven
    (hsmall : ChenFiveHuaSmallPrimePowerBound)
    (hlarge : ChenFiveLargePrimeFieldBound)
    (q : Nat) [NeZero q] (a : Nat) (z : Real) (P : Nat)
    (hPThreshold : (10 : Real) ^ 150 <= P)
    (hqLower : (P : Real) ^ (1 / 2 : Real) <= q)
    (hqUpper : (q : Real) <= (P : Real) ^ (26 / 25 : Real))
    (ha : IsUnit (a : ZMod q))
    (hz : |z| <= 1 / (10 * (q : Real) * (P : Real) ^ 4)) :
    ‖∑ i ∈ Finset.range P,
        Complex.exp
          (2 * Real.pi * Complex.I *
            (((a : Real) / q + z) * (((1 + i : Nat) : Real) ^ 5)))‖ <=
      (P : Real) ^ (24 / 25 : Real) := by
  apply chenSeven_bound_of_completeSum q a z P hPThreshold hqLower hqUpper ha hz
  intro h
  let coeff : FiveCoefficients q := ![(a : ZMod q), 0, 0, 0, h]
  have hprimitive : PrimitiveFiveCoefficients coeff := by
    refine ⟨![(a : ZMod q)⁻¹, 0, 0, 0, 0], ?_⟩
    simp [coeff, Fin.sum_univ_succ, mul_comm,
      ZMod.mul_inv_of_unit _ ha]
  simpa [fivePolynomialCompleteSum, coeff] using
    chen_five_polynomialCompleteSum_bound hsmall hlarge coeff hprimitive

end Waring.Analytic
