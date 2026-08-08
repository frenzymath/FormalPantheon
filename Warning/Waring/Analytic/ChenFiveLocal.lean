import Waring.Analytic.ChenFiveGlobalization
import Waring.Analytic.ChenFourPrimePowerInduction

/-!
# The large-prime local input to Chen's Lemma 5

This file connects the bundled primitive coefficient interface of Lemma 5 to
the integer-coefficient prime-power induction of Lemma 4.  The primitive
prime-field estimate itself remains an explicit hypothesis
[CHEN1964-EN, pp. 1549-1551; CHEN1964-ZH, pp. 717-718].
-/

namespace Waring.Analytic

open scoped BigOperators

/-- Reduce all five coefficients from a positive prime power to its prime
residue field. -/
noncomputable def primePowerFiveReduction (p alpha : Nat) (hAlpha : 0 < alpha)
    (a : FiveCoefficients (p ^ alpha)) : FiveCoefficients p := fun i =>
  ZMod.castHom (dvd_pow_self p hAlpha.ne') (ZMod p) (a i)

/-- A Bezout certificate remains a Bezout certificate after reduction from
`p^alpha` to `p`. -/
theorem primitiveFiveCoefficients_primePowerFiveReduction
    (p alpha : Nat) (hAlpha : 0 < alpha)
    (a : FiveCoefficients (p ^ alpha)) (ha : PrimitiveFiveCoefficients a) :
    PrimitiveFiveCoefficients (primePowerFiveReduction p alpha hAlpha a) := by
  rcases ha with ⟨u, hu⟩
  refine ⟨primePowerFiveReduction p alpha hAlpha u, ?_⟩
  let rho : ZMod (p ^ alpha) →+* ZMod p :=
    ZMod.castHom (dvd_pow_self p hAlpha.ne') (ZMod p)
  change ∑ i, rho (u i) * rho (a i) = 1
  calc
    (∑ i, rho (u i) * rho (a i)) =
        ∑ i, rho (u i * a i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [map_mul]
    _ = rho (∑ i, u i * a i) := by rw [map_sum]
    _ = 1 := by rw [hu, map_one]

/-- At least one coefficient of a primitive prime-power vector remains
nonzero after reduction to the prime field. -/
theorem exists_primePowerFiveReduction_ne_zero
    (p alpha : Nat) (hp : p.Prime) (hAlpha : 0 < alpha)
    (a : FiveCoefficients (p ^ alpha)) (ha : PrimitiveFiveCoefficients a) :
    ∃ i, primePowerFiveReduction p alpha hAlpha a i ≠ 0 :=
  (primitiveFiveCoefficients_iff_modPrime hp _).mp
    (primitiveFiveCoefficients_primePowerFiveReduction
      p alpha hAlpha a ha)

/-- The canonical natural representatives of a primitive vector are not all
zero modulo the underlying prime. -/
theorem primitiveFiveCoefficients_representatives_mod_prime
    (p alpha : Nat) (hp : p.Prime) (hAlpha : 0 < alpha)
    (a : FiveCoefficients (p ^ alpha)) (ha : PrimitiveFiveCoefficients a) :
    ((a 0).val : ZMod p) ≠ 0 ∨ ((a 1).val : ZMod p) ≠ 0 ∨
      ((a 2).val : ZMod p) ≠ 0 ∨ ((a 3).val : ZMod p) ≠ 0 ∨
      ((a 4).val : ZMod p) ≠ 0 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rcases exists_primePowerFiveReduction_ne_zero p alpha hp hAlpha a ha with
    ⟨i, hi⟩
  simp only [primePowerFiveReduction, ZMod.castHom_apply,
    ZMod.cast_eq_val] at hi
  fin_cases i <;> simp_all

/-- Casting the five canonical representatives back into the original
residue ring recovers the bundled complete sum. -/
theorem fivePolynomialCompleteSum_eq_integerRepresentatives
    {q : Nat} [NeZero q] (a : FiveCoefficients q) :
    fivePolynomialCompleteSum a =
      integerPolynomialCompleteSum (q := q)
        ((a 0).val : Int) ((a 1).val : Int) ((a 2).val : Int)
        ((a 3).val : Int) ((a 4).val : Int) := by
  simp [fivePolynomialCompleteSum, integerPolynomialCompleteSum]

/-- Lemma 4 supplies the Lemma 5 local estimate at every prime at least
eleven, once its primitive prime-field input is available. -/
theorem norm_fivePolynomialCompleteSum_primePower_le_of_chenFour
    (p alpha : Nat) (hp : p.Prime) (hpLarge : 11 ≤ p)
    (K : Real) (hK : 1 ≤ K)
    (hprime : @ChenFourPrimeFieldBound p ⟨hp.ne_zero⟩ K)
    (hAlpha : 0 < alpha) (a : FiveCoefficients (p ^ alpha))
    (ha : PrimitiveFiveCoefficients a) :
    ‖@fivePolynomialCompleteSum (p ^ alpha)
        ⟨pow_ne_zero alpha hp.ne_zero⟩ a‖ ≤
      K * (((p ^ alpha : Nat) : Real) ^ (4 / 5 : Real)) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (p ^ alpha) := ⟨pow_ne_zero alpha hp.ne_zero⟩
  rw [fivePolynomialCompleteSum_eq_integerRepresentatives]
  apply chenFour_primePower_rpow_bound_of_primeField
    p alpha hpLarge K hK hprime hAlpha
  simpa only [Int.cast_natCast] using
    primitiveFiveCoefficients_representatives_mod_prime
      p alpha hp hAlpha a ha

/-- The exact Chen factor is the corresponding specialization of the local
bridge. -/
theorem norm_fivePolynomialCompleteSum_primePower_le_chenFourPrimeFactor
    (p alpha : Nat) (hp : p.Prime) (hpLarge : 11 ≤ p)
    (hprime : @ChenFourPrimeFieldBound p ⟨hp.ne_zero⟩
      (chenFourPrimeFactor p))
    (hAlpha : 0 < alpha) (a : FiveCoefficients (p ^ alpha))
    (ha : PrimitiveFiveCoefficients a) :
    ‖@fivePolynomialCompleteSum (p ^ alpha)
        ⟨pow_ne_zero alpha hp.ne_zero⟩ a‖ ≤
      chenFourPrimeFactor p *
        (((p ^ alpha : Nat) : Real) ^ (4 / 5 : Real)) := by
  exact norm_fivePolynomialCompleteSum_primePower_le_of_chenFour
    p alpha hp hpLarge (chenFourPrimeFactor p)
      (one_le_chenFourPrimeFactor p) hprime hAlpha a ha

/-- Large-prime Lemma 4 inputs and separate estimates below eleven together
form the complete local hypothesis consumed by the CRT globalization theorem. -/
theorem fivePolynomialPrimePowerBound_of_chenFour_and_small
    (K : Nat → Real)
    (hK : ∀ p, p.Prime → 11 ≤ p → 1 ≤ K p)
    (hprime : ∀ (p : Nat) (hp : p.Prime), 11 ≤ p →
      @ChenFourPrimeFieldBound p ⟨hp.ne_zero⟩ (K p))
    (hsmall : ∀ (p alpha : Nat) (hp : p.Prime), 0 < alpha → p < 11 →
      ∀ (a : FiveCoefficients (p ^ alpha)),
        PrimitiveFiveCoefficients a →
          ‖@fivePolynomialCompleteSum (p ^ alpha)
              ⟨pow_ne_zero alpha hp.ne_zero⟩ a‖ ≤
            K p * (((p ^ alpha : Nat) : Real) ^ (4 / 5 : Real))) :
    FivePolynomialPrimePowerBound K := by
  intro p alpha hp hAlpha a ha
  by_cases hpLarge : 11 ≤ p
  · exact norm_fivePolynomialCompleteSum_primePower_le_of_chenFour
      p alpha hp hpLarge (K p) (hK p hp hpLarge)
        (hprime p hp hpLarge) hAlpha a ha
  · exact hsmall p alpha hp hAlpha (by omega) a ha

end Waring.Analytic
