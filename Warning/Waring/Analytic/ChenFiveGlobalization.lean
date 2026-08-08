import Waring.Analytic.PolynomialMultiplicativity
import Mathlib.Data.Nat.Factorization.Induction

/-!
# CRT globalization in Chen's Lemma 5

This file packages the algebraic globalization step in Chen's polynomial
complete-sum estimate [CHEN1964-EN, pp. 1550-1551; CHEN1964-ZH, pp. 717-718].
The local prime-power constants remain parameters, so the result can later be
instantiated with Lemma 4 and the separate estimates at `2`, `3`, `5`, and `7`.
-/

namespace Waring.Analytic

open scoped BigOperators

/-- The five nonconstant coefficients of Chen's degree-five polynomial. -/
abbrev FiveCoefficients (q : Nat) := Fin 5 → ZMod q

/-- The polynomial complete sum with its five coefficients bundled as a
vector in descending degree order. -/
noncomputable def fivePolynomialCompleteSum {q : Nat} [NeZero q]
    (a : FiveCoefficients q) : Complex :=
  polynomialCompleteSum (a 0) (a 1) (a 2) (a 3) (a 4)

/-- A five-vector is primitive over its residue ring when its coefficients
generate the unit ideal, expressed by a finite Bezout certificate. -/
def PrimitiveFiveCoefficients {q : Nat} (a : FiveCoefficients q) : Prop :=
  ∃ u : FiveCoefficients q, ∑ i, u i * a i = 1

/-- At a prime modulus, primitivity means that at least one coefficient is
nonzero in the prime field. -/
def PrimitiveFiveCoefficientsModPrime {p : Nat}
    (a : FiveCoefficients p) : Prop :=
  ∃ i, a i ≠ 0

/-- The unit-ideal and nonzero-coefficient formulations of primitivity agree
over a prime field. -/
theorem primitiveFiveCoefficients_iff_modPrime {p : Nat} (hp : p.Prime)
    (a : FiveCoefficients p) :
    PrimitiveFiveCoefficients a ↔ PrimitiveFiveCoefficientsModPrime a := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  constructor
  · rintro ⟨u, hu⟩
    by_contra ha
    simp only [PrimitiveFiveCoefficientsModPrime, not_exists, ne_eq,
      not_not] at ha
    have hsum : (∑ i, u i * a i) = (0 : ZMod p) := by simp [ha]
    rw [hsum] at hu
    exact zero_ne_one hu
  · rintro ⟨i, hi⟩
    classical
    refine ⟨fun j => if j = i then (a i)⁻¹ else 0, ?_⟩
    simp [hi]

/-- Left normalized coefficient vector in the standard-character CRT
factorization. -/
noncomputable def normalizedCrtFiveLeft {m n : Nat} [NeZero m] [NeZero n]
    (hcoprime : m.Coprime n) (a : FiveCoefficients (m * n)) :
    FiveCoefficients m := fun i =>
  (n : ZMod m)⁻¹ * (ZMod.chineseRemainder hcoprime (a i)).1

/-- Right normalized coefficient vector in the standard-character CRT
factorization. -/
noncomputable def normalizedCrtFiveRight {m n : Nat} [NeZero m] [NeZero n]
    (hcoprime : m.Coprime n) (a : FiveCoefficients (m * n)) :
    FiveCoefficients n := fun i =>
  (m : ZMod n)⁻¹ * (ZMod.chineseRemainder hcoprime (a i)).2

/-- The left CRT projection of a primitive vector remains primitive after all
five coefficients are scaled by the inverse of the complementary modulus. -/
theorem primitiveFiveCoefficients_normalizedCrtLeft {m n : Nat}
    [NeZero m] [NeZero n] (hcoprime : m.Coprime n)
    {a : FiveCoefficients (m * n)} (ha : PrimitiveFiveCoefficients a) :
    PrimitiveFiveCoefficients (normalizedCrtFiveLeft hcoprime a) := by
  rcases ha with ⟨u, hu⟩
  have hnUnit : IsUnit (n : ZMod m) :=
    (ZMod.isUnit_iff_coprime n m).mpr hcoprime.symm
  have hnInv : (n : ZMod m) * (n : ZMod m)⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ hnUnit
  have huLeft :
      ∑ i, (ZMod.chineseRemainder hcoprime (u i)).1 *
        (ZMod.chineseRemainder hcoprime (a i)).1 = 1 := by
    let leftProjection : ZMod (m * n) →+* ZMod m :=
      (RingHom.fst (ZMod m) (ZMod n)).comp
        (ZMod.chineseRemainder hcoprime).toRingHom
    have hmap := congrArg leftProjection hu
    simpa [leftProjection] using hmap
  refine ⟨fun i => (n : ZMod m) *
    (ZMod.chineseRemainder hcoprime (u i)).1, ?_⟩
  change (∑ i, ((n : ZMod m) *
      (ZMod.chineseRemainder hcoprime (u i)).1) *
    ((n : ZMod m)⁻¹ *
      (ZMod.chineseRemainder hcoprime (a i)).1)) = 1
  calc
    (∑ i, ((n : ZMod m) *
          (ZMod.chineseRemainder hcoprime (u i)).1) *
        ((n : ZMod m)⁻¹ *
          (ZMod.chineseRemainder hcoprime (a i)).1)) =
        ∑ i, (ZMod.chineseRemainder hcoprime (u i)).1 *
          (ZMod.chineseRemainder hcoprime (a i)).1 := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        ((n : ZMod m) * (ZMod.chineseRemainder hcoprime (u i)).1) *
            ((n : ZMod m)⁻¹ *
              (ZMod.chineseRemainder hcoprime (a i)).1) =
            ((n : ZMod m) * (n : ZMod m)⁻¹) *
              ((ZMod.chineseRemainder hcoprime (u i)).1 *
                (ZMod.chineseRemainder hcoprime (a i)).1) := by ring
        _ = _ := by rw [hnInv, one_mul]
    _ = 1 := huLeft

/-- The right CRT projection of a primitive vector remains primitive after
normalization by the inverse of the complementary modulus. -/
theorem primitiveFiveCoefficients_normalizedCrtRight {m n : Nat}
    [NeZero m] [NeZero n] (hcoprime : m.Coprime n)
    {a : FiveCoefficients (m * n)} (ha : PrimitiveFiveCoefficients a) :
    PrimitiveFiveCoefficients (normalizedCrtFiveRight hcoprime a) := by
  rcases ha with ⟨u, hu⟩
  have hmUnit : IsUnit (m : ZMod n) :=
    (ZMod.isUnit_iff_coprime m n).mpr hcoprime
  have hmInv : (m : ZMod n) * (m : ZMod n)⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ hmUnit
  have huRight :
      ∑ i, (ZMod.chineseRemainder hcoprime (u i)).2 *
        (ZMod.chineseRemainder hcoprime (a i)).2 = 1 := by
    let rightProjection : ZMod (m * n) →+* ZMod n :=
      (RingHom.snd (ZMod m) (ZMod n)).comp
        (ZMod.chineseRemainder hcoprime).toRingHom
    have hmap := congrArg rightProjection hu
    simpa [rightProjection] using hmap
  refine ⟨fun i => (m : ZMod n) *
    (ZMod.chineseRemainder hcoprime (u i)).2, ?_⟩
  change (∑ i, ((m : ZMod n) *
      (ZMod.chineseRemainder hcoprime (u i)).2) *
    ((m : ZMod n)⁻¹ *
      (ZMod.chineseRemainder hcoprime (a i)).2)) = 1
  calc
    (∑ i, ((m : ZMod n) *
          (ZMod.chineseRemainder hcoprime (u i)).2) *
        ((m : ZMod n)⁻¹ *
          (ZMod.chineseRemainder hcoprime (a i)).2)) =
        ∑ i, (ZMod.chineseRemainder hcoprime (u i)).2 *
          (ZMod.chineseRemainder hcoprime (a i)).2 := by
      apply Finset.sum_congr rfl
      intro i _
      calc
        ((m : ZMod n) * (ZMod.chineseRemainder hcoprime (u i)).2) *
            ((m : ZMod n)⁻¹ *
              (ZMod.chineseRemainder hcoprime (a i)).2) =
            ((m : ZMod n) * (m : ZMod n)⁻¹) *
              ((ZMod.chineseRemainder hcoprime (u i)).2 *
                (ZMod.chineseRemainder hcoprime (a i)).2) := by ring
        _ = _ := by rw [hmInv, one_mul]
    _ = 1 := huRight

/-- Both normalized CRT coefficient vectors inherit primitivity at once. -/
theorem primitiveFiveCoefficients_normalizedCrt {m n : Nat}
    [NeZero m] [NeZero n] (hcoprime : m.Coprime n)
    {a : FiveCoefficients (m * n)} (ha : PrimitiveFiveCoefficients a) :
    PrimitiveFiveCoefficients (normalizedCrtFiveLeft hcoprime a) ∧
      PrimitiveFiveCoefficients (normalizedCrtFiveRight hcoprime a) :=
  ⟨primitiveFiveCoefficients_normalizedCrtLeft hcoprime ha,
    primitiveFiveCoefficients_normalizedCrtRight hcoprime ha⟩

/-- Exact norm factorization in the bundled five-coefficient interface. -/
theorem norm_fivePolynomialCompleteSum_mul {m n : Nat}
    [NeZero m] [NeZero n] (hcoprime : m.Coprime n)
    (a : FiveCoefficients (m * n)) :
    ‖fivePolynomialCompleteSum a‖ =
      ‖fivePolynomialCompleteSum (normalizedCrtFiveLeft hcoprime a)‖ *
        ‖fivePolynomialCompleteSum
          (normalizedCrtFiveRight hcoprime a)‖ := by
  simpa [fivePolynomialCompleteSum, normalizedCrtFiveLeft,
    normalizedCrtFiveRight] using
      norm_polynomialCompleteSum_mul_standard hcoprime
        (a 0) (a 1) (a 2) (a 3) (a 4)

/-- A parameterized family of primitive polynomial complete-sum estimates at
all positive prime powers. -/
def FivePolynomialPrimePowerBound (K : Nat → Real) : Prop :=
  ∀ (p alpha : Nat) (hp : p.Prime) (_hAlpha : 0 < alpha)
    (a : FiveCoefficients (p ^ alpha)),
    PrimitiveFiveCoefficients a →
      ‖@fivePolynomialCompleteSum (p ^ alpha)
          ⟨pow_ne_zero alpha hp.ne_zero⟩ a‖ ≤
        K p * (((p ^ alpha : Nat) : Real) ^ (4 / 5 : Real))

/-- Product of the parameterized local constants over the distinct prime
divisors of the modulus. -/
noncomputable def fivePolynomialFactor (K : Nat → Real) (q : Nat) : Real :=
  ∏ p ∈ q.primeFactors, K p

/-- The parameterized factor product is multiplicative on positive coprime
moduli. -/
theorem fivePolynomialFactor_mul (K : Nat → Real) {m n : Nat}
    (hm : m ≠ 0) (hn : n ≠ 0) (hcoprime : m.Coprime n) :
    fivePolynomialFactor K (m * n) =
      fivePolynomialFactor K m * fivePolynomialFactor K n := by
  rw [fivePolynomialFactor, fivePolynomialFactor, fivePolynomialFactor,
    Nat.primeFactors_mul hm hn, Finset.prod_union hcoprime.disjoint_primeFactors]

/-- Local estimates at every positive prime power globalize to the product of
their distinct-prime factors times `q^(4/5)`. -/
theorem norm_fivePolynomialCompleteSum_le_fivePolynomialFactor
    (K : Nat → Real) (hlocal : FivePolynomialPrimePowerBound K)
    {q : Nat} [NeZero q] (a : FiveCoefficients q)
    (ha : PrimitiveFiveCoefficients a) :
    ‖fivePolynomialCompleteSum a‖ ≤
      fivePolynomialFactor K q * (q : Real) ^ (4 / 5 : Real) := by
  let motive : Nat → Prop := fun r =>
    ∀ (hr : r ≠ 0) (b : FiveCoefficients r),
      PrimitiveFiveCoefficients b →
        ‖@fivePolynomialCompleteSum r ⟨hr⟩ b‖ ≤
          fivePolynomialFactor K r * (r : Real) ^ (4 / 5 : Real)
  have hAll : ∀ r, motive r := by
    apply Nat.recOnPosPrimePosCoprime
    · intro p alpha hp hAlpha hr b hb
      simpa [fivePolynomialFactor, primeFactors_primePow hp hAlpha] using
        hlocal p alpha hp hAlpha b hb
    · intro hr
      exact (hr rfl).elim
    · intro _hr b _hb
      simp [fivePolynomialFactor, fivePolynomialCompleteSum,
        polynomialCompleteSum, Nat.primeFactors_one]
    · intro m n hmOne hnOne hcoprime hmInd hnInd hmn b hb
      have hm : m ≠ 0 := by omega
      have hn : n ≠ 0 := by omega
      letI : NeZero m := ⟨hm⟩
      letI : NeZero n := ⟨hn⟩
      have hprimitive :=
        primitiveFiveCoefficients_normalizedCrt hcoprime hb
      have hLeft := hmInd hm (normalizedCrtFiveLeft hcoprime b) hprimitive.1
      have hRight :=
        hnInd hn (normalizedCrtFiveRight hcoprime b) hprimitive.2
      rw [norm_fivePolynomialCompleteSum_mul hcoprime]
      calc
        ‖fivePolynomialCompleteSum (normalizedCrtFiveLeft hcoprime b)‖ *
            ‖fivePolynomialCompleteSum
              (normalizedCrtFiveRight hcoprime b)‖ ≤
            (fivePolynomialFactor K m *
                (m : Real) ^ (4 / 5 : Real)) *
              (fivePolynomialFactor K n *
                (n : Real) ^ (4 / 5 : Real)) :=
          mul_le_mul hLeft hRight (norm_nonneg _)
            ((norm_nonneg _).trans hLeft)
        _ = (fivePolynomialFactor K m * fivePolynomialFactor K n) *
            ((m : Real) * n) ^ (4 / 5 : Real) := by
          rw [Real.mul_rpow (by positivity) (by positivity)]
          ring
        _ = fivePolynomialFactor K (m * n) *
            ((m * n : Nat) : Real) ^ (4 / 5 : Real) := by
          rw [fivePolynomialFactor_mul K hm hn hcoprime]
          norm_num [Nat.cast_mul]
  exact hAll q (NeZero.ne q) a ha

-- Both normalized coefficient projections retain the nonzero CRT hypotheses
-- used by their downstream factorization API, although their raw formulas do not.
attribute [nolint unusedArguments]
  normalizedCrtFiveLeft normalizedCrtFiveRight

end Waring.Analytic
