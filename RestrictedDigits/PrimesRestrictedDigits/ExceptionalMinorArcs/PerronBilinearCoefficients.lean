import PrimesRestrictedDigits.ExceptionalMinorArcs.LocalizedBilinearSum

/-!
# One-bounded prime coefficients on a Perron line

This records the complex powers omitted from the printed reduction of Proposition 9.3 and
normalizes the two prime-product weights by their exact factorial-logarithm caps.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- A real coefficient divided by a positive cap and by the Perron complex
power. -/
def normalizedPerronCoefficient
    (w : Nat → Real) (bound : Real) (s : Complex) (n : Nat) : Complex :=
  ((w n / bound : Real) : Complex) / (n : Complex) ^ s

/-- On a nonnegative Perron line, normalization by a pointwise cap gives a
one-bounded complex coefficient. -/
theorem norm_normalizedPerronCoefficient_le_one
    {w : Nat → Real} {bound : Real} {s : Complex} {n : Nat}
    (hbound : 0 < bound) (hn : 0 < n) (hw : 0 ≤ w n)
    (hwBound : w n ≤ bound) (hs : 0 ≤ s.re) :
    ‖normalizedPerronCoefficient w bound s n‖ ≤ 1 := by
  have hnOne : (1 : Real) ≤ n := by exact_mod_cast hn
  have hpow : (1 : Real) ≤ (n : Real) ^ s.re :=
    Real.one_le_rpow hnOne hs
  have hquotient : 0 ≤ w n / bound := div_nonneg hw hbound.le
  rw [normalizedPerronCoefficient, norm_div, Complex.norm_real,
    Real.norm_of_nonneg hquotient,
    Complex.norm_natCast_cpow_of_pos hn]
  calc
    w n / bound / (n : Real) ^ s.re ≤ w n / bound :=
      div_le_self hquotient hpow
    _ ≤ 1 := (div_le_one hbound).2 hwBound

/-- Restoring the positive cap recovers the original Perron coefficient
exactly. -/
theorem bound_mul_normalizedPerronCoefficient
    {w : Nat → Real} {bound : Real} {s : Complex} {n : Nat}
    (hbound : 0 < bound) :
    (bound : Complex) * normalizedPerronCoefficient w bound s n =
      (w n : Complex) / (n : Complex) ^ s := by
  rw [normalizedPerronCoefficient, ← mul_div_assoc]
  congr 1
  exact_mod_cast (mul_div_cancel₀ (w n) hbound.ne')

/-- The explicit cap for the selected product-fiber coefficient. -/
def selectedPrimePerronCoefficientCap
    (X : Nat) {k : Nat} (I : Finset (Fin k)) : Real :=
  (Nat.factorial I.card : Real) * Real.log (X : Real) ^ I.card

/-- The explicit cap for the complement-plus-last product-fiber
coefficient. -/
def complementaryPrimePerronCoefficientCap
    (X : Nat) {k : Nat} (I : Finset (Fin k)) : Real :=
  (Nat.factorial (Iᶜ.card + 1) : Real) *
    Real.log (X : Real) ^ (Iᶜ.card + 1)

theorem selectedPrimePerronCoefficientCap_pos
    {X k : Nat} (hX : 1 < X) (I : Finset (Fin k)) :
    0 < selectedPrimePerronCoefficientCap X I := by
  unfold selectedPrimePerronCoefficientCap
  exact mul_pos (by positivity) (pow_pos (Real.log_pos (by exact_mod_cast hX)) _)

theorem complementaryPrimePerronCoefficientCap_pos
    {X k : Nat} (hX : 1 < X) (I : Finset (Fin k)) :
    0 < complementaryPrimePerronCoefficientCap X I := by
  unfold complementaryPrimePerronCoefficientCap
  exact mul_pos (by positivity) (pow_pos (Real.log_pos (by exact_mod_cast hX)) _)

/-- The selected product coefficient, including its omitted complex power,
is one-bounded after normalization. -/
theorem norm_normalizedSelectedPrimePerronCoefficient_le_one
    {length k n : Nat} {a : Fin k → Real} {delta : Real}
    {I : Finset (Fin k)} {i : Nat} {s : Complex}
    (hlength : 0 < length)
    (hn : n ∈ splitProductCoordinateFiber length i)
    (hs : 0 ≤ s.re) :
    ‖normalizedPerronCoefficient
        (selectedProjectedPrimeWeightAtProduct
          (10 ^ length) a delta I)
        (selectedPrimePerronCoefficientCap (10 ^ length) I) s n‖ ≤ 1 := by
  have hX : 1 < 10 ^ length :=
    Nat.one_lt_pow hlength.ne' (by norm_num)
  apply norm_normalizedPerronCoefficient_le_one
    (selectedPrimePerronCoefficientCap_pos hX I)
    (splitProductCoordinateFiber_pos hn)
    (selectedProjectedPrimeWeightAtProduct_nonneg _ _ _ _ _)
    (selectedProjectedPrimeWeightAtProduct_le
      (10 ^ length) n a delta I
      (splitProductCoordinateFiber_lt_ambient hn))
    hs

/-- The complement-plus-last product coefficient has the analogous
one-bounded Perron normalization. -/
theorem norm_normalizedComplementaryPrimePerronCoefficient_le_one
    {length k m : Nat} {a : Fin k → Real} {delta eta : Real}
    {I : Finset (Fin k)} {i : Nat} {s : Complex}
    (hlength : 0 < length)
    (hm : m ∈ splitProductCoordinateFiber length i)
    (hs : 0 ≤ s.re) :
    ‖normalizedPerronCoefficient
        (complementaryLastPrimeWeightAtProduct
          (10 ^ length) a delta eta I)
        (complementaryPrimePerronCoefficientCap (10 ^ length) I) s m‖ ≤ 1 := by
  have hX : 1 < 10 ^ length :=
    Nat.one_lt_pow hlength.ne' (by norm_num)
  apply norm_normalizedPerronCoefficient_le_one
    (complementaryPrimePerronCoefficientCap_pos hX I)
    (splitProductCoordinateFiber_pos hm)
    (complementaryLastPrimeWeightAtProduct_nonneg _ _ _ _ _ _)
    (complementaryLastPrimeWeightAtProduct_le
      (10 ^ length) m a delta eta I
      (splitProductCoordinateFiber_lt_ambient hm))
    hs

end

end PrimesRestrictedDigits
