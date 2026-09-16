import PrimesRestrictedDigits.Fourier.ComputableEdgeWeight
import PrimesRestrictedDigits.Fourier.FixedDenominatorCosine
import Mathlib.Algebra.Order.Floor.Div

/-!
# Fixed-denominator powered edge evaluation

Signed endpoint sums are proved nonnegative before conversion to naturals.
Exact ceiling division then reproduces the rational and Horner numerators from
the universal powered-edge construction.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

def windowEndpointSquareUpperFixedDenominator : Nat :=
  0x348739f4f637adb6d87cd8c3ebd66bd52c5e046ff5ac5086270bc1752efdedad69116d5fadf15154a32719bf14e3a294f78eb294f382df8ff8101e20f5426d13a8081deac3a5020e927d3a3aea2310b1438e49a5148141451a26ff5195f41cef817103ba08f29824fc087b9ca391fa8f84c2db3f894b42f13214e4d580958d1d4219c82acdb596aac00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

theorem windowEndpointSquareUpperFixedDenominator_eq :
    windowEndpointSquareUpperFixedDenominator =
      81 * rationalCosineUpper20D20FixedDenominator := by
  norm_num [windowEndpointSquareUpperFixedDenominator,
    rationalCosineUpper20D20FixedDenominator]

/-- Closed formula for the signed-difference multiplicity after excluding `a`. -/
def signedDifferenceCountFormula (a : Fin 10) (k : Fin 19) : Nat :=
  let difference := (signedDifference k).natAbs
  if difference = 0 then 9
  else
    10 - difference - (if a.val + difference < 10 then 1 else 0) -
      (if difference ≤ a.val then 1 else 0)

theorem signedDifferenceCountFormula_eq_table (a : Fin 10) (k : Fin 19) :
    signedDifferenceCountFormula a k = signedDifferenceCountTable a k := by
  fin_cases a <;> fin_cases k <;>
    norm_num [signedDifferenceCountFormula, signedDifference,
      signedDifferenceCountTable]

def windowEndpointSquareUpperFixedIntNumerator
    (a : Fin 10) (window : Fin 5 -> Fin 10) (offset : Int) : Int :=
  let numerator := digitWindowNumeratorFour window + offset
  ∑ k : Fin 19, (signedDifferenceCountFormula a k : Int) *
    rationalCosineUpper20D20FixedNumerator
      (centeredResidual100000 (signedDifference k * numerator))

theorem windowEndpointSquareUpperRat_eq_fixedIntNumerator
    (a : Fin 10) (window : Fin 5 -> Fin 10) (offset : Int) :
    windowEndpointSquareUpperRat a window offset =
      (windowEndpointSquareUpperFixedIntNumerator a window offset : Rat) /
        windowEndpointSquareUpperFixedDenominator := by
  rw [windowEndpointSquareUpperRat,
    windowEndpointSquareUpperFixedIntNumerator,
    windowEndpointSquareUpperFixedDenominator_eq]
  simp_rw [signedDifferenceCountFormula_eq_table]
  simp_rw [signedDifferencePhaseTermRat,
    centeredRationalPart_eq_fixedResidual,
    rationalCosineUpper20D20Rat_eq_fixedNumerator]
  simp only [mul_comm]
  push_cast
  rw [Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem windowEndpointSquareUpperFixedIntNumerator_nonneg
    (a : Fin 10) (window : Fin 5 -> Fin 10) (offset : Int) :
    0 ≤ windowEndpointSquareUpperFixedIntNumerator a window offset := by
  have hreal : (0 : Real) ≤
      (windowEndpointSquareUpperRat a window offset : Real) :=
    (sq_nonneg _).trans
      (digitKernel_sq_le_windowEndpointSquareUpperRat a window offset)
  have hrat : (0 : Rat) ≤ windowEndpointSquareUpperRat a window offset :=
    (Rat.cast_nonneg (K := Real)).mp hreal
  rw [windowEndpointSquareUpperRat_eq_fixedIntNumerator] at hrat
  rcases (div_nonneg_iff.mp hrat) with h | h
  · exact_mod_cast h.1
  · have hden : (0 : Rat) < windowEndpointSquareUpperFixedDenominator := by
      norm_num [windowEndpointSquareUpperFixedDenominator,
        rationalCosineUpper20D20FixedDenominator,
        rationalCosineUpper20D20BaseDenominator]
    exact (not_le_of_gt hden h.2).elim

def windowEndpointSquareUpperFixedNumerator
    (a : Fin 10) (window : Fin 5 -> Fin 10) (offset : Int) : Nat :=
  (windowEndpointSquareUpperFixedIntNumerator a window offset).toNat

def windowCellCorrectionFixedNumerator : Nat :=
  0x7f41a76943f3481c9a7d7748b2a563aa07622d339abfb8c295305d53499b7a97cc00936c9ab52e09e850367f284d53435c0f71adc2f091a4c030133483e3c1b900233a092b9635d51746b0d4f1699027cdba1db707dfab2f57a1f32dbfb161e01e3581a3b4d263b23c357c4641b0f9377fca642928ff9d4008e2fb5152e3099eacdec9adae7ec00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

def windowCellSquareUpperFixedNumerator
    (a : Fin 10) (window : Fin 5 -> Fin 10) : Nat :=
  max (windowEndpointSquareUpperFixedNumerator a window 0)
      (windowEndpointSquareUpperFixedNumerator a window 1) +
    windowCellCorrectionFixedNumerator

theorem windowEndpointSquareUpperRat_eq_fixedNumerator
    (a : Fin 10) (window : Fin 5 -> Fin 10) (offset : Int) :
    windowEndpointSquareUpperRat a window offset =
      (windowEndpointSquareUpperFixedNumerator a window offset : Rat) /
        windowEndpointSquareUpperFixedDenominator := by
  rw [windowEndpointSquareUpperRat_eq_fixedIntNumerator]
  congr 1
  unfold windowEndpointSquareUpperFixedNumerator
  exact_mod_cast (Int.toNat_of_nonneg
    (windowEndpointSquareUpperFixedIntNumerator_nonneg
      a window offset)).symm

theorem windowCellCorrection_eq_fixedNumerator :
    (361 / 40000000000 : Rat) =
      (windowCellCorrectionFixedNumerator : Rat) /
        windowEndpointSquareUpperFixedDenominator := by
  norm_num [windowCellCorrectionFixedNumerator,
    windowEndpointSquareUpperFixedDenominator,
    rationalCosineUpper20D20FixedDenominator,
    rationalCosineUpper20D20BaseDenominator]

theorem windowCellSquareUpperRat_eq_fixedNumerator
    (a : Fin 10) (window : Fin 5 -> Fin 10) :
    windowCellSquareUpperRat a window =
      (windowCellSquareUpperFixedNumerator a window : Rat) /
        windowEndpointSquareUpperFixedDenominator := by
  rw [windowCellSquareUpperRat,
    windowEndpointSquareUpperRat_eq_fixedNumerator,
    windowEndpointSquareUpperRat_eq_fixedNumerator,
    max_div_div_right, windowCellCorrection_eq_fixedNumerator]
  · rw [windowCellSquareUpperFixedNumerator]
    push_cast
    ring
  · positivity

theorem windowCellSquareUpperFixedNumerator_pos
    (a : Fin 10) (window : Fin 5 -> Fin 10) :
    0 < windowCellSquareUpperFixedNumerator a window := by
  unfold windowCellSquareUpperFixedNumerator
    windowCellCorrectionFixedNumerator
  norm_num

private theorem natCeil_rat_div_eq_ceilDiv (n d : Nat) (hd : 0 < d) :
    Nat.ceil ((n : Rat) / d) = n ⌈/⌉ d := by
  apply le_antisymm
  · rw [Nat.ceil_le]
    apply (div_le_iff₀ (by exact_mod_cast hd : (0 : Rat) < d)).2
    have hnat : n ≤ (n ⌈/⌉ d) * d := by
      simpa [mul_comm] using (le_smul_ceilDiv (β := Nat) hd (b := n))
    exact_mod_cast hnat
  · rw [ceilDiv_le_iff_le_mul hd]
    have h := Nat.le_ceil ((n : Rat) / d)
    rw [div_le_iff₀ (by exact_mod_cast hd : (0 : Rat) < d)] at h
    have hnat : n ≤ Nat.ceil ((n : Rat) / d) * d := by
      exact_mod_cast h
    simpa [mul_comm] using hnat

def windowCellSquareNumeratorFixed
    (D : Nat) (a : Fin 10) (window : Fin 5 -> Fin 10) : Nat :=
  (D * windowCellSquareUpperFixedNumerator a window +
      windowEndpointSquareUpperFixedDenominator - 1) /
    windowEndpointSquareUpperFixedDenominator + 1

theorem windowCellSquareNumeratorFixed_eq
    (D : Nat) (a : Fin 10) (window : Fin 5 -> Fin 10) :
    windowCellSquareNumeratorFixed D a window =
      windowCellSquareNumerator D a window := by
  rw [windowCellSquareNumeratorFixed, windowCellSquareNumerator,
    windowCellSquareUpperRat_eq_fixedNumerator]
  symm
  rw [show (D : Rat) *
      ((windowCellSquareUpperFixedNumerator a window : Rat) /
        windowEndpointSquareUpperFixedDenominator) =
      ((D * windowCellSquareUpperFixedNumerator a window : Nat) : Rat) /
        windowEndpointSquareUpperFixedDenominator by
    push_cast
    ring]
  rw [natCeil_rat_div_eq_ceilDiv _ _ (by
    norm_num [windowEndpointSquareUpperFixedDenominator,
      rationalCosineUpper20D20FixedDenominator,
      rationalCosineUpper20D20BaseDenominator]),
    Nat.ceilDiv_eq_add_pred_div]

def windowPoweredNumeratorFixed
    (D : Nat) (a : Fin 10) (window : Fin 5 -> Fin 10) : Nat :=
  hornerNum D (windowCellSquareNumeratorFixed D a window) betaBits30

theorem windowPoweredNumeratorFixed_eq
    (D : Nat) (a : Fin 10) (window : Fin 5 -> Fin 10) :
    windowPoweredNumeratorFixed D a window =
      windowPoweredNumerator D a window := by
  rw [windowPoweredNumeratorFixed, windowPoweredNumerator,
    windowCellSquareNumeratorFixed_eq]

/-- The fixed-denominator evaluator retains universal edge bound. -/
theorem poweredWindowMajorant_four_le_fixedNaturalWeight
    (D : Nat) (hD : 0 < D) (a : Fin 10) :
    ∀ window : Fin 5 -> Fin 10,
      poweredWindowMajorantWeight a 4 (235 / 154 : Real) window ≤
        naturalWindowWeight D (windowPoweredNumeratorFixed D a) window := by
  intro window
  simpa only [naturalWindowWeight, windowPoweredNumeratorFixed_eq] using
    poweredWindowMajorant_four_le_computableNaturalWeight D hD a window

end PrimesRestrictedDigits
