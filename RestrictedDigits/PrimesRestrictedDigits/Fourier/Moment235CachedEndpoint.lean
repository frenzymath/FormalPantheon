import PrimesRestrictedDigits.Fourier.FixedDenominatorEdge
import PrimesRestrictedDigits.Fourier.Moment235CachedCosineBound

/-!
# Cached endpoint and cell upper bounds

The signed cosine cache is summed with the exact digit-difference
multiplicities. Nonnegativity is proved before conversion to naturals.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

def moment235EndpointDenominator : Nat :=
  81 * moment235CosineScale

theorem moment235EndpointDenominator_pos :
    0 < moment235EndpointDenominator := by
  norm_num [moment235EndpointDenominator, moment235CosineScale]

def moment235EndpointIntNumeratorOfValue
    (a : Fin 10) (value offset : Int) : Int :=
  ∑ k : Fin 19, (signedDifferenceCountFormula a k : Int) *
    moment235CenteredCosineUpperNumerator
      (signedDifference k * (value + offset))

def moment235EndpointIntNumerator
    (a : Fin 10) (window : Fin 5 -> Fin 10) (offset : Int) : Int :=
  moment235EndpointIntNumeratorOfValue a
    (digitWindowNumeratorFour window) offset

private theorem signedDifferencePhaseTermRat_le_moment235Cache
    (window : Fin 5 -> Fin 10) (offset : Int) (k : Fin 19) :
    signedDifferencePhaseTermRat window offset k <=
      (moment235CenteredCosineUpperNumerator
          (signedDifference k *
            (digitWindowNumeratorFour window + offset)) : Rat) /
        moment235CosineScale := by
  rw [signedDifferencePhaseTermRat,
    centeredRationalPart_eq_fixedResidual]
  exact rationalCosineUpper20D20Rat_centered_le_moment235Cache _

theorem windowEndpointSquareUpperRat_le_moment235Endpoint
    (a : Fin 10) (window : Fin 5 -> Fin 10) (offset : Int) :
    windowEndpointSquareUpperRat a window offset <=
      (moment235EndpointIntNumerator a window offset : Rat) /
        moment235EndpointDenominator := by
  rw [windowEndpointSquareUpperRat]
  simp_rw [← signedDifferenceCountFormula_eq_table]
  calc
    (1 / 81 : Rat) *
          ∑ k : Fin 19, (signedDifferenceCountFormula a k : Rat) *
            signedDifferencePhaseTermRat window offset k <=
        (1 / 81 : Rat) *
          ∑ k : Fin 19, (signedDifferenceCountFormula a k : Rat) *
            ((moment235CenteredCosineUpperNumerator
                (signedDifference k *
                  (digitWindowNumeratorFour window + offset)) : Rat) /
              moment235CosineScale) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_left
        (signedDifferencePhaseTermRat_le_moment235Cache window offset k)
      positivity
    _ = (moment235EndpointIntNumerator a window offset : Rat) /
          moment235EndpointDenominator := by
      rw [moment235EndpointIntNumerator,
        moment235EndpointIntNumeratorOfValue, moment235EndpointDenominator]
      push_cast
      simp_rw [← mul_div_assoc]
      rw [← Finset.sum_div]
      ring

theorem moment235EndpointIntNumerator_nonneg
    (a : Fin 10) (window : Fin 5 -> Fin 10) (offset : Int) :
    0 <= moment235EndpointIntNumerator a window offset := by
  have hreal : (0 : Real) <=
      (windowEndpointSquareUpperRat a window offset : Real) :=
    (sq_nonneg _).trans
      (digitKernel_sq_le_windowEndpointSquareUpperRat a window offset)
  have hrat : (0 : Rat) <= windowEndpointSquareUpperRat a window offset :=
    (Rat.cast_nonneg (K := Real)).mp hreal
  have hcached : (0 : Rat) <=
      (moment235EndpointIntNumerator a window offset : Rat) /
        moment235EndpointDenominator :=
    hrat.trans (windowEndpointSquareUpperRat_le_moment235Endpoint
      a window offset)
  rcases div_nonneg_iff.mp hcached with h | h
  · exact_mod_cast h.1
  · have hden : (0 : Rat) < moment235EndpointDenominator := by
      exact_mod_cast moment235EndpointDenominator_pos
    exact (not_le_of_gt hden h.2).elim

def moment235EndpointNumerator
    (a : Fin 10) (window : Fin 5 -> Fin 10) (offset : Int) : Nat :=
  (moment235EndpointIntNumerator a window offset).toNat

theorem moment235EndpointRat_eq_natural
    (a : Fin 10) (window : Fin 5 -> Fin 10) (offset : Int) :
    (moment235EndpointIntNumerator a window offset : Rat) /
        moment235EndpointDenominator =
      (moment235EndpointNumerator a window offset : Rat) /
        moment235EndpointDenominator := by
  congr 1
  unfold moment235EndpointNumerator
  exact_mod_cast (Int.toNat_of_nonneg
    (moment235EndpointIntNumerator_nonneg a window offset)).symm

def moment235CellCorrectionNumerator : Nat :=
  361 * (moment235EndpointDenominator / 40000000000)

theorem moment235CellCorrection_eq_numerator :
    (361 / 40000000000 : Rat) =
      (moment235CellCorrectionNumerator : Rat) /
        moment235EndpointDenominator := by
  norm_num [moment235CellCorrectionNumerator, moment235EndpointDenominator,
    moment235CosineScale]

def moment235CellNumerator
    (a : Fin 10) (window : Fin 5 -> Fin 10) : Nat :=
  max (moment235EndpointNumerator a window 0)
      (moment235EndpointNumerator a window 1) +
    moment235CellCorrectionNumerator

theorem windowCellSquareUpperRat_le_moment235Cell
    (a : Fin 10) (window : Fin 5 -> Fin 10) :
    windowCellSquareUpperRat a window <=
      (moment235CellNumerator a window : Rat) /
        moment235EndpointDenominator := by
  rw [windowCellSquareUpperRat]
  have hzero := (windowEndpointSquareUpperRat_le_moment235Endpoint
    a window 0).trans_eq (moment235EndpointRat_eq_natural a window 0)
  have hone := (windowEndpointSquareUpperRat_le_moment235Endpoint
    a window 1).trans_eq (moment235EndpointRat_eq_natural a window 1)
  calc
    max (windowEndpointSquareUpperRat a window 0)
          (windowEndpointSquareUpperRat a window 1) +
        361 / 40000000000 <=
      max ((moment235EndpointNumerator a window 0 : Rat) /
            moment235EndpointDenominator)
          ((moment235EndpointNumerator a window 1 : Rat) /
            moment235EndpointDenominator) +
        361 / 40000000000 := by
      exact add_le_add (max_le_max hzero hone) le_rfl
    _ = (moment235CellNumerator a window : Rat) /
          moment235EndpointDenominator := by
      rw [moment235CellCorrection_eq_numerator,
        max_div_div_right]
      · rw [moment235CellNumerator]
        push_cast
        ring
      · exact_mod_cast moment235EndpointDenominator_pos.le

theorem oneSidedWindowMajorant_four_sq_le_moment235Cell
    (a : Fin 10) (window : Fin 5 -> Fin 10) :
    oneSidedWindowMajorant a 4 window ^ 2 <=
      (moment235CellNumerator a window : Real) /
        moment235EndpointDenominator := by
  apply (oneSidedWindowMajorant_four_sq_le_windowCellSquareUpperRat
    a window).trans
  have hcast := Rat.cast_mono (K := Real)
    (windowCellSquareUpperRat_le_moment235Cell a window)
  simpa using hcast

end PrimesRestrictedDigits
