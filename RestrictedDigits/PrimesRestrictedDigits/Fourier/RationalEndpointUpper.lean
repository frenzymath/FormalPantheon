import PrimesRestrictedDigits.Fourier.DifferenceCount
import PrimesRestrictedDigits.Fourier.J4EndpointTight
import PrimesRestrictedDigits.Fourier.WindowPhaseCertificate

/-!
# Computable rational endpoint uppers

The established d20 Taylor certificate and signed-difference table are
mirrored exactly in `Rat`, producing a computable upper bound for every J=4
cell without generated trigonometric proof data.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

def cosinePolynomial20UpperRat (lo hi : Rat) : Rat :=
  1 - lo / 2 + hi ^ 2 / 24 - lo ^ 3 / 720 + hi ^ 4 / 40320 -
    lo ^ 5 / 3628800 + hi ^ 6 / 479001600 - lo ^ 7 / 87178291200 +
    hi ^ 8 / 20922789888000 - lo ^ 9 / 6402373705728000

def rationalCosineUpper20D20Rat (r : Rat) : Rat :=
  cosinePolynomial20UpperRat
      (4 * (314159265358979323846 / 100000000000000000000 : Rat) ^ 2 * r ^ 2)
      (4 * (314159265358979323847 / 100000000000000000000 : Rat) ^ 2 * r ^ 2) +
    1 / 100000000

theorem rationalCosineUpper20D20Rat_cast (r : Rat) :
    (rationalCosineUpper20D20Rat r : Real) =
      rationalCosineUpper20D20 r := by
  rw [rationalCosineUpper20D20Rat, rationalCosineUpper20D20,
    cosinePolynomial20UpperRat, cosinePolynomial20Upper]
  push_cast
  ring

def signedDifferencePhaseTermRat
    (window : Fin 5 -> Fin 10) (offset : Int) (k : Fin 19) : Rat :=
  rationalCosineUpper20D20Rat
    (centeredRationalPart
      (signedDifference k * (digitWindowNumeratorFour window + offset)) 100000)

theorem signedDifferencePhaseTermRat_cast
    (window : Fin 5 -> Fin 10) (offset : Int) (k : Fin 19) :
    (signedDifferencePhaseTermRat window offset k : Real) =
      signedDifferencePhaseTerm window offset k := by
  simp only [signedDifferencePhaseTermRat, signedDifferencePhaseTerm,
    rationalCosineUpper20D20Rat_cast]

def windowEndpointSquareUpperRat
    (a : Fin 10) (window : Fin 5 -> Fin 10) (offset : Int) : Rat :=
  (1 / 81 : Rat) *
    ∑ k : Fin 19, (signedDifferenceCountTable a k : Rat) *
      signedDifferencePhaseTermRat window offset k

theorem windowEndpointSquareUpperRat_cast
    (a : Fin 10) (window : Fin 5 -> Fin 10) (offset : Int) :
    (windowEndpointSquareUpperRat a window offset : Real) =
      (1 / 81 : Real) *
        (∑ d ∈ allowedDecimalDigits a, ∑ e ∈ allowedDecimalDigits a,
          rationalCosineUpper20D20 (windowPhase window offset d e)) := by
  rw [windowEndpointSquareUpperRat]
  push_cast
  rw [windowPhaseCosineSum_eq_signedDifferenceTable]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [signedDifferencePhaseTermRat_cast]

theorem digitKernel_sq_le_windowEndpointSquareUpperRat
    (a : Fin 10) (window : Fin 5 -> Fin 10) (offset : Int) :
    digitKernel a
        (((digitWindowNumeratorFour window + offset : Int) : Real) / 100000) ^ 2 <=
      (windowEndpointSquareUpperRat a window offset : Real) := by
  apply digitKernel_sq_le_of_window_phase_sum
  rw [windowEndpointSquareUpperRat_cast]

theorem digitKernel_left_sq_le_windowEndpointSquareUpperRat
    (a : Fin 10) (window : Fin 5 -> Fin 10) :
    digitKernel a (digitWindowArgument 4 window) ^ 2 <=
      (windowEndpointSquareUpperRat a window 0 : Real) := by
  rw [digitWindowArgument_four_eq_numerator]
  simpa using digitKernel_sq_le_windowEndpointSquareUpperRat a window 0

theorem digitKernel_right_sq_le_windowEndpointSquareUpperRat
    (a : Fin 10) (window : Fin 5 -> Fin 10) :
    digitKernel a (digitWindowArgument 4 window + 1 / 100000) ^ 2 <=
      (windowEndpointSquareUpperRat a window 1 : Real) := by
  rw [digitWindowArgument_four_add_cell_eq_numerator]
  exact digitKernel_sq_le_windowEndpointSquareUpperRat a window 1

def windowCellSquareUpperRat
    (a : Fin 10) (window : Fin 5 -> Fin 10) : Rat :=
  max (windowEndpointSquareUpperRat a window 0)
      (windowEndpointSquareUpperRat a window 1) +
    361 / 40000000000

theorem windowCellSquareUpperRat_cast
    (a : Fin 10) (window : Fin 5 -> Fin 10) :
    (windowCellSquareUpperRat a window : Real) =
      max (windowEndpointSquareUpperRat a window 0 : Real)
          (windowEndpointSquareUpperRat a window 1 : Real) +
        361 / 40000000000 := by
  rw [windowCellSquareUpperRat]
  push_cast
  rfl

theorem oneSidedWindowMajorant_four_sq_le_windowCellSquareUpperRat
    (a : Fin 10) (window : Fin 5 -> Fin 10) :
    oneSidedWindowMajorant a 4 window ^ 2 <=
      (windowCellSquareUpperRat a window : Real) := by
  have hleft := digitKernel_left_sq_le_windowEndpointSquareUpperRat a window
  have hright := digitKernel_right_sq_le_windowEndpointSquareUpperRat a window
  have hcell :
      max (digitKernel a (digitWindowArgument 4 window) ^ 2)
          (digitKernel a
            (digitWindowArgument 4 window + 1 / 100000) ^ 2) +
          361 / 40000000000 <=
        (windowCellSquareUpperRat a window : Real) := by
    rw [windowCellSquareUpperRat_cast]
    exact add_le_add_left (max_le_max hleft hright) _
  have hnonneg : 0 <= (windowCellSquareUpperRat a window : Real) := by
    have hsource : 0 <=
        max (digitKernel a (digitWindowArgument 4 window) ^ 2)
            (digitKernel a
              (digitWindowArgument 4 window + 1 / 100000) ^ 2) +
          361 / 40000000000 := by positivity
    exact hsource.trans hcell
  have hmajorant :
      oneSidedWindowMajorant a 4 window <=
        Real.sqrt (windowCellSquareUpperRat a window : Real) := by
    apply oneSidedWindowMajorant_four_le_of_endpoint_sq_tight
    · exact Real.sqrt_nonneg _
    · rw [Real.sq_sqrt hnonneg]
      exact hcell
  have hsquare := pow_le_pow_left₀
    (oneSidedWindowMajorant_nonneg a 4 window) hmajorant 2
  rwa [Real.sq_sqrt hnonneg] at hsquare

end PrimesRestrictedDigits
