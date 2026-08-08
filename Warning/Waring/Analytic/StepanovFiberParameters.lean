import Waring.Analytic.StepanovDegreeSeparation

/-!
# Degree and trace-fiber parameters for the Stepanov construction

The total auxiliary degree is an exact multiple of the derivative count.
The quotient separates into the expected average trace-fiber size and an
error of square-root order in the even extension degree.
 -/

namespace Waring.Analytic

namespace Stepanov

/-- A strict upper bound for the degree of the full auxiliary polynomial. -/
def auxiliaryDegreeBound (p h d : Nat) : Nat :=
  S p h + degreeBase p h * (d * (p - 1) + p * K p h)

/-- The resulting upper bound for one full-trace fiber. -/
def traceFiberBound (p h d : Nat) : Nat :=
  degreeBase p h + d * (p - 1) * p ^ (h + 4) + p ^ (h + 3)

/-- The auxiliary degree bound is exactly the derivative count times the
trace-fiber bound. -/
theorem auxiliaryDegreeBound_eq_R_mul_traceFiberBound
    (p h d : Nat) :
    auxiliaryDegreeBound p h d = R p h * traceFiberBound p h d := by
  simp only [auxiliaryDegreeBound, traceFiberBound, S, R, K, degreeBase]
  rw [show p ^ (2 * h + 4) = p ^ (h + 1) * p ^ (h + 3) by
      rw [← pow_add]; congr 1; omega]
  rw [show p ^ (2 * h + 5) = p ^ (h + 1) * p ^ (h + 4) by
      rw [← pow_add]; congr 1; omega]
  rw [show p * p ^ h = p ^ (h + 1) by
      rw [show h + 1 = 1 + h by omega, pow_add, pow_one]]
  ring

/-- The error above the average fiber size is a fixed coefficient times
`p ^ (h + 3)`, the square root of the extension cardinality. -/
theorem traceFiberBound_eq_average_add_error (p h d : Nat) :
    traceFiberBound p h d =
      degreeBase p h + (d * (p - 1) * p + 1) * p ^ (h + 3) := by
  simp only [traceFiberBound]
  rw [show p ^ (h + 4) = p * p ^ (h + 3) by
      rw [show h + 4 = 1 + (h + 3) by omega, pow_add, pow_one]]
  ring

/-- The average-fiber term is `p ^ (2 * m - 1)` for `m = h + 3`. -/
theorem degreeBase_eq_even_extension_divisor (p h : Nat) :
    degreeBase p h = p ^ (2 * (h + 3) - 1) := by
  simp only [degreeBase]
  congr 1

end Stepanov

end Waring.Analytic
