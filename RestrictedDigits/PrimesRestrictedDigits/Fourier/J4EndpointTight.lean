import PrimesRestrictedDigits.Fourier.KernelCurvature
import PrimesRestrictedDigits.Fourier.MajorantSquare
import PrimesRestrictedDigits.Fourier.PositiveMoment
import Mathlib.Tactic.NormNum

/-!
# Tight J=4 endpoint certificates

The exact frequency-sum curvature bound reduces the one-sided five-digit cell error to
`361/40000000000`. These declarations intentionally coexist with the coarser interface.
-/

namespace PrimesRestrictedDigits

private theorem digitKernel_sq_le_four_endpoint_bound_tight
    (a : Fin 10) (window : Fin 5 → Fin 10)
    (gamma : Set.Icc (0 : ℝ) (1 / (10 : ℝ) ^ (4 + 1))) :
    digitKernel a (digitWindowArgument 4 window + gamma) ^ 2 ≤
      max (digitKernel a (digitWindowArgument 4 window) ^ 2)
          (digitKernel a (digitWindowArgument 4 window + 1 / 100000) ^ 2) +
        361 / 40000000000 := by
  have hwidth : (1 / (10 : ℝ) ^ (4 + 1)) = 1 / 100000 := by
    norm_num
  have hgamma0 : (0 : ℝ) ≤ gamma := gamma.2.1
  have hgammaUpper : (gamma : ℝ) ≤ 1 / 100000 := by
    rw [← hwidth]
    exact gamma.2.2
  have hx : digitWindowArgument 4 window + gamma ∈
      Set.Icc (digitWindowArgument 4 window)
        (digitWindowArgument 4 window + 1 / 100000) := by
    constructor
    · exact le_add_of_nonneg_right hgamma0
    · exact add_le_add_right hgammaUpper _
  exact digitKernel_sq_le_cell_endpoints_tight a
    (digitWindowArgument 4 window) (digitWindowArgument 4 window + gamma) hx

theorem oneSidedWindowMajorant_four_le_of_endpoint_sq_tight
    (a : Fin 10) (window : Fin 5 → Fin 10) (q : ℝ)
    (hq : 0 ≤ q)
    (hendpoints :
      max (digitKernel a (digitWindowArgument 4 window) ^ 2)
          (digitKernel a (digitWindowArgument 4 window + 1 / 100000) ^ 2) +
        361 / 40000000000 ≤ q ^ 2) :
    oneSidedWindowMajorant a 4 window ≤ q := by
  apply oneSidedWindowMajorant_le_of_sq_le a 4 window q hq
  intro gamma
  exact (digitKernel_sq_le_four_endpoint_bound_tight a window gamma).trans hendpoints

theorem poweredWindowMajorant_four_le_of_endpoint_sq_tight
    (a : Fin 10) (window : Fin 5 → Fin 10) (q exponent : ℝ)
    (hq : 0 ≤ q) (hexponent : 0 < exponent)
    (hendpoints :
      max (digitKernel a (digitWindowArgument 4 window) ^ 2)
          (digitKernel a (digitWindowArgument 4 window + 1 / 100000) ^ 2) +
        361 / 40000000000 ≤ q ^ 2) :
    poweredWindowMajorantWeight a 4 exponent window ≤ q ^ exponent := by
  exact poweredWindowMajorant_le_of_sq_le a 4 window q exponent hq hexponent
    (fun gamma =>
      (digitKernel_sq_le_four_endpoint_bound_tight a window gamma).trans hendpoints)

end PrimesRestrictedDigits
