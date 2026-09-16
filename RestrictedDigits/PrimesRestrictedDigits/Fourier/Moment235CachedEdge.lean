import PrimesRestrictedDigits.Fourier.Moment235CachedEndpoint

/-!
# Cached natural powered edge weights

The cached cell numerator is rounded upward over an arbitrary positive natural
denominator and passed through the established dyadic Horner construction.
-/

namespace PrimesRestrictedDigits

def moment235SquareNumerator
    (D : Nat) (a : Fin 10) (window : Fin 5 -> Fin 10) : Nat :=
  (D * moment235CellNumerator a window) ⌈/⌉
      moment235EndpointDenominator + 1

def moment235PoweredNumerator
    (D : Nat) (a : Fin 10) (window : Fin 5 -> Fin 10) : Nat :=
  hornerNum D (moment235SquareNumerator D a window) betaBits30

theorem moment235SquareNumerator_pos
    (D : Nat) (a : Fin 10) (window : Fin 5 -> Fin 10) :
    0 < moment235SquareNumerator D a window := by
  unfold moment235SquareNumerator
  omega

theorem oneSidedWindowMajorant_four_sq_le_moment235SquareNumerator
    (D : Nat) (hD : 0 < D) (a : Fin 10)
    (window : Fin 5 -> Fin 10) :
    oneSidedWindowMajorant a 4 window ^ 2 <=
      (moment235SquareNumerator D a window : Real) / D := by
  apply (oneSidedWindowMajorant_four_sq_le_moment235Cell a window).trans
  have hceil :
      D * moment235CellNumerator a window <=
        ((D * moment235CellNumerator a window) ⌈/⌉
          moment235EndpointDenominator) * moment235EndpointDenominator := by
    simpa [mul_comm] using
      (le_smul_ceilDiv (β := Nat) moment235EndpointDenominator_pos
        (b := D * moment235CellNumerator a window))
  have hnat :
      moment235CellNumerator a window * D <=
        moment235SquareNumerator D a window *
          moment235EndpointDenominator := by
    calc
      moment235CellNumerator a window * D =
          D * moment235CellNumerator a window := mul_comm _ _
      _ <= ((D * moment235CellNumerator a window) ⌈/⌉
            moment235EndpointDenominator) *
          moment235EndpointDenominator := hceil
      _ <= (((D * moment235CellNumerator a window) ⌈/⌉
              moment235EndpointDenominator) + 1) *
          moment235EndpointDenominator := by
        exact Nat.mul_le_mul_right moment235EndpointDenominator
          (Nat.le_succ _)
      _ = moment235SquareNumerator D a window *
          moment235EndpointDenominator := by
        rfl
  rw [div_le_div_iff₀]
  · exact_mod_cast hnat
  · exact_mod_cast moment235EndpointDenominator_pos
  · exact_mod_cast hD

/-- Every source-exponent `J=4` edge is bounded by the cached natural
numerator over the chosen positive denominator. -/
theorem poweredWindowMajorant_four_le_moment235NaturalWeight
    (D : Nat) (hD : 0 < D) (a : Fin 10) :
    forall window : Fin 5 -> Fin 10,
      poweredWindowMajorantWeight a 4 (235 / 154 : Real) window <=
        naturalWindowWeight D (moment235PoweredNumerator D a) window := by
  apply poweredWindowMajorant_le_naturalWindowWeight_of_horner
    a 4 (235 / 154 : Real) betaBits30 D hD
      (moment235SquareNumerator D a) (moment235PoweredNumerator D a)
  · exact moment235SquareNumerator_pos D a
  · exact oneSidedWindowMajorant_four_sq_le_moment235SquareNumerator D hD a
  · exact two_mul_dyadicExponent_betaBits30_le
  · intro window
    exact le_rfl

end PrimesRestrictedDigits
