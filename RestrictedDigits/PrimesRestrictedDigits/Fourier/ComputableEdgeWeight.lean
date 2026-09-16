import PrimesRestrictedDigits.Fourier.BetaExponentCertificate
import PrimesRestrictedDigits.Fourier.HornerNaturalWeight
import PrimesRestrictedDigits.Fourier.RationalEndpointUpper

/-!
# Computable natural powered edge weights

An exact rational cell upper is rounded upward over one common natural
denominator and passed through the established dyadic Horner construction.
-/

namespace PrimesRestrictedDigits

def windowCellSquareNumerator
    (D : Nat) (a : Fin 10) (window : Fin 5 -> Fin 10) : Nat :=
  Nat.ceil ((D : Rat) * windowCellSquareUpperRat a window) + 1

def windowPoweredNumerator
    (D : Nat) (a : Fin 10) (window : Fin 5 -> Fin 10) : Nat :=
  hornerNum D (windowCellSquareNumerator D a window) betaBits30

theorem windowCellSquareNumerator_pos
    (D : Nat) (a : Fin 10) (window : Fin 5 -> Fin 10) :
    0 < windowCellSquareNumerator D a window := by
  unfold windowCellSquareNumerator
  omega

theorem oneSidedWindowMajorant_four_sq_le_naturalNumerator
    (D : Nat) (hD : 0 < D) (a : Fin 10) (window : Fin 5 -> Fin 10) :
    oneSidedWindowMajorant a 4 window ^ 2 <=
      (windowCellSquareNumerator D a window : Real) / D := by
  let q : Rat := windowCellSquareUpperRat a window
  have hDq : q <=
      (windowCellSquareNumerator D a window : Rat) / D := by
    apply (le_div_iff₀ (by exact_mod_cast hD : (0 : Rat) < D)).2
    calc
      q * (D : Rat) = (D : Rat) * q := mul_comm _ _
      _ <= (Nat.ceil ((D : Rat) * q) : Nat) := Nat.le_ceil _
      _ <= (windowCellSquareNumerator D a window : Nat) := by
        unfold windowCellSquareNumerator
        dsimp only [q]
        exact_mod_cast Nat.le_succ _
  have hreal : (q : Real) <=
      (windowCellSquareNumerator D a window : Real) / D := by
    have hcast := Rat.cast_mono (K := Real) hDq
    simpa using hcast
  exact (oneSidedWindowMajorant_four_sq_le_windowCellSquareUpperRat
    a window).trans (by simpa only [q] using hreal)

/-- Every J=4 powered edge at the source exponent is bounded by one
computable natural numerator over the chosen common positive denominator. -/
theorem poweredWindowMajorant_four_le_computableNaturalWeight
    (D : Nat) (hD : 0 < D) (a : Fin 10) :
    ∀ window : Fin 5 -> Fin 10,
      poweredWindowMajorantWeight a 4 (235 / 154 : Real) window <=
        naturalWindowWeight D (windowPoweredNumerator D a) window := by
  apply poweredWindowMajorant_le_naturalWindowWeight_of_horner
    a 4 (235 / 154 : Real) betaBits30 D hD
      (windowCellSquareNumerator D a) (windowPoweredNumerator D a)
  · exact windowCellSquareNumerator_pos D a
  · exact oneSidedWindowMajorant_four_sq_le_naturalNumerator D hD a
  · exact two_mul_dyadicExponent_betaBits30_le
  · intro window
    exact le_rfl

end PrimesRestrictedDigits
