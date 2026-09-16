import PrimesRestrictedDigits.Fourier.DyadicHornerCertificate
import PrimesRestrictedDigits.Fourier.ScaledNaturalCertificate

/-!
# Horner bounds as natural edge weights

Cached natural Horner numerators over a common denominator discharge the
analytic edge hypothesis of the scaled sparse certificate.
-/

namespace PrimesRestrictedDigits

theorem poweredWindowMajorant_le_naturalWindowWeight_of_horner
    (a : Fin 10) (J : ℕ) (t : ℝ) (bits : List Bool)
    (D : ℕ) (hD : 0 < D)
    (c p : (Fin (J + 1) → Fin 10) → ℕ)
    (hc : ∀ window, 0 < c window)
    (hsquare : ∀ window,
      oneSidedWindowMajorant a J window ^ 2 ≤ (c window : ℝ) / D)
    (hexponent : 2 * dyadicExponent bits ≤ t)
    (hnum : ∀ window, hornerNum D (c window) bits ≤ p window) :
    ∀ window,
      poweredWindowMajorantWeight a J t window ≤
        naturalWindowWeight D p window := by
  intro window
  have hhorner := rpow_le_hornerValue_of_sq_le D (c window) hD (hc window)
    (oneSidedWindowMajorant a J window) t bits
    (oneSidedWindowMajorant_nonneg a J window)
    (oneSidedWindowMajorant_le_one a J window)
    (hsquare window) hexponent
  exact hhorner.trans (by
    unfold hornerValue naturalWindowWeight
    gcongr
    exact_mod_cast hnum window)

end PrimesRestrictedDigits
