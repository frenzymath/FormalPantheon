import PrimesRestrictedDigits.Fourier.PositiveMoment

/-!
# Conditional certificate continuation

An explicit entrywise upper matrix and positive subeigenvector certificate turn
the exact positive-moment row bound into a geometric bound. The certificate
data itself remains a separate, kernel-checked obligation.
-/

open scoped BigOperators Matrix

namespace PrimesRestrictedDigits

theorem positiveMomentFrequencySum_le_certificate
    (a : Fin 10) (length J : ℕ) (t : ℝ) (ht : 0 < t)
    (upper : Matrix (DigitWindowState J) (DigitWindowState J) ℝ)
    (vector : DigitWindowState J → ℝ) (rho : ℝ)
    (hupper : ∀ i j,
      digitWindowTransitionMatrix J (poweredWindowMajorantWeight a J t) i j ≤
        upper i j)
    (hvector : ∀ i, 1 ≤ vector i) (hrho : 0 ≤ rho)
    (hsub :
      (upper *ᵥ vector) ≤ rho • vector) :
    (∑ frequency : Fin (10 ^ length),
      normalizedPaddedDigitFourierMagnitude a length frequency.val ^ t) ≤
      rho ^ length * vector (fun _ : Fin J => 0) := by
  let matrix : Matrix (DigitWindowState J) (DigitWindowState J) ℝ :=
    digitWindowTransitionMatrix J (poweredWindowMajorantWeight a J t)
  have hweight : ∀ window : Fin (J + 1) → Fin 10,
      0 ≤ poweredWindowMajorantWeight a J t window := by
    intro window
    exact Real.rpow_nonneg (oneSidedWindowMajorant_nonneg a J window) t
  have hmatrix : ∀ i j, 0 ≤ matrix i j := by
    intro i j
    exact digitWindowTransitionMatrix_nonneg J _ hweight i j
  have hrow := positiveMomentFrequencySum_le_transitionRowSum a length J t ht
  change
    (∑ frequency : Fin (10 ^ length),
      normalizedPaddedDigitFourierMagnitude a length frequency.val ^ t) ≤
      ∑ previous : DigitWindowState J,
        (matrix ^ length) (fun _ : Fin J => 0) previous at hrow
  calc
    (∑ frequency : Fin (10 ^ length),
        normalizedPaddedDigitFourierMagnitude a length frequency.val ^ t) ≤
        ∑ previous : DigitWindowState J,
          (matrix ^ length) (fun _ : Fin J => 0) previous := hrow
    _ ≤ rho ^ length * vector (fun _ : Fin J => 0) := by
      exact rowSum_pow_le_of_entrywise_upper_subEigen
        hmatrix hupper hvector hrho hsub length (fun _ : Fin J => 0)

theorem positiveMomentFrequencySum_le_certificate_rpow
    (a : Fin 10) (length J : ℕ) (t alpha : ℝ) (ht : 0 < t)
    (upper : Matrix (DigitWindowState J) (DigitWindowState J) ℝ)
    (vector : DigitWindowState J → ℝ) (rho : ℝ)
    (hupper : ∀ i j,
      digitWindowTransitionMatrix J (poweredWindowMajorantWeight a J t) i j ≤
        upper i j)
    (hvector : ∀ i, 1 ≤ vector i) (hrho : 0 ≤ rho)
    (hsub :
      (upper *ᵥ vector) ≤ rho • vector)
    (hrho_alpha : rho ≤ (10 : ℝ) ^ alpha) :
    (∑ frequency : Fin (10 ^ length),
      normalizedPaddedDigitFourierMagnitude a length frequency.val ^ t) ≤
      ((10 ^ length : ℕ) : ℝ) ^ alpha * vector (fun _ : Fin J => 0) := by
  have hcertificate := positiveMomentFrequencySum_le_certificate
    a length J t ht upper vector rho hupper hvector hrho hsub
  have hpow : rho ^ length ≤ ((10 : ℝ) ^ alpha) ^ length := by
    exact pow_le_pow_left₀ hrho hrho_alpha length
  have hvector_zero : 0 ≤ vector (fun _ : Fin J => 0) := by
    exact zero_le_one.trans (hvector _)
  have hmul : rho ^ length * vector (fun _ : Fin J => 0) ≤
      ((10 : ℝ) ^ alpha) ^ length * vector (fun _ : Fin J => 0) :=
    mul_le_mul_of_nonneg_right hpow hvector_zero
  have hscale : ((10 : ℝ) ^ alpha) ^ length =
      ((10 ^ length : ℕ) : ℝ) ^ alpha := by
    calc
      ((10 : ℝ) ^ alpha) ^ length =
          ((10 : ℝ) ^ alpha) ^ (length : ℝ) := by
            rw [Real.rpow_natCast]
      _ = (10 : ℝ) ^ (alpha * (length : ℝ)) := by
            rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10)]
      _ = ((10 : ℝ) ^ (length : ℝ)) ^ alpha := by
            rw [mul_comm, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10)]
      _ = ((10 ^ length : ℕ) : ℝ) ^ alpha := by
            norm_num [Nat.cast_pow, Real.rpow_natCast]
  calc
    (∑ frequency : Fin (10 ^ length),
        normalizedPaddedDigitFourierMagnitude a length frequency.val ^ t) ≤
        rho ^ length * vector (fun _ : Fin J => 0) := hcertificate
    _ ≤ ((10 : ℝ) ^ alpha) ^ length * vector (fun _ : Fin J => 0) := hmul
    _ = ((10 ^ length : ℕ) : ℝ) ^ alpha * vector (fun _ : Fin J => 0) := by
      rw [hscale]

end PrimesRestrictedDigits
