import PrimesRestrictedDigits.Fourier.CertificateContinuation
import PrimesRestrictedDigits.Fourier.IncomingPath
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp

/-!
# Scaled natural sparse certificates

Natural edge and vector numerators over common positive scales provide the
exact sparse data interface for the conditional positive-moment certificate.
This file asserts no numerical certificate data.
-/

open scoped BigOperators Matrix

namespace PrimesRestrictedDigits

noncomputable def naturalWindowWeight {J : ℕ} (D : ℕ)
    (p : (Fin (J + 1) → Fin 10) → ℕ) :
    (Fin (J + 1) → Fin 10) → ℝ :=
  fun window => (p window : ℝ) / (D : ℝ)

noncomputable def naturalStateVector {J : ℕ} (S : ℕ)
    (z : DigitWindowState J → ℕ) : DigitWindowState J → ℝ :=
  fun state => (z state : ℝ) / (S : ℝ)

noncomputable def naturalRatio (R Q : ℕ) : ℝ :=
  (R : ℝ) / (Q : ℝ)

theorem naturalStateVector_one_le {J : ℕ} (S : ℕ) (hS : 0 < S)
    (z : DigitWindowState J → ℕ) (hz : ∀ state, S ≤ z state) :
    ∀ state, 1 ≤ naturalStateVector S z state := by
  intro state
  rw [naturalStateVector, one_le_div (by exact_mod_cast hS)]
  exact_mod_cast hz state

theorem digitWindowTransitionMatrix_mono {J : ℕ}
    {weight upper : (Fin (J + 1) → Fin 10) → ℝ}
    (h : ∀ window, weight window ≤ upper window) :
    ∀ future previous,
      digitWindowTransitionMatrix J weight future previous ≤
        digitWindowTransitionMatrix J upper future previous := by
  intro future previous
  unfold digitWindowTransitionMatrix
  apply Finset.sum_le_sum
  intro last hlast
  split_ifs
  · exact h _
  · exact le_rfl

theorem naturalWindowTransition_mulVec_le
    {J : ℕ} (D S R Q : ℕ) (hD : 0 < D) (hS : 0 < S) (hQ : 0 < Q)
    (p : (Fin (J + 1) → Fin 10) → ℕ)
    (z : DigitWindowState J → ℕ)
    (hrow : ∀ future,
      Q * (∑ first : Fin 10,
        p (prependDigitWindow first future) *
          z (digitWindowPrefix (prependDigitWindow first future))) ≤
        D * R * z future) :
    (digitWindowTransitionMatrix J (naturalWindowWeight D p) *ᵥ
        naturalStateVector S z) ≤
      naturalRatio R Q • naturalStateVector S z := by
  intro future
  rw [digitWindowTransitionMatrix_mulVec_eq_incoming]
  simp only [naturalWindowWeight, naturalStateVector, naturalRatio,
    Pi.smul_apply, smul_eq_mul]
  have hreal :
      (Q : ℝ) * (∑ first : Fin 10,
        (p (prependDigitWindow first future) : ℝ) *
          (z (digitWindowPrefix (prependDigitWindow first future)) : ℝ)) ≤
        (D : ℝ) * (R : ℝ) * (z future : ℝ) := by
    exact_mod_cast hrow future
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hSpos : (0 : ℝ) < S := by exact_mod_cast hS
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hsum :
      (∑ first : Fin 10,
        (p (prependDigitWindow first future) : ℝ) / D *
          ((z (digitWindowPrefix (prependDigitWindow first future)) : ℝ) / S)) =
        (∑ first : Fin 10,
          (p (prependDigitWindow first future) : ℝ) *
            (z (digitWindowPrefix (prependDigitWindow first future)) : ℝ)) /
          ((D : ℝ) * S) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro first hfirst
    field_simp
  rw [hsum]
  calc
    (∑ first : Fin 10,
        (p (prependDigitWindow first future) : ℝ) *
          (z (digitWindowPrefix (prependDigitWindow first future)) : ℝ)) /
        ((D : ℝ) * S) =
      ((∑ first : Fin 10,
          (p (prependDigitWindow first future) : ℝ) *
            (z (digitWindowPrefix (prependDigitWindow first future)) : ℝ)) / D) /
        S := by field_simp
    _ ≤ (((R : ℝ) * (z future : ℝ)) / Q) / S := by
      apply (div_le_div_iff_of_pos_right hSpos).2
      apply (div_le_div_iff₀ hDpos hQpos).2
      simpa [mul_assoc, mul_left_comm, mul_comm] using hreal
    _ = ((R : ℝ) / Q) * ((z future : ℝ) / S) := by field_simp

theorem positiveMomentFrequencySum_le_naturalCertificate
    (a : Fin 10) (length J : ℕ) (t : ℝ) (ht : 0 < t)
    (D S R Q : ℕ) (hD : 0 < D) (hS : 0 < S) (hQ : 0 < Q)
    (p : (Fin (J + 1) → Fin 10) → ℕ)
    (z : DigitWindowState J → ℕ)
    (hweight : ∀ window,
      poweredWindowMajorantWeight a J t window ≤
        naturalWindowWeight D p window)
    (hz : ∀ state, S ≤ z state)
    (hrow : ∀ future,
      Q * (∑ first : Fin 10,
        p (prependDigitWindow first future) *
          z (digitWindowPrefix (prependDigitWindow first future))) ≤
        D * R * z future) :
    (∑ frequency : Fin (10 ^ length),
      normalizedPaddedDigitFourierMagnitude a length frequency.val ^ t) ≤
      naturalRatio R Q ^ length *
        naturalStateVector S z (fun _ : Fin J => 0) := by
  apply positiveMomentFrequencySum_le_certificate
    a length J t ht
    (digitWindowTransitionMatrix J (naturalWindowWeight D p))
    (naturalStateVector S z) (naturalRatio R Q)
  · exact digitWindowTransitionMatrix_mono hweight
  · exact naturalStateVector_one_le S hS z hz
  · unfold naturalRatio
    positivity
  · exact naturalWindowTransition_mulVec_le D S R Q hD hS hQ p z hrow

end PrimesRestrictedDigits
