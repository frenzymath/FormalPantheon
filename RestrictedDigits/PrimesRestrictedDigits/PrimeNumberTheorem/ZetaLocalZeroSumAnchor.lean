import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaLocalZeros
import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaLocalZeroSumReal
import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaLogDerivativeRight

/-!
# The local zeta-zero sum at the right-hand anchor

This file proves the real-part estimate in `MONTGOMERY-VAUGHAN-MNT-I`,
Chapter 6, Theorem 6.7, Eq. (6.10).  The local sum retains the closed-disk
analytic multiplicities from Lemma 6.4.
-/

open Complex

namespace PrimesRestrictedDigits

/-- At `1 + 1 / log (|t| + 4) + I * t`, the real part of the local
multiplicity-weighted zero sum is bounded by an absolute constant times the
logarithmic height. -/
theorem exists_riemannZetaLocalZeroSum_anchor_bound :
    ∃ D : Real, 0 < D ∧
      ∀ t : Real, 7 / 8 ≤ |t| →
        (riemannZetaLocalZeroSum t
          ((((1 + 1 / Real.log (|t| + 4)) : Real) : Complex) +
            Complex.I * (t : Complex))).re ≤
          D * Real.log (|t| + 4) := by
  obtain ⟨A, hAPos, hRight⟩ := exists_riemannZeta_logDeriv_right_bound
  obtain ⟨C, hCPos, hLocal⟩ := riemannZeta_logDeriv_localZeroSum_bound
  refine ⟨A + C, add_pos hAPos hCPos, ?_⟩
  intro t hT
  let L : Real := Real.log (|t| + 4)
  let sigma : Real := 1 + 1 / L
  let s : Complex := (sigma : Complex) + Complex.I * t
  have hLOne : 1 < L := by
    dsimp [L]
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    exact Real.exp_one_lt_three.trans (by linarith [abs_nonneg t])
  have hLPos : 0 < L := zero_lt_one.trans hLOne
  have hInvPos : 0 < 1 / L := by positivity
  have hInvLe : 1 / L ≤ 1 := (div_le_one hLPos).2 hLOne.le
  have hSigmaOne : 1 < sigma := by
    dsimp [sigma]
    linarith
  have hSigmaLower : 5 / 6 ≤ sigma := by linarith
  have hSigmaUpper : sigma ≤ 2 := by
    dsimp [sigma]
    linarith
  have hs : riemannZeta s ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_le_re
    simpa [s] using hSigmaOne.le
  have hRightAt := hRight t sigma (by simp [sigma, L])
  change norm (logDeriv riemannZeta s) ≤ A * L at hRightAt
  have hLocalAt :=
    hLocal t sigma hT hSigmaLower hSigmaUpper hs
  change norm
      (logDeriv riemannZeta s - riemannZetaLocalZeroSum t s) ≤
    C * L at hLocalAt
  have hAggregate :
      (riemannZetaLocalZeroSum t s).re ≤
        norm (logDeriv riemannZeta s) +
          norm (logDeriv riemannZeta s - riemannZetaLocalZeroSum t s) := by
    have hMainRe := Complex.re_le_norm (logDeriv riemannZeta s)
    have hErrorRe := neg_le_of_abs_le (Complex.abs_re_le_norm
      (logDeriv riemannZeta s - riemannZetaLocalZeroSum t s))
    have hIdentity :
        (riemannZetaLocalZeroSum t s).re =
          (logDeriv riemannZeta s).re -
            (logDeriv riemannZeta s - riemannZetaLocalZeroSum t s).re := by
      simp
    rw [hIdentity]
    linarith
  change (riemannZetaLocalZeroSum t s).re ≤ (A + C) * L
  calc
    (riemannZetaLocalZeroSum t s).re ≤
        norm (logDeriv riemannZeta s) +
          norm (logDeriv riemannZeta s - riemannZetaLocalZeroSum t s) :=
      hAggregate
    _ ≤ A * L + C * L := add_le_add hRightAt hLocalAt
    _ = (A + C) * L := by ring

end PrimesRestrictedDigits
