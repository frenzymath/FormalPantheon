import BoundedGaps.Maynard.LevelSelection
import Mathlib.Data.Nat.Totient

/-!
# Maynard's real cutoff and main-term scale

The source uses `R = N^(theta/2-delta)` in the asymptotic main terms. This
module records the exact real logarithm identity and positivity of the common
normalization, while leaving natural floor and modulus-cutoff comparisons
explicit elsewhere.
-/

namespace BoundedGaps.Maynard

noncomputable def maynardRealCutoff (alpha : ℝ) (N : ℕ) : ℝ :=
  Real.rpow (N : ℝ) alpha

theorem maynardRealCutoff_gt_one {alpha : ℝ} {N : ℕ}
    (hN : 1 < N) (halpha : 0 < alpha) :
    1 < maynardRealCutoff alpha N := by
  unfold maynardRealCutoff
  apply Real.one_lt_rpow
  · exact_mod_cast hN
  · exact halpha

theorem log_maynardRealCutoff_div_log {alpha : ℝ} {N : ℕ} (hN : 1 < N) :
    Real.log (maynardRealCutoff alpha N) / Real.log (N : ℝ) = alpha := by
  unfold maynardRealCutoff
  change Real.log ((N : ℝ) ^ alpha) / Real.log (N : ℝ) = alpha
  have hNreal : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [Real.log_rpow (by positivity)]
  exact mul_div_cancel_right₀ alpha (ne_of_gt (Real.log_pos hNreal))

noncomputable def maynardSieveScale (k W N : ℕ) (R : ℝ) : ℝ :=
  ((Nat.totient W : ℝ) ^ k * (N : ℝ) * (Real.log R) ^ k) /
    (W : ℝ) ^ (k + 1)

theorem maynardSieveScale_pos {k W N : ℕ} {R : ℝ}
    (hW : 0 < W) (hN : 0 < N) (hR : 1 < R) :
    0 < maynardSieveScale k W N R := by
  unfold maynardSieveScale
  have htot : 0 < (Nat.totient W : ℝ) := by
    exact_mod_cast (Nat.totient_pos.mpr hW)
  have hW' : 0 < (W : ℝ) := by exact_mod_cast hW
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  have hlog : 0 < Real.log R := Real.log_pos hR
  positivity

noncomputable def maynardDivisorCutoff (alpha : ℝ) (N : ℕ) : ℕ :=
  ⌊Real.rpow (N : ℝ) alpha⌋₊

theorem divisorPairProduct_le_modulusCutoff_of_real_bounds
    {theta eps alpha : ℝ} {N W R : ℕ}
    (hN : 1 ≤ N) (hsum : eps + 2 * alpha ≤ theta)
    (hW : (W : ℝ) ≤ Real.rpow (N : ℝ) eps)
    (hR : (R : ℝ) ≤ Real.rpow (N : ℝ) alpha) :
    W * R * R ≤ modulusCutoff theta N := by
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hRnonneg : 0 ≤ (R : ℝ) := by positivity
  have hNnonneg : 0 ≤ (N : ℝ) := by positivity
  have hNpos : 0 < (N : ℝ) := lt_of_lt_of_le zero_lt_one hNreal
  have hepspow : 0 ≤ Real.rpow (N : ℝ) eps :=
    Real.rpow_nonneg hNnonneg eps
  have halphapow : 0 ≤ Real.rpow (N : ℝ) alpha :=
    Real.rpow_nonneg hNnonneg alpha
  have hprod :
      (W : ℝ) * (R : ℝ) * (R : ℝ) ≤
        Real.rpow (N : ℝ) eps * Real.rpow (N : ℝ) alpha *
          Real.rpow (N : ℝ) alpha := by
    exact mul_le_mul (mul_le_mul hW hR hRnonneg hepspow) hR hRnonneg
      (mul_nonneg hepspow halphapow)
  have hpow :
      Real.rpow (N : ℝ) eps * Real.rpow (N : ℝ) alpha *
          Real.rpow (N : ℝ) alpha =
        Real.rpow (N : ℝ) (eps + 2 * alpha) := by
    change (N : ℝ) ^ eps * (N : ℝ) ^ alpha * (N : ℝ) ^ alpha =
      (N : ℝ) ^ (eps + 2 * alpha)
    calc
      (N : ℝ) ^ eps * (N : ℝ) ^ alpha * (N : ℝ) ^ alpha =
          (N : ℝ) ^ (eps + alpha) * (N : ℝ) ^ alpha := by
        rw [Real.rpow_add hNpos eps alpha]
      _ = (N : ℝ) ^ (eps + alpha + alpha) :=
        (Real.rpow_add hNpos (eps + alpha) alpha).symm
      _ = (N : ℝ) ^ (eps + 2 * alpha) := by ring_nf
  have hlepow :
      (W : ℝ) * (R : ℝ) * (R : ℝ) ≤ Real.rpow (N : ℝ) theta := by
    rw [hpow] at hprod
    exact hprod.trans (Real.rpow_le_rpow_of_exponent_le hNreal hsum)
  unfold modulusCutoff
  apply Nat.le_floor
  simpa only [Nat.cast_mul] using hlepow

theorem eventually_maynardDivisorCutoff_product_le_modulusCutoff
    {theta eps alpha : ℝ} {W : ℕ → ℕ}
    (hsum : eps + 2 * alpha ≤ theta)
    (hW : ∀ᶠ N : ℕ in Filter.atTop,
      (W N : ℝ) ≤ Real.rpow (N : ℝ) eps) :
    ∀ᶠ N : ℕ in Filter.atTop,
      W N * maynardDivisorCutoff alpha N * maynardDivisorCutoff alpha N ≤
        modulusCutoff theta N := by
  filter_upwards [hW, Filter.eventually_ge_atTop 1] with N hWN hN
  apply divisorPairProduct_le_modulusCutoff_of_real_bounds hN hsum hWN
  unfold maynardDivisorCutoff
  exact Nat.floor_le (Real.rpow_nonneg (by positivity) alpha)

end BoundedGaps.Maynard
