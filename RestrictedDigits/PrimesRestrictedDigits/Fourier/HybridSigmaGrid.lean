import PrimesRestrictedDigits.Fourier.GridCircleSpacing
import PrimesRestrictedDigits.Fourier.LargeSieveSampling

/-!
# Exact complete-grid estimates for the alternative hybrid bound

The source's `Sigma_2` and `Sigma_4` grids contain exactly the residues in `Fin q`, without
the duplicated endpoint in the printed Lemma 10.5 carrier.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

/-- The repaired large-sieve sampling estimate on the exact complete
positive-modulus grid. -/
theorem completeFinGrid_largeSieveSampling
    (digit : Fin 10) (length q : Nat) (hq : 0 < q)
    {delta : Real} (hdelta : 0 ≤ delta) (beta : Real) :
    (∑ a : Fin q, closedWindowMaximum
      (normalizedPaddedDigitFourierMagnitudeAt digit length) delta
        ((a.val : Real) / q + beta)) ≤
      largeSieveSamplingConstant * (1 + delta * q) *
        ((q : Real) ^ largeSieveAlpha +
          (q : Real) *
            (((10 ^ length : Nat) : Real) ^ (-largeSieveSigma))) := by
  have hqReal : (1 : Real) ≤ q := by exact_mod_cast hq
  have hseparated :
      ∀ a ∈ (Finset.univ : Finset (Fin q)),
        ∀ b ∈ (Finset.univ : Finset (Fin q)), a ≠ b →
          1 / (q : Real) ≤
            dist ((((a.val : Real) / q : Real)) : UnitAddCircle)
              ((((b.val : Real) / q : Real)) : UnitAddCircle) := by
    intro a ha b hb hab
    exact one_div_natCast_le_dist_fin_div hq hab
  simpa using
    sum_closedWindowMaximum_normalizedPaddedDigitFourierMagnitudeAt_le
      (Finset.univ : Finset (Fin q)) digit length
      (fun a : Fin q => (a.val : Real) / q) hqReal hdelta hseparated beta

/-- If the complete grid lies below the transform scale and the window
density is bounded by `K`, both sampler terms are bounded by the same
`q^(27/77)` power. -/
theorem completeFinGrid_largeSieveSampling_le_power
    (digit : Fin 10) (length q : Nat) (hq : 0 < q)
    (hqY : q ≤ 10 ^ length) {delta K : Real} (hdelta : 0 ≤ delta)
    (hK : 0 ≤ K) (hdeltaq : delta * q ≤ K) (beta : Real) :
    (∑ a : Fin q, closedWindowMaximum
      (normalizedPaddedDigitFourierMagnitudeAt digit length) delta
        ((a.val : Real) / q + beta)) ≤
      2 * largeSieveSamplingConstant * (1 + K) *
        (q : Real) ^ largeSieveAlpha := by
  have hq0 : (0 : Real) < q := by exact_mod_cast hq
  have hqYReal : (q : Real) ≤ ((10 ^ length : Nat) : Real) := by
    exact_mod_cast hqY
  have hpowNeg :
      (((10 ^ length : Nat) : Real) ^ (-largeSieveSigma)) ≤
        (q : Real) ^ (-largeSieveSigma) := by
    exact Real.rpow_le_rpow_of_nonpos hq0 hqYReal
      (neg_nonpos.mpr largeSieveSigma_nonneg)
  have hcombine :
      (q : Real) * (q : Real) ^ (-largeSieveSigma) =
        (q : Real) ^ largeSieveAlpha := by
    calc
      (q : Real) * (q : Real) ^ (-largeSieveSigma) =
          (q : Real) ^ (1 : Real) * (q : Real) ^ (-largeSieveSigma) := by
        rw [Real.rpow_one]
      _ = (q : Real) ^ ((1 : Real) + (-largeSieveSigma)) :=
        (Real.rpow_add hq0 _ _).symm
      _ = (q : Real) ^ largeSieveAlpha := by
        congr 1
        norm_num [largeSieveAlpha, largeSieveSigma]
  have htail :
      (q : Real) *
          (((10 ^ length : Nat) : Real) ^ (-largeSieveSigma)) ≤
        (q : Real) ^ largeSieveAlpha := by
    calc
      _ ≤ (q : Real) * (q : Real) ^ (-largeSieveSigma) :=
        mul_le_mul_of_nonneg_left hpowNeg hq0.le
      _ = _ := hcombine
  have hpower0 : 0 ≤ (q : Real) ^ largeSieveAlpha :=
    Real.rpow_nonneg hq0.le _
  have hsum :
      (q : Real) ^ largeSieveAlpha +
          (q : Real) *
            (((10 ^ length : Nat) : Real) ^ (-largeSieveSigma)) ≤
        2 * (q : Real) ^ largeSieveAlpha := by
    linarith
  have hsum0 :
      0 ≤ (q : Real) ^ largeSieveAlpha +
        (q : Real) *
          (((10 ^ length : Nat) : Real) ^ (-largeSieveSigma)) := by
    positivity
  have hconstant : 0 ≤ largeSieveSamplingConstant := by
    unfold largeSieveSamplingConstant
    norm_num
  have hsample :=
    completeFinGrid_largeSieveSampling digit length q hq hdelta beta
  calc
    _ ≤ largeSieveSamplingConstant * (1 + delta * q) *
        ((q : Real) ^ largeSieveAlpha +
          (q : Real) *
            (((10 ^ length : Nat) : Real) ^ (-largeSieveSigma))) :=
      hsample
    _ ≤ largeSieveSamplingConstant * (1 + K) *
        ((q : Real) ^ largeSieveAlpha +
          (q : Real) *
            (((10 ^ length : Nat) : Real) ^ (-largeSieveSigma))) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith) hconstant) hsum0
    _ ≤ largeSieveSamplingConstant * (1 + K) *
        (2 * (q : Real) ^ largeSieveAlpha) := by
      exact mul_le_mul_of_nonneg_left hsum
        (mul_nonneg hconstant (by linarith))
    _ = 2 * largeSieveSamplingConstant * (1 + K) *
        (q : Real) ^ largeSieveAlpha := by ring

end

end PrimesRestrictedDigits
