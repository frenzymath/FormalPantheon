import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Scalar estimates for the high-rank Rosser seed

This file isolates the large-parameter arithmetic used by the independent finite-product
replacement for Iwaniec's Eq. (8.13).
-/

namespace PrimesRestrictedDigits

/-- The multiplicative moment tilt used in the high-rank seed. -/
noncomputable def dimensionOneRosserSeedTilt (s : Real) : Real :=
  s / (1024 * Real.log s)

/-- The elementary envelope left after reserving the density factor. -/
noncomputable def dimensionOneRosserSeedEnvelope (s : Real) : Real :=
  Real.exp (s * (4 - Real.log (dimensionOneRosserSeedTilt s)))

/-- The seed envelope is positive for every real argument. -/
theorem dimensionOneRosserSeedEnvelope_pos (s : Real) :
    0 < dimensionOneRosserSeedEnvelope s := by
  exact Real.exp_pos _

private theorem dimensionOneRosserSeed_large_data
    {s : Real} (hsLarge : Real.exp 5000 + 1 <= s) :
    0 < s /\ 5000 < Real.log s /\ 1025 * Real.log s < s := by
  have hExp : Real.exp 5000 < s := by linarith
  have hs : 0 < s := (Real.exp_pos (5000 : Real)).trans hExp
  have hLog : 5000 < Real.log s :=
    (Real.lt_log_iff_exp_lt hs).2 hExp
  have hLogSqrt : Real.log (Real.sqrt s) = Real.log s / 2 :=
    Real.log_sqrt hs.le
  have hSqrt : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hLogSqrtLarge : 2500 < Real.log (Real.sqrt s) := by
    rw [hLogSqrt]
    linarith
  have hExpLarge : (2501 : Real) < Real.exp 2500 := by
    have h := Real.add_one_lt_exp (x := (2500 : Real)) (by norm_num)
    norm_num at h ⊢
    exact h
  have hSqrtLarge : (2501 : Real) < Real.sqrt s :=
    hExpLarge.trans ((Real.lt_log_iff_exp_lt hSqrt).1 hLogSqrtLarge)
  have hLogLe : Real.log s <= 2 * Real.sqrt s := by
    have h := Real.log_le_rpow_div hs.le
      (by norm_num : (0 : Real) < 1 / 2)
    rw [<- Real.sqrt_eq_rpow] at h
    norm_num at h
    linarith
  have hSqrtProduct :
      0 < Real.sqrt s * (Real.sqrt s - 2050) :=
    mul_pos hSqrt (by linarith)
  have hSqrtSq : (Real.sqrt s) ^ 2 = s := Real.sq_sqrt hs.le
  refine ⟨hs, hLog, ?_⟩
  nlinarith

/-- The large seed threshold forces the parameter to be positive. -/
theorem dimensionOneRosserSeed_pos {s : Real}
    (hsLarge : Real.exp 5000 + 1 <= s) :
    0 < s :=
  (dimensionOneRosserSeed_large_data hsLarge).1

/-- The logarithm has a large explicit lower bound at the seed threshold. -/
theorem dimensionOneRosserSeed_log_gt {s : Real}
    (hsLarge : Real.exp 5000 + 1 <= s) :
    5000 < Real.log s :=
  (dimensionOneRosserSeed_large_data hsLarge).2.1

/-- The coarse logarithmic comparison used by both scalar reserves. -/
theorem dimensionOneRosserSeed_log_mul_lt {s : Real}
    (hsLarge : Real.exp 5000 + 1 <= s) :
    1025 * Real.log s < s :=
  (dimensionOneRosserSeed_large_data hsLarge).2.2

/-- The multiplicative seed tilt is positive on the large range. -/
theorem dimensionOneRosserSeedTilt_pos {s : Real}
    (hsLarge : Real.exp 5000 + 1 <= s) :
    0 < dimensionOneRosserSeedTilt s := by
  unfold dimensionOneRosserSeedTilt
  exact div_pos (dimensionOneRosserSeed_pos hsLarge)
    (mul_pos (by norm_num) (by linarith [dimensionOneRosserSeed_log_gt hsLarge]))

/-- The multiplicative seed tilt is strictly larger than one. -/
theorem one_lt_dimensionOneRosserSeedTilt {s : Real}
    (hsLarge : Real.exp 5000 + 1 <= s) :
    1 < dimensionOneRosserSeedTilt s := by
  have hLog : 0 < Real.log s := by
    linarith [dimensionOneRosserSeed_log_gt hsLarge]
  rw [dimensionOneRosserSeedTilt, lt_div_iff₀ (mul_pos (by norm_num) hLog)]
  linarith [dimensionOneRosserSeed_log_mul_lt hsLarge]

/-- The multiplicative seed tilt is at most its parameter. -/
theorem dimensionOneRosserSeedTilt_le {s : Real}
    (hsLarge : Real.exp 5000 + 1 <= s) :
    dimensionOneRosserSeedTilt s <= s := by
  have hs := (dimensionOneRosserSeed_pos hsLarge).le
  have hLog := dimensionOneRosserSeed_log_gt hsLarge
  have hDen : (1 : Real) <= 1024 * Real.log s := by linarith
  unfold dimensionOneRosserSeedTilt
  calc
    s / (1024 * Real.log s) <= s / 1 :=
      div_le_div_of_nonneg_left hs (by norm_num) hDen
    _ = s := div_one s

/-- The logarithm of the tilt is controlled by the logarithm of its
parameter. -/
theorem dimensionOneRosserSeed_log_tilt_le {s : Real}
    (hsLarge : Real.exp 5000 + 1 <= s) :
    Real.log (dimensionOneRosserSeedTilt s) <= Real.log s := by
  exact Real.strictMonoOn_log.monotoneOn
    (dimensionOneRosserSeedTilt_pos hsLarge)
    (dimensionOneRosserSeed_pos hsLarge)
    (dimensionOneRosserSeedTilt_le hsLarge)

/-- The tilted reciprocal-prime mass consumes at most two fifths of the
available linear exponent. -/
theorem dimensionOneRosserSeedTilt_mul_massBound_le
    {s : Real} (hsLarge : Real.exp 5000 + 1 <= s) :
    dimensionOneRosserSeedTilt s * (24 + 400 * Real.log s) <=
      (2 / 5 : Real) * s := by
  have hs : 0 < s := dimensionOneRosserSeed_pos hsLarge
  have hLog : 0 < Real.log s := by
    linarith [dimensionOneRosserSeed_log_gt hsLarge]
  have hDen : 0 < 1024 * Real.log s := mul_pos (by norm_num) hLog
  have hNumeric : (120 : Real) <= 48 * Real.log s := by
    linarith [dimensionOneRosserSeed_log_gt hsLarge]
  rw [dimensionOneRosserSeedTilt, div_mul_eq_mul_div,
    div_le_iff₀ hDen]
  nlinarith

/-- Three logarithms of the tilt fit in one half of the parameter. -/
theorem dimensionOneRosserSeed_three_log_tilt_lt
    {s : Real} (hsLarge : Real.exp 5000 + 1 <= s) :
    3 * Real.log (dimensionOneRosserSeedTilt s) < s / 2 := by
  have hLogTilt := dimensionOneRosserSeed_log_tilt_le hsLarge
  have hLogScale := dimensionOneRosserSeed_log_mul_lt hsLarge
  have hThree : 3 * Real.log (dimensionOneRosserSeedTilt s) <=
      3 * Real.log s :=
    mul_le_mul_of_nonneg_left hLogTilt (by norm_num)
  have hLogPos : 0 < Real.log s := by
    linarith [dimensionOneRosserSeed_log_gt hsLarge]
  have hSix : 6 * Real.log s < s := by
    exact (mul_lt_mul_of_pos_right (by norm_num : (6 : Real) < 1025)
      hLogPos).trans hLogScale
  have hLogHalf : 3 * Real.log s < s / 2 := by
    rw [lt_div_iff₀ (by norm_num : (0 : Real) < 2)]
    calc
      3 * Real.log s * 2 = 6 * Real.log s := by ring
      _ < s := hSix
  exact hThree.trans_lt hLogHalf

/-- The logarithmic exponent needed to convert an inverse density into a
lower density bound remains strictly below `2 * s`. -/
theorem dimensionOneRosserSeed_densityExponent_lt
    {s : Real} (hsLarge : Real.exp 5000 + 1 <= s) :
    48 + 802 * Real.log s < 2 * s := by
  have hs : 0 < s := dimensionOneRosserSeed_pos hsLarge
  have hLogScale := dimensionOneRosserSeed_log_mul_lt hsLarge
  have hsFortyEight : (48 : Real) < s := by
    have hExp := Real.add_one_lt_exp (x := (5000 : Real)) (by norm_num)
    nlinarith [Real.exp_pos (5000 : Real)]
  nlinarith

/-- Abstract scalar reserve for the multiplicative moment estimate. -/
theorem dimensionOneRosserSeedMomentExponent_lt
    {s S : Real} (hsLarge : Real.exp 5000 + 1 <= s)
    (hS : S <= 24 + 400 * Real.log s) :
    (3 - s) * Real.log (dimensionOneRosserSeedTilt s) +
        dimensionOneRosserSeedTilt s * S <
      -2 * s + s *
        (4 - Real.log (dimensionOneRosserSeedTilt s)) := by
  have hTilt : 0 < dimensionOneRosserSeedTilt s :=
    dimensionOneRosserSeedTilt_pos hsLarge
  have hMoment : dimensionOneRosserSeedTilt s * S <=
      dimensionOneRosserSeedTilt s * (24 + 400 * Real.log s) :=
    mul_le_mul_of_nonneg_left hS hTilt.le
  have hMomentBound := dimensionOneRosserSeedTilt_mul_massBound_le hsLarge
  have hLogBound := dimensionOneRosserSeed_three_log_tilt_lt hsLarge
  have hs : 0 < s := dimensionOneRosserSeed_pos hsLarge
  have hCombined :
      3 * Real.log (dimensionOneRosserSeedTilt s) +
          dimensionOneRosserSeedTilt s * S < 2 * s := by
    have hSum : 3 * Real.log (dimensionOneRosserSeedTilt s) +
          dimensionOneRosserSeedTilt s * S <
        s / 2 + (2 / 5 : Real) * s :=
      add_lt_add_of_lt_of_le hLogBound (hMoment.trans hMomentBound)
    have hFraction : s / 2 + (2 / 5 : Real) * s < 2 * s := by
      nlinarith
    exact hSum.trans hFraction
  calc
    (3 - s) * Real.log (dimensionOneRosserSeedTilt s) +
          dimensionOneRosserSeedTilt s * S =
        -s * Real.log (dimensionOneRosserSeedTilt s) +
          (3 * Real.log (dimensionOneRosserSeedTilt s) +
            dimensionOneRosserSeedTilt s * S) := by ring
    _ < -s * Real.log (dimensionOneRosserSeedTilt s) + 2 * s :=
      by simpa [add_comm] using
        add_lt_add_left hCombined
          (-s * Real.log (dimensionOneRosserSeedTilt s))
    _ = -2 * s + s *
        (4 - Real.log (dimensionOneRosserSeedTilt s)) := by ring

/-- Exponential form of the abstract moment reserve. -/
theorem dimensionOneRosserSeedMomentExp_lt
    {s S : Real} (hsLarge : Real.exp 5000 + 1 <= s)
    (hS : S <= 24 + 400 * Real.log s) :
    Real.exp ((3 - s) * Real.log (dimensionOneRosserSeedTilt s) +
        dimensionOneRosserSeedTilt s * S) <
      Real.exp (-2 * s) * dimensionOneRosserSeedEnvelope s := by
  rw [dimensionOneRosserSeedEnvelope, <- Real.exp_add]
  exact Real.exp_lt_exp.mpr
    (dimensionOneRosserSeedMomentExponent_lt hsLarge hS)

/-- Abstract conversion of the exponential reserve into the normalized
density factor. -/
theorem dimensionOneRosserSeedExpNegTwo_lt_density_div_sq
    {s S V : Real} (hsLarge : Real.exp 5000 + 1 <= s)
    (hV : 0 < V) (hInv : V⁻¹ <= Real.exp (2 * S))
    (hS : S <= 24 + 400 * Real.log s) :
    Real.exp (-2 * s) < V / s ^ 2 := by
  have hs : 0 < s := dimensionOneRosserSeed_pos hsLarge
  have hsSq : 0 < s ^ 2 := sq_pos_of_pos hs
  have hExponent : 2 * S + 2 * Real.log s < 2 * s := by
    calc
      2 * S + 2 * Real.log s <=
          2 * (24 + 400 * Real.log s) + 2 * Real.log s := by
        linarith
      _ = 48 + 802 * Real.log s := by ring
      _ < 2 * s := dimensionOneRosserSeed_densityExponent_lt hsLarge
  have hsExp : s ^ 2 = Real.exp (2 * Real.log s) := by
    rw [show (2 : Real) * Real.log s =
        (2 : Nat) * Real.log s by norm_num,
      Real.exp_nat_mul, Real.exp_log hs]
  have hProduct : V⁻¹ * s ^ 2 < Real.exp (2 * s) := by
    calc
      V⁻¹ * s ^ 2 <= Real.exp (2 * S) * s ^ 2 :=
        mul_le_mul_of_nonneg_right hInv hsSq.le
      _ = Real.exp (2 * S + 2 * Real.log s) := by
        rw [Real.exp_add, <- hsExp]
      _ < Real.exp (2 * s) := Real.exp_lt_exp.mpr hExponent
  have hInverse := (inv_lt_inv₀ (Real.exp_pos (2 * s))
    (mul_pos (inv_pos.mpr hV) hsSq)).mpr hProduct
  have hLeft : (Real.exp (2 * s))⁻¹ = Real.exp (-2 * s) := by
    rw [<- Real.exp_neg]
    congr 1
    ring
  have hRight : (V⁻¹ * s ^ 2)⁻¹ = V / s ^ 2 := by
    field_simp [hV.ne', hs.ne']
  rwa [hLeft, hRight] at hInverse

end PrimesRestrictedDigits
