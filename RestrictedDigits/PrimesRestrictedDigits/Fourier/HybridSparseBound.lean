import PrimesRestrictedDigits.Fourier.HybridConstants
import PrimesRestrictedDigits.Fourier.HybridConsecutiveGrid
import PrimesRestrictedDigits.Fourier.HybridScaleSelection
import PrimesRestrictedDigits.Fourier.TransformBlockFactorization
import PrimesRestrictedDigits.Fourier.LargeSieveSampling

/-!
# Sparse-regime hybrid estimate

This is the low-density branch of the repaired sampler. The integer carrier is exact, while
the three-block factorization supplies a prefix maximum and a complete tail grid.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

private theorem alignedGridSum_le_prefix_mul_tail
    (digit : Fin 10) (length u v w : Nat) (E x : Real)
    (hlength : length = u + v + w) (hE : 1 <= E)
    (hEW : E <= ((10 ^ w : Nat) : Real))
    (hWUpper : ((10 ^ w : Nat) : Real) < 100 * E)
    (hx : x ∈ Set.Icc (0 : Real) 1) :
    alignedGridSum digit length E x <=
      closedWindowMaximum
          (normalizedPaddedDigitFourierMagnitudeAt digit u) (E / ((10 ^ length : Nat) : Real)) x *
        (8000000 * E ^ largeSieveAlpha) := by
  classical
  let Y : Real := ((10 ^ length : Nat) : Real)
  let W : Real := ((10 ^ w : Nat) : Real)
  have hY : 0 < Y := by
    dsimp [Y]
    positivity
  have hdelta : 0 <= E / Y := by positivity
  have htail := alignedGridWindow_tail_sum_le digit length w E x hE hEW hWUpper
  have hsum :
      (∑ b ∈ alignedGridWindow length E x,
        normalizedPaddedDigitFourierMagnitudeAt digit length
          ((b : Real) / Y)) <=
        ∑ b ∈ alignedGridWindow length E x,
          closedWindowMaximum
              (normalizedPaddedDigitFourierMagnitudeAt digit u) (E / Y) x *
            normalizedPaddedDigitFourierMagnitudeAt digit w
              ((b : Real) / W) := by
    apply Finset.sum_le_sum
    intro b hb
    have hfactor := normalizedPaddedDigitFourierMagnitudeAt_threeBlock_le
      digit length u v w hlength ((b : Real) / Y)
    have hE0 : 0 <= E := by linarith
    have hmem := (mem_alignedGridWindow_iff_of_mem_Icc hE0 hx (b := b)).mp hb
    have hwindow : b / Y - x ∈ Set.Icc (-(E / Y)) (E / Y) := by
      rw [Set.mem_Icc]
      have habs := abs_le.mp hmem
      constructor <;> linarith
    have hmax := le_closedWindowMaximum
      (normalizedPaddedDigitFourierMagnitudeAt_continuous digit u)
      hdelta x hwindow
    have hargument : x + ((b : Real) / Y - x) = (b : Real) / Y := by
      ring
    have hfirst :
        normalizedPaddedDigitFourierMagnitudeAt digit u ((b : Real) / Y) <=
          closedWindowMaximum
            (normalizedPaddedDigitFourierMagnitudeAt digit u) (E / Y) x := by
      rw [hargument] at hmax
      exact hmax
    have htailnonneg := normalizedPaddedDigitFourierMagnitudeAt_nonneg digit w
      ((b : Real) / W)
    have harg :
        ((10 : Real) ^ (u + v)) * ((b : Real) / Y) = (b : Real) / W := by
      dsimp [Y, W]
      norm_num only [Nat.cast_pow, Nat.cast_ofNat]
      rw [hlength, pow_add]
      field_simp
      rw [pow_add]
      ring
    rw [← harg] at htailnonneg ⊢
    calc
      normalizedPaddedDigitFourierMagnitudeAt digit length ((b : Real) / Y) <=
          normalizedPaddedDigitFourierMagnitudeAt digit u ((b : Real) / Y) *
            normalizedPaddedDigitFourierMagnitudeAt digit w
              (((10 : Real) ^ (u + v)) * ((b : Real) / Y)) := hfactor
      _ <= closedWindowMaximum
            (normalizedPaddedDigitFourierMagnitudeAt digit u) (E / Y) x *
            normalizedPaddedDigitFourierMagnitudeAt digit w
              (((10 : Real) ^ (u + v)) * ((b : Real) / Y)) :=
        mul_le_mul_of_nonneg_right hfirst htailnonneg
  have hsum' :
      (∑ b ∈ alignedGridWindow length E x,
        closedWindowMaximum
            (normalizedPaddedDigitFourierMagnitudeAt digit u) (E / Y) x *
          normalizedPaddedDigitFourierMagnitudeAt digit w
            ((b : Real) / W)) =
        closedWindowMaximum
            (normalizedPaddedDigitFourierMagnitudeAt digit u) (E / Y) x *
          (∑ b ∈ alignedGridWindow length E x,
            normalizedPaddedDigitFourierMagnitudeAt digit w ((b : Real) / W)) := by
    rw [Finset.mul_sum]
  calc
    alignedGridSum digit length E x =
        ∑ b ∈ alignedGridWindow length E x,
          normalizedPaddedDigitFourierMagnitudeAt digit length ((b : Real) / Y) := by
      rfl
    _ <= ∑ b ∈ alignedGridWindow length E x,
        closedWindowMaximum
            (normalizedPaddedDigitFourierMagnitudeAt digit u) (E / Y) x *
          normalizedPaddedDigitFourierMagnitudeAt digit w ((b : Real) / W) := hsum
    _ = closedWindowMaximum
          (normalizedPaddedDigitFourierMagnitudeAt digit u) (E / Y) x *
        (∑ b ∈ alignedGridWindow length E x,
          normalizedPaddedDigitFourierMagnitudeAt digit w ((b : Real) / W)) := hsum'
    _ <= closedWindowMaximum
          (normalizedPaddedDigitFourierMagnitudeAt digit u) (E / Y) x *
        (8000000 * E ^ largeSieveAlpha) := by
      apply mul_le_mul_of_nonneg_left htail
      exact closedWindowMaximum_nonneg
        (normalizedPaddedDigitFourierMagnitudeAt_continuous digit u)
        (fun z => normalizedPaddedDigitFourierMagnitudeAt_nonneg digit u z)
        hdelta x

theorem sum_alignedGridSum_sparse_le
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (digit : Fin 10) (length : Nat) (base : ι -> Real)
    {L E : Real} (hL : 1 <= L) (hE : 1 <= E)
    (hbase : ∀ i ∈ s, base i ∈ Set.Icc (0 : Real) 1)
    (hseparated : ∀ i ∈ s, ∀ j ∈ s, i ≠ j ->
      1 / L <= dist ((base i : Real) : UnitAddCircle)
        ((base j : Real) : UnitAddCircle))
    (hlow : 10 * L * E < ((10 ^ length : Nat) : Real)) :
    (∑ i ∈ s, alignedGridSum digit length E (base i)) <=
      hybridSamplingConstant * (L * E) ^ largeSieveAlpha := by
  classical
  let Y : Real := ((10 ^ length : Nat) : Real)
  have hY : 0 < Y := by
    dsimp [Y]
    positivity
  obtain ⟨u, v, w, hlength, huL, hLu, hvV, hVclose, hEw, hwUpper⟩ :=
    exists_hybrid_decimalBlocks hL hE length (by simpa [Y] using hlow)
  let U : Real := ((10 ^ u : Nat) : Real)
  have hU : 0 < U := by
    dsimp [U]
    positivity
  have hsumPoint (i : ι) (hi : i ∈ s) :
      alignedGridSum digit length E (base i) <=
        closedWindowMaximum
            (normalizedPaddedDigitFourierMagnitudeAt digit u)
            (E / Y) (base i) * (8000000 * E ^ largeSieveAlpha) := by
    simpa [Y] using alignedGridSum_le_prefix_mul_tail digit length u v w E
      (base i) hlength hE hEw hwUpper (hbase i hi)
  have hpointSum :
      (∑ i ∈ s, alignedGridSum digit length E (base i)) <=
        (∑ i ∈ s, closedWindowMaximum
          (normalizedPaddedDigitFourierMagnitudeAt digit u) (E / Y) (base i)) *
          (8000000 * E ^ largeSieveAlpha) := by
    calc
      (∑ i ∈ s, alignedGridSum digit length E (base i)) <=
          ∑ i ∈ s,
            closedWindowMaximum
                (normalizedPaddedDigitFourierMagnitudeAt digit u) (E / Y)
                (base i) * (8000000 * E ^ largeSieveAlpha) :=
        Finset.sum_le_sum fun i hi => hsumPoint i hi
      _ = _ := by rw [Finset.sum_mul]
  have hsample := sum_closedWindowMaximum_normalizedPaddedDigitFourierMagnitudeAt_le
    s digit u base hL (by positivity : 0 <= E / Y) hseparated 0
  have hsample' :
      (∑ i ∈ s, closedWindowMaximum
        (normalizedPaddedDigitFourierMagnitudeAt digit u) (E / Y)
          (base i)) <=
        70400000 * (1 + (E / Y) * L) *
          (L ^ largeSieveAlpha + L * U ^ (-largeSieveSigma)) := by
    simpa only [add_zero, U, largeSieveSamplingConstant] using hsample
  have hsmall : (E / Y) * L < (1 : Real) / 10 := by
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hY).mpr
    nlinarith [hlow]
  have hfac : 1 + (E / Y) * L <= 2 := by linarith
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hLdivU : L / 10 <= U := by
    dsimp [U] at hLu ⊢
    linarith
  have hpowNeg : U ^ (-largeSieveSigma) <=
      (L / 10) ^ (-largeSieveSigma) := by
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hLdivU
      (neg_nonpos.mpr largeSieveSigma_nonneg)
  have hdivIdentity :
      (L / 10) ^ (-largeSieveSigma) =
        10 ^ largeSieveSigma * L ^ (-largeSieveSigma) := by
    rw [Real.div_rpow hL0.le (by norm_num : (0 : Real) <= 10)]
    rw [Real.rpow_neg hL0.le, Real.rpow_neg (by norm_num : (0 : Real) <= 10)]
    rw [div_eq_mul_inv, inv_inv]
    ring
  have htenPower : (10 : Real) ^ largeSieveSigma <= 10 := by
    calc
      (10 : Real) ^ largeSieveSigma <= (10 : Real) ^ (1 : Real) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (by norm_num [largeSieveSigma])
      _ = 10 := Real.rpow_one 10
  have hpowNeg' : U ^ (-largeSieveSigma) <=
      10 * L ^ (-largeSieveSigma) := by
    calc
      U ^ (-largeSieveSigma) <= (L / 10) ^ (-largeSieveSigma) := hpowNeg
      _ = 10 ^ largeSieveSigma * L ^ (-largeSieveSigma) := hdivIdentity
      _ <= 10 * L ^ (-largeSieveSigma) :=
        mul_le_mul_of_nonneg_right htenPower (Real.rpow_nonneg hL0.le _)
  have hcombine : L * L ^ (-largeSieveSigma) = L ^ largeSieveAlpha := by
    calc
      L * L ^ (-largeSieveSigma) = L ^ (1 : Real) * L ^ (-largeSieveSigma) := by
        rw [Real.rpow_one]
      _ = L ^ ((1 : Real) + (-largeSieveSigma)) :=
        (Real.rpow_add hL0 _ _).symm
      _ = L ^ largeSieveAlpha := by
        congr 1
        norm_num [largeSieveAlpha, largeSieveSigma]
  have hpowTarget :
      L ^ largeSieveAlpha + L * U ^ (-largeSieveSigma) <=
        11 * L ^ largeSieveAlpha := by
    have htail : L * U ^ (-largeSieveSigma) <=
        10 * L ^ largeSieveAlpha := by
      calc
        L * U ^ (-largeSieveSigma) <=
            L * (10 * L ^ (-largeSieveSigma)) :=
          mul_le_mul_of_nonneg_left hpowNeg' hL0.le
        _ = 10 * (L * L ^ (-largeSieveSigma)) := by ring
        _ = 10 * L ^ largeSieveAlpha := by rw [hcombine]
    nlinarith [Real.rpow_nonneg hL0.le largeSieveAlpha]
  have hpref :
      (∑ i ∈ s, closedWindowMaximum
        (normalizedPaddedDigitFourierMagnitudeAt digit u) (E / Y)
          (base i)) <= 1548800000 * L ^ largeSieveAlpha := by
    calc
      _ <= 70400000 * (1 + (E / Y) * L) *
          (L ^ largeSieveAlpha + L * U ^ (-largeSieveSigma)) := hsample'
      _ <= 70400000 * 2 * (11 * L ^ largeSieveAlpha) := by
        gcongr
      _ = 1548800000 * L ^ largeSieveAlpha := by ring
  calc
    (∑ i ∈ s, alignedGridSum digit length E (base i)) <=
        (∑ i ∈ s, closedWindowMaximum
          (normalizedPaddedDigitFourierMagnitudeAt digit u) (E / Y)
            (base i)) * (8000000 * E ^ largeSieveAlpha) := hpointSum
    _ <= (1548800000 * L ^ largeSieveAlpha) *
          (8000000 * E ^ largeSieveAlpha) := by
      gcongr
    _ <= hybridSamplingConstant * (L * E) ^ largeSieveAlpha := by
      have hLpow : 0 <= L ^ largeSieveAlpha := Real.rpow_nonneg hL0.le _
      have hE0 : 0 <= E := by linarith
      have hEpow : 0 <= E ^ largeSieveAlpha := Real.rpow_nonneg hE0 _
      have hmul : L ^ largeSieveAlpha * E ^ largeSieveAlpha =
          (L * E) ^ largeSieveAlpha := by
        rw [← Real.mul_rpow hL0.le hE0]
      rw [show (1548800000 : Real) * (L ^ largeSieveAlpha) *
          (8000000 * E ^ largeSieveAlpha) =
            12390400000000000 *
              (L ^ largeSieveAlpha * E ^ largeSieveAlpha) by ring]
      rw [hmul]
      unfold hybridSamplingConstant
      gcongr
      norm_num

end

end PrimesRestrictedDigits
