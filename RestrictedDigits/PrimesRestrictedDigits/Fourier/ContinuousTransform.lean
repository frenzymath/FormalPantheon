import PrimesRestrictedDigits.Fourier.DigitKernel
import PrimesRestrictedDigits.Fourier.Normalized
import Mathlib.Algebra.BigOperators.Fin

/-!
# Continuous padded digit Fourier transform

This is the arbitrary-real-frequency form of `F_Y` in
`MAYNARD-PRD-PUBLISHED`, Lemma 10.1, specialized to `Y = 10^k`.  The carrier
is the fixed-length padded block; when zero is omitted, no identification with
the standard variable-length carrier is asserted.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- The additive phase `exp (2 * pi * i * n * theta)` at a real frequency. -/
noncomputable def digitPhaseAt (theta : ℝ) (n : ℕ) : ℂ :=
  Complex.exp
    (((2 * Real.pi * (n : ℝ) * theta : ℝ) : ℂ) * Complex.I)

private noncomputable def digitListFourierSumAt
    (a : Fin 10) (length : ℕ) (theta : ℝ) : ℂ :=
  ∑ L ∈ restrictedDigitLists a length,
    digitPhaseAt theta (Nat.ofDigits 10 L)

/-- The source's finite exponential sum on the padded length-`k` block. -/
noncomputable def paddedDigitFourierSumAt
    (a : Fin 10) (length : ℕ) (theta : ℝ) : ℂ :=
  ∑ n ∈ paddedRestrictedNumbers a length, digitPhaseAt theta n

private noncomputable def continuousDigitFourierFactor (a : Fin 10) :
    ℕ → ℝ → ℂ
  | 0, _ => 1
  | length + 1, theta =>
      (∑ d ∈ allowedDecimalDigits a, digitPhaseAt theta d) *
        continuousDigitFourierFactor a length (10 * theta)

private theorem digitPhaseAt_cons (theta : ℝ) (d : ℕ) (tail : List ℕ) :
    digitPhaseAt theta (Nat.ofDigits 10 (d :: tail)) =
      digitPhaseAt theta d *
        digitPhaseAt (10 * theta) (Nat.ofDigits 10 tail) := by
  rw [digitPhaseAt, digitPhaseAt, digitPhaseAt, Nat.ofDigits_cons,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem digitListFourierSumAt_eq_factor
    (a : Fin 10) (length : ℕ) (theta : ℝ) :
    digitListFourierSumAt a length theta =
      continuousDigitFourierFactor a length theta := by
  induction length generalizing theta with
  | zero =>
      rw [digitListFourierSumAt, restrictedDigitLists,
        List.fixedLengthDigits_zero, Finset.filter_singleton]
      simp [continuousDigitFourierFactor, digitPhaseAt]
  | succ length ih =>
      rw [digitListFourierSumAt, restrictedDigitLists,
        List.fixedLengthDigits_succ_eq_disjiUnion, Finset.filter_disjiUnion,
        Finset.sum_disjiUnion]
      rw [continuousDigitFourierFactor]
      have hhead (d : ℕ) :
          (∑ L ∈ (List.consFixedLengthDigits (by omega : 1 < 10) length d).filter
              (fun L => a.val ∉ L),
            digitPhaseAt theta (Nat.ofDigits 10 L)) =
            if d = a.val then 0 else
              ∑ T ∈ restrictedDigitLists a length,
                digitPhaseAt theta (Nat.ofDigits 10 (d :: T)) := by
        classical
        by_cases hda : d = a.val
        · rw [if_pos hda]
          have hempty :
              (List.consFixedLengthDigits (by omega : 1 < 10) length d).filter
                  (fun L => a.val ∉ L) = ∅ := by
            rw [Finset.filter_eq_empty_iff]
            intro L hL
            obtain ⟨tail, htail, rfl⟩ := Finset.mem_image.mp hL
            simp [hda]
          rw [hempty]
          simp
        · have hda' : a.val ≠ d := Ne.symm hda
          have heq :
              (List.consFixedLengthDigits (by omega : 1 < 10) length d).filter
                  (fun L => a.val ∉ L) =
                (restrictedDigitLists a length).image (fun L => d :: L) := by
            ext L
            constructor
            · intro hL
              rcases Finset.mem_filter.mp hL with ⟨hL, hnot⟩
              obtain ⟨tail, htail, rfl⟩ := Finset.mem_image.mp hL
              refine Finset.mem_image.mpr ⟨tail,
                Finset.mem_filter.mpr ⟨htail, ?_⟩, rfl⟩
              intro ha
              exact hnot (by simp [ha])
            · intro hL
              rcases Finset.mem_image.mp hL with ⟨tail, htail, rfl⟩
              rcases Finset.mem_filter.mp htail with ⟨htail, hnot⟩
              refine Finset.mem_filter.mpr
                ⟨Finset.mem_image.mpr ⟨tail, htail, rfl⟩, ?_⟩
              simpa [hda'] using hnot
          rw [heq, Finset.sum_image]
          · rw [if_neg hda]
          · intro L₁ hL₁ L₂ hL₂ h
            exact List.cons.inj h |>.2
      calc
        (∑ i ∈ Finset.range 10,
            ∑ L ∈ (List.consFixedLengthDigits (by omega : 1 < 10) length i).filter
              (fun L => a.val ∉ L),
              digitPhaseAt theta (Nat.ofDigits 10 L)) =
            ∑ i ∈ Finset.range 10,
              (if i = a.val then 0 else
                ∑ T ∈ restrictedDigitLists a length,
                  digitPhaseAt theta (Nat.ofDigits 10 (i :: T))) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hhead i
        _ = ∑ i ∈ allowedDecimalDigits a,
              ∑ T ∈ restrictedDigitLists a length,
                digitPhaseAt theta (Nat.ofDigits 10 (i :: T)) := by
          rw [allowedDecimalDigits]
          calc
            (∑ i ∈ Finset.range 10,
                (if i = a.val then 0 else
                  ∑ T ∈ restrictedDigitLists a length,
                    digitPhaseAt theta (Nat.ofDigits 10 (i :: T)))) =
                ∑ i ∈ Finset.range 10,
                  (if i ≠ a.val then
                    ∑ T ∈ restrictedDigitLists a length,
                      digitPhaseAt theta (Nat.ofDigits 10 (i :: T))
                   else 0) := by
              apply Finset.sum_congr rfl
              intro i hi
              by_cases h : i = a.val <;> simp [h]
            _ = ∑ i ∈ (Finset.range 10).filter (fun i => i ≠ a.val),
                  ∑ T ∈ restrictedDigitLists a length,
                    digitPhaseAt theta (Nat.ofDigits 10 (i :: T)) := by
              rw [Finset.sum_filter]
        _ = (∑ i ∈ allowedDecimalDigits a, digitPhaseAt theta i) *
            (∑ T ∈ restrictedDigitLists a length,
              digitPhaseAt (10 * theta) (Nat.ofDigits 10 T)) := by
          rw [Finset.sum_mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro T hT
          exact digitPhaseAt_cons theta i T
        _ = (∑ i ∈ allowedDecimalDigits a, digitPhaseAt theta i) *
            continuousDigitFourierFactor a length (10 * theta) := by
          change (∑ i ∈ allowedDecimalDigits a, digitPhaseAt theta i) *
              digitListFourierSumAt a length (10 * theta) = _
          rw [ih]

private theorem paddedDigitFourierSumAt_eq_factor
    (a : Fin 10) (length : ℕ) (theta : ℝ) :
    paddedDigitFourierSumAt a length theta =
      continuousDigitFourierFactor a length theta := by
  rw [← digitListFourierSumAt_eq_factor]
  apply Finset.sum_nbij (Nat.digitsAppend 10 length)
  · exact (bijOn_digitsAppend_paddedRestrictedNumbers a length).mapsTo
  · exact (bijOn_digitsAppend_paddedRestrictedNumbers a length).injOn
  · exact (bijOn_digitsAppend_paddedRestrictedNumbers a length).surjOn
  · intro n hn
    change digitPhaseAt theta n =
      digitPhaseAt theta (Nat.ofDigits 10 (paddedDecimalDigits length n))
    rw [ofDigits_paddedDecimalDigits]

private theorem continuousDigitFourierFactor_eq_product
    (a : Fin 10) (length : ℕ) (theta : ℝ) :
    continuousDigitFourierFactor a length theta =
      ∏ start : Fin length,
        ∑ d ∈ allowedDecimalDigits a,
          digitPhaseAt ((10 : ℝ) ^ start.val * theta) d := by
  induction length generalizing theta with
  | zero => simp [continuousDigitFourierFactor]
  | succ length ih =>
      rw [continuousDigitFourierFactor, Fin.prod_univ_succ]
      congr 1
      · simp
      · rw [ih]
        apply Finset.prod_congr rfl
        intro start hstart
        congr 1
        funext d
        congr 1
        simp only [Fin.val_succ, pow_succ]
        ring

/-- The paper's power-of-ten normalization, written with its negative exponent. -/
theorem powerOfTen_sourceNormalization (k : ℕ) :
    (((10 ^ k : ℕ) : ℝ) ^ (-(Real.log 9 / Real.log 10))) =
      1 / (9 : ℝ) ^ k := by
  have hlogTen : Real.log (10 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num))
  rw [Real.rpow_def_of_pos (by positivity), Nat.cast_pow, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  have hexponent :
      (k : ℝ) * Real.log 10 * (-(Real.log 9 / Real.log 10)) =
        -(k : ℝ) * Real.log 9 := by
    field_simp
  rw [hexponent, show -(k : ℝ) * Real.log 9 = -((k : ℝ) * Real.log 9) by ring,
    Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 9)]
  rw [one_div]

/-- The normalized complex one-digit factor before taking its norm. -/
noncomputable def normalizedDigitFourierFactorAt
    (a : Fin 10) (theta : ℝ) : ℂ :=
  (∑ d ∈ allowedDecimalDigits a, digitPhaseAt theta d) / 9

/-- The normalized complex padded transform before taking its norm. -/
noncomputable def normalizedPaddedDigitFourierTransformAt
    (a : Fin 10) (length : ℕ) (theta : ℝ) : ℂ :=
  paddedDigitFourierSumAt a length theta / (9 : ℂ) ^ length

/-- The normalized complex transform factors into normalized local factors. -/
theorem normalizedPaddedDigitFourierTransformAt_eq_factorProduct
    (a : Fin 10) (length : ℕ) (theta : ℝ) :
    normalizedPaddedDigitFourierTransformAt a length theta =
      ∏ start : Fin length,
        normalizedDigitFourierFactorAt a
          ((10 : ℝ) ^ start.val * theta) := by
  rw [normalizedPaddedDigitFourierTransformAt,
    paddedDigitFourierSumAt_eq_factor,
    continuousDigitFourierFactor_eq_product,
    ← Fin.prod_const length (9 : ℂ), ← Finset.prod_div_distrib]
  rfl

/-- The source sum divided by the exact cardinality `9^k`. -/
noncomputable def normalizedPaddedDigitFourierMagnitudeAt
    (a : Fin 10) (length : ℕ) (theta : ℝ) : ℝ :=
  ‖paddedDigitFourierSumAt a length theta‖ / (9 : ℝ) ^ length

private theorem localFactorAt_normalized_eq_digitKernel
    (a : Fin 10) (theta : ℝ) :
    ‖∑ d ∈ allowedDecimalDigits a, digitPhaseAt theta d‖ / 9 =
      digitKernel a theta := by
  unfold digitPhaseAt digitKernel
  ring

/-- Taking the norm of a normalized local factor gives the existing kernel. -/
theorem norm_normalizedDigitFourierFactorAt
    (a : Fin 10) (theta : ℝ) :
    ‖normalizedDigitFourierFactorAt a theta‖ = digitKernel a theta := by
  rw [normalizedDigitFourierFactorAt, norm_div]
  norm_num only [Complex.norm_ofNat]
  exact localFactorAt_normalized_eq_digitKernel a theta

/-- Taking the norm of the complex transform gives the source magnitude. -/
theorem norm_normalizedPaddedDigitFourierTransformAt
    (a : Fin 10) (length : ℕ) (theta : ℝ) :
    ‖normalizedPaddedDigitFourierTransformAt a length theta‖ =
      normalizedPaddedDigitFourierMagnitudeAt a length theta := by
  rw [normalizedPaddedDigitFourierTransformAt,
    normalizedPaddedDigitFourierMagnitudeAt, norm_div, norm_pow]
  norm_num only [Complex.norm_ofNat]

/-- The continuous source sum factors into its normalized one-digit kernels. -/
theorem normalizedPaddedDigitFourierMagnitudeAt_eq_kernelProduct
    (a : Fin 10) (length : ℕ) (theta : ℝ) :
    normalizedPaddedDigitFourierMagnitudeAt a length theta =
      ∏ start : Fin length,
        digitKernel a ((10 : ℝ) ^ start.val * theta) := by
  rw [normalizedPaddedDigitFourierMagnitudeAt,
    paddedDigitFourierSumAt_eq_factor,
    continuousDigitFourierFactor_eq_product, norm_prod]
  rw [← Fin.prod_const length (9 : ℝ), ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro start hstart
  exact localFactorAt_normalized_eq_digitKernel a _

private theorem digitPhaseAt_grid
    (length frequency n : ℕ) :
    digitPhaseAt ((frequency : ℝ) / (10 : ℝ) ^ length) n =
      digitPhase length frequency n := by
  rw [digitPhaseAt, digitPhase]
  congr 1
  push_cast
  field_simp

/-- The existing natural-frequency transform is the exact decimal grid case. -/
theorem normalizedPaddedDigitFourierMagnitudeAt_grid
    (a : Fin 10) (length frequency : ℕ) :
    normalizedPaddedDigitFourierMagnitudeAt a length
        ((frequency : ℝ) / (10 : ℝ) ^ length) =
      normalizedPaddedDigitFourierMagnitude a length frequency := by
  rw [normalizedPaddedDigitFourierMagnitudeAt,
    normalizedPaddedDigitFourierMagnitude,
    paddedDigitFourierSumAt, paddedDigitFourierSum]
  congr 2
  apply Finset.sum_congr rfl
  intro n hn
  exact digitPhaseAt_grid length frequency n

end PrimesRestrictedDigits
