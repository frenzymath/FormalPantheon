import PrimesRestrictedDigits.Fourier.Normalized
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum

/-!
# Digit-transform level sets

This proves the exact finite Markov inequality underlying Lemma 10.4 of
`MAYNARD-PRD-PUBLISHED` and checks the two rational exponent margins used in
Lemma 12.2. The missing moment certificate remains a separate obligation.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- Frequencies on the complete decimal grid where the normalized digit
transform is at least `T`. -/
noncomputable def normalizedMagnitudeLargeFrequencies
    (a : Fin 10) (length : Nat) (T : Real) :
    Finset (Fin (10 ^ length)) := by
  classical
  exact Finset.univ.filter fun frequency =>
    T <= normalizedPaddedDigitFourierMagnitude a length frequency.val

@[simp] theorem mem_normalizedMagnitudeLargeFrequencies
    {a : Fin 10} {length : Nat} {T : Real}
    {frequency : Fin (10 ^ length)} :
    frequency ∈ normalizedMagnitudeLargeFrequencies a length T <->
      T <= normalizedPaddedDigitFourierMagnitude a length frequency.val := by
  simp [normalizedMagnitudeLargeFrequencies]

/-- Exact finite Markov inequality for a nonnegative real moment. -/
theorem card_normalizedMagnitudeLargeFrequencies_mul_rpow_le
    (a : Fin 10) (length : Nat) (T t : Real)
    (hT : 0 <= T) (ht : 0 <= t) :
    ((normalizedMagnitudeLargeFrequencies a length T).card : Real) * T ^ t <=
      ∑ frequency : Fin (10 ^ length),
        normalizedPaddedDigitFourierMagnitude a length frequency.val ^ t := by
  let E := normalizedMagnitudeLargeFrequencies a length T
  have hpoint : ∀ frequency ∈ E, T ^ t <=
      normalizedPaddedDigitFourierMagnitude a length frequency.val ^ t := by
    intro frequency hfrequency
    exact Real.rpow_le_rpow hT
      (mem_normalizedMagnitudeLargeFrequencies.mp hfrequency) ht
  calc
    (E.card : Real) * T ^ t = ∑ _frequency ∈ E, T ^ t := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ <= ∑ frequency ∈ E,
        normalizedPaddedDigitFourierMagnitude a length frequency.val ^ t :=
      Finset.sum_le_sum hpoint
    _ <= ∑ frequency : Fin (10 ^ length),
        normalizedPaddedDigitFourierMagnitude a length frequency.val ^ t := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E)
      intro frequency hfrequency hnot
      exact Real.rpow_nonneg
        (normalizedPaddedDigitFourierMagnitude_nonneg
          a length frequency.val) t

/-- A supplied finite moment bound controls the weak level-set cardinality. -/
theorem card_normalizedMagnitudeLargeFrequencies_le
    (a : Fin 10) (length : Nat) (T t M : Real)
    (hT : 0 < T) (ht : 0 <= t)
    (hmoment : (∑ frequency : Fin (10 ^ length),
      normalizedPaddedDigitFourierMagnitude a length frequency.val ^ t) <= M) :
    ((normalizedMagnitudeLargeFrequencies a length T).card : Real) <=
      M / T ^ t := by
  have hpow : 0 < T ^ t := Real.rpow_pos_of_pos hT t
  apply (le_div_iff₀ hpow).2
  exact (card_normalizedMagnitudeLargeFrequencies_mul_rpow_le
    a length T t hT.le ht).trans hmoment

/-- The exact coefficient-one specialization at threshold `1 / B`. -/
theorem card_normalizedMagnitudeLargeFrequencies_one_div_le
    (a : Fin 10) (length : Nat) (B t M : Real)
    (hB : 0 < B) (ht : 0 <= t)
    (hmoment : (∑ frequency : Fin (10 ^ length),
      normalizedPaddedDigitFourierMagnitude a length frequency.val ^ t) <= M) :
    ((normalizedMagnitudeLargeFrequencies a length (1 / B)).card : Real) <=
      B ^ t * M := by
  have h := card_normalizedMagnitudeLargeFrequencies_le
    a length (1 / B) t M (by positivity) ht hmoment
  rw [Real.div_rpow (by positivity) hB.le, Real.one_rpow] at h
  have hpow : B ^ t ≠ 0 := (Real.rpow_pos_of_pos hB t).ne'
  calc
    ((normalizedMagnitudeLargeFrequencies a length (1 / B)).card : Real) <=
        M / (1 / B ^ t) := h
    _ = B ^ t * M := by field_simp

/-- Above a positive threshold, a `t`th moment with `t >= 1` controls the
total first-power mass directly, without a dyadic decomposition. -/
theorem sum_normalizedMagnitudeLargeFrequencies_le_moment
    (a : Fin 10) (length : Nat) (T t : Real)
    (hT : 0 < T) (ht : 1 <= t) :
    (∑ frequency ∈ normalizedMagnitudeLargeFrequencies a length T,
      normalizedPaddedDigitFourierMagnitude a length frequency.val) <=
      T ^ (1 - t) *
        ∑ frequency : Fin (10 ^ length),
          normalizedPaddedDigitFourierMagnitude a length frequency.val ^ t := by
  let E := normalizedMagnitudeLargeFrequencies a length T
  have hpoint : ∀ frequency ∈ E,
      normalizedPaddedDigitFourierMagnitude a length frequency.val <=
        T ^ (1 - t) *
          normalizedPaddedDigitFourierMagnitude a length frequency.val ^ t := by
    intro frequency hfrequency
    let F := normalizedPaddedDigitFourierMagnitude a length frequency.val
    have hTF : T <= F :=
      mem_normalizedMagnitudeLargeFrequencies.mp hfrequency
    have hF : 0 < F := hT.trans_le hTF
    have hanti : F ^ (1 - t) <= T ^ (1 - t) :=
      Real.rpow_le_rpow_of_nonpos hT hTF (by linarith)
    have hpow : 0 <= F ^ t := Real.rpow_nonneg hF.le t
    calc
      F = F ^ t * F ^ (1 - t) := by
        rw [← Real.rpow_add hF]
        ring_nf
        rw [Real.rpow_one]
      _ <= F ^ t * T ^ (1 - t) :=
        mul_le_mul_of_nonneg_left hanti hpow
      _ = T ^ (1 - t) * F ^ t := mul_comm _ _
  calc
    (∑ frequency ∈ E,
        normalizedPaddedDigitFourierMagnitude a length frequency.val) <=
        ∑ frequency ∈ E,
          T ^ (1 - t) *
            normalizedPaddedDigitFourierMagnitude a length frequency.val ^ t :=
      Finset.sum_le_sum hpoint
    _ = T ^ (1 - t) *
        ∑ frequency ∈ E,
          normalizedPaddedDigitFourierMagnitude a length frequency.val ^ t := by
      rw [Finset.mul_sum]
    _ <= T ^ (1 - t) *
        ∑ frequency : Fin (10 ^ length),
          normalizedPaddedDigitFourierMagnitude a length frequency.val ^ t := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hT.le (1 - t))
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E)
      intro frequency hfrequency hnot
      exact Real.rpow_nonneg
        (normalizedPaddedDigitFourierMagnitude_nonneg
          a length frequency.val) t

/-- A supplied complete moment bound controls the first-power mass above a
positive threshold. -/
theorem sum_normalizedMagnitudeLargeFrequencies_le
    (a : Fin 10) (length : Nat) (T t M : Real)
    (hT : 0 < T) (ht : 1 <= t)
    (hmoment : (∑ frequency : Fin (10 ^ length),
      normalizedPaddedDigitFourierMagnitude a length frequency.val ^ t) <= M) :
    (∑ frequency ∈ normalizedMagnitudeLargeFrequencies a length T,
      normalizedPaddedDigitFourierMagnitude a length frequency.val) <=
      T ^ (1 - t) * M := by
  exact (sum_normalizedMagnitudeLargeFrequencies_le_moment
    a length T t hT ht).trans
      (mul_le_mul_of_nonneg_left hmoment
        (Real.rpow_nonneg hT.le (1 - t)))

/-- The reciprocal-threshold form has the exact exponent `t - 1`. -/
theorem sum_normalizedMagnitudeLargeFrequencies_one_div_le
    (a : Fin 10) (length : Nat) (B t M : Real)
    (hB : 0 < B) (ht : 1 <= t)
    (hmoment : (∑ frequency : Fin (10 ^ length),
      normalizedPaddedDigitFourierMagnitude a length frequency.val ^ t) <= M) :
    (∑ frequency ∈ normalizedMagnitudeLargeFrequencies a length (1 / B),
      normalizedPaddedDigitFourierMagnitude a length frequency.val) <=
      B ^ (t - 1) * M := by
  have h := sum_normalizedMagnitudeLargeFrequencies_le
    a length (1 / B) t M (by positivity) ht hmoment
  have hscale : (1 / B) ^ (1 - t) = B ^ (t - 1) := by
    rw [Real.div_rpow (by positivity) hB.le, Real.one_rpow]
    calc
      1 / B ^ (1 - t) = (B ^ (1 - t))⁻¹ := one_div _
      _ = B ^ (-(1 - t)) := (Real.rpow_neg hB.le (1 - t)).symm
      _ = B ^ (t - 1) := by ring_nf
  rwa [hscale] at h

/-- Exact positive margin for the exceptional-set cardinality exponent in
Lemma 12.2. -/
theorem genericExceptionalCardinalityExponent_gap :
    (23 / 40 : Real) -
        ((23 / 80 : Real) * (235 / 154 : Real) + 59 / 433) =
      127 / 5334560 := by
  norm_num

theorem genericExceptionalCardinalityExponent_lt :
    (23 / 80 : Real) * (235 / 154 : Real) + 59 / 433 < 23 / 40 := by
  norm_num

/-- Exact positive margin for the complementary digit-prime product in
Lemma 12.2. -/
theorem genericComplementaryProductExponent_gap :
    (23 / 80 : Real) * (73 / 308 : Real) - 59 / 866 =
      127 / 10669120 := by
  norm_num

theorem genericComplementaryProductExponent_lt :
    (59 / 866 : Real) < (23 / 80 : Real) * (73 / 308 : Real) := by
  norm_num

/-- The exponent left after weighting a `235/154` level-set count by its
dyadic magnitude. -/
theorem genericDyadicMomentExponent_sub_one :
    (235 / 154 : Real) - 1 = 81 / 154 := by
  norm_num

/-- The exponent of `B` after taking the geometric mean of the prime and
digit level-set bounds. -/
theorem genericGeometricMeanBExponent_sub_one :
    (235 / 308 : Real) - 1 = -(73 / 308 : Real) := by
  norm_num

end PrimesRestrictedDigits
