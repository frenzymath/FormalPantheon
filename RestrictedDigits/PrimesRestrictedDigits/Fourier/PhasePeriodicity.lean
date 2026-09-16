import PrimesRestrictedDigits.Fourier.FrequencyWindow

/-!
# Integer prefixes and periodic digit phases

The decimal suffix used by the Markov argument is obtained after removing an
integer prefix from a scaled frequency. The finite digit kernel is periodic
under that prefix translation.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

def decimalIntegerPrefix (length : ℕ) (digits : ℕ → ℕ) : ℕ :=
  ∑ i ∈ Finset.range length, digits i * 10 ^ (length - 1 - i)

private lemma prefix_term_scale {length index : ℕ} (hindex : index < length)
    (digits : ℕ → ℕ) :
    (10 : ℝ) ^ length * ((digits index : ℝ) / 10 ^ (index + 1)) =
      (digits index : ℝ) * 10 ^ (length - 1 - index) := by
  have hsum : (index + 1) + (length - 1 - index) = length := by omega
  have hpow : (10 : ℝ) ^ (index + 1) *
      10 ^ (length - 1 - index) = 10 ^ length := by
    rw [← pow_add, hsum]
  field_simp [show (10 : ℝ) ^ (index + 1) ≠ 0 by positivity,
    show (10 : ℝ) ^ length ≠ 0 by positivity]
  nlinarith [hpow]

private lemma suffix_term_scale {start index : ℕ} (digits : ℕ → ℕ) :
    (10 : ℝ) ^ start *
        ((digits (start + index) : ℝ) / 10 ^ (start + index + 1)) =
      (digits (start + index) : ℝ) / 10 ^ (index + 1) := by
  have hpow : (10 : ℝ) ^ (start + index + 1) =
      10 ^ start * 10 ^ (index + 1) := by
    rw [← pow_add]
    ring_nf
  field_simp [show (10 : ℝ) ^ (start + index + 1) ≠ 0 by positivity,
    show (10 : ℝ) ^ (index + 1) ≠ 0 by positivity]
  nlinarith [hpow]

theorem pow_mul_decimalFraction_split {start length : ℕ}
    (hstart : start ≤ length) (digits : ℕ → ℕ) :
    (10 : ℝ) ^ start * decimalFraction length digits =
      (decimalIntegerPrefix start digits : ℝ) +
        decimalFraction (length - start) (fun index => digits (start + index)) := by
  unfold decimalFraction decimalIntegerPrefix
  rw [Finset.mul_sum]
  calc
    (∑ index ∈ Finset.range length,
        (10 : ℝ) ^ start * ((digits index : ℝ) / 10 ^ (index + 1))) =
        (∑ index ∈ Finset.range start,
          (10 : ℝ) ^ start * ((digits index : ℝ) / 10 ^ (index + 1))) +
          ∑ index ∈ Finset.Ico start length,
            (10 : ℝ) ^ start * ((digits index : ℝ) / 10 ^ (index + 1)) := by
      rw [← Finset.sum_range_add_sum_Ico _ hstart]
    _ = (∑ index ∈ Finset.range start,
          (digits index : ℝ) * 10 ^ (start - 1 - index)) +
          ∑ index ∈ Finset.Ico start length,
            (10 : ℝ) ^ start * ((digits index : ℝ) / 10 ^ (index + 1)) := by
      apply congrArg₂ (· + ·) ?_ rfl
      apply Finset.sum_congr rfl
      intro index hindex
      exact prefix_term_scale (Finset.mem_range.mp hindex) digits
    _ = (∑ index ∈ Finset.range start,
          (digits index : ℝ) * 10 ^ (start - 1 - index)) +
          ∑ index ∈ Finset.range (length - start),
            (digits (start + index) : ℝ) / 10 ^ (index + 1) := by
      congr 1
      let f : ℕ → ℝ := fun index =>
        (10 : ℝ) ^ start * ((digits index : ℝ) / 10 ^ (index + 1))
      have hshift :
          (∑ index ∈ Finset.range (length - start), f (start + index)) =
            ∑ index ∈ Finset.Ico start length, f index := by
        rw [← Nat.Ico_zero_eq_range]
        rw [Finset.sum_Ico_add f 0 (length - start) start]
        simp [Nat.sub_add_cancel hstart]
      rw [← hshift]
      apply Finset.sum_congr rfl
      intro index hindex
      exact suffix_term_scale digits
    _ = (↑(∑ index ∈ Finset.range start,
          digits index * 10 ^ (start - 1 - index)) : ℝ) +
          ∑ index ∈ Finset.range (length - start),
            (digits (start + index) : ℝ) / 10 ^ (index + 1) := by
      congr 1
      norm_cast

private lemma digit_phase_add_int (digit : ℕ) (shift : ℤ) (x : ℝ) :
    Complex.exp
        (((2 * Real.pi * (digit : ℝ) * (x + shift) : ℝ) : ℂ) * Complex.I) =
      Complex.exp
        (((2 * Real.pi * (digit : ℝ) * x : ℝ) : ℂ) * Complex.I) := by
  have harg :
      (((2 * Real.pi * (digit : ℝ) * (x + shift) : ℝ) : ℂ) * Complex.I) =
        (((2 * Real.pi * (digit : ℝ) * x : ℝ) : ℂ) * Complex.I) +
          (((digit : ℤ) * shift : ℤ) : ℂ) *
            (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem digitKernel_add_int (a : Fin 10) (x : ℝ) (shift : ℤ) :
    digitKernel a (x + shift) = digitKernel a x := by
  unfold digitKernel
  congr 2
  apply Finset.sum_congr rfl
  intro digit hdigit
  exact digit_phase_add_int digit shift x

theorem digitKernel_periodic (a : Fin 10) :
    Function.Periodic (digitKernel a) 1 := by
  intro x
  simpa using digitKernel_add_int a x (1 : ℤ)

theorem digitKernel_add_nat (a : Fin 10) (x : ℝ) (shift : ℕ) :
    digitKernel a (x + shift) = digitKernel a x := by
  exact digitKernel_add_int a x shift

theorem digitKernel_pow_mul_decimalFraction {start length : ℕ}
    (hstart : start ≤ length) (a : Fin 10) (digits : ℕ → ℕ) :
    digitKernel a ((10 : ℝ) ^ start * decimalFraction length digits) =
      digitKernel a (decimalFraction (length - start)
        (fun index => digits (start + index))) := by
  rw [pow_mul_decimalFraction_split hstart]
  rw [add_comm]
  exact digitKernel_add_nat a _ (decimalIntegerPrefix start digits)

theorem digitKernel_frequencyFactor_le_windowMajorant (a : Fin 10)
    {start length frequency J : ℕ}
    (hstart : start ≤ length) (hfrequency : frequency < 10 ^ length) :
    digitKernel a ((10 : ℝ) ^ start *
        ((frequency : ℝ) / (10 : ℝ) ^ length)) ≤
      oneSidedWindowMajorant a J
        (frequencyDigitWindow length frequency start J hfrequency) := by
  rw [← decimalFraction_frequencyDecimalDigit hfrequency]
  rw [digitKernel_pow_mul_decimalFraction hstart]
  exact digitKernel_shiftedFrequency_le_windowMajorant a hfrequency

end PrimesRestrictedDigits
