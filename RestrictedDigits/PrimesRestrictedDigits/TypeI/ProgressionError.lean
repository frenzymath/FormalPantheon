import PrimesRestrictedDigits.Fourier.ContinuousTransformProperties
import PrimesRestrictedDigits.TypeI.AdditiveCharacterIdentity
import PrimesRestrictedDigits.TypeI.DenominatorReduction
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Type I progression error

This extracts the modulus-one main block from the exact character identity and bounds the
remaining frequencies by the corrected reduced carrier.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- The fully reduced nontrivial Fourier sum in the proof of published
Proposition 7.1. -/
noncomputable def typeIReducedErrorFourierSum
    (digit : Fin 10) (length q : Nat) : Real :=
  ∑ d' ∈ Nat.divisors 10,
    ∑ q' ∈ (Nat.divisors q).filter (fun q' => 1 < q'),
      ∑ b'' ∈ (Finset.range (d' * q')).filter
          (fun b'' => Nat.Coprime b'' (d' * q')),
        normalizedPaddedDigitFourierMagnitudeAt digit length
          ((b'' : Real) / ((d' * q' : Nat) : Real))

private theorem typeIReducedRange_filter_eq
    {q d' q' : Nat} (hq : 0 < q) (hd' : d' ∈ Nat.divisors 10)
    (hq' : q' ∈ Nat.divisors q) :
    (Finset.range (10 * q)).filter (fun b'' =>
        b'' < d' * q' ∧ Nat.Coprime b'' (d' * q')) =
      (Finset.range (d' * q')).filter
        (fun b'' => Nat.Coprime b'' (d' * q')) := by
  have hd'Le : d' ≤ 10 := Nat.le_of_dvd (by norm_num)
    (Nat.dvd_of_mem_divisors hd')
  have hq'Le : q' ≤ q := Nat.le_of_dvd hq
    (Nat.dvd_of_mem_divisors hq')
  have hdenLe : d' * q' ≤ 10 * q := Nat.mul_le_mul hd'Le hq'Le
  ext b''
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, hb'', hcoprime⟩
    exact ⟨hb'', hcoprime⟩
  · rintro ⟨hb'', hcoprime⟩
    exact ⟨hb''.trans_le hdenLe, hb'', hcoprime⟩

private theorem sum_typeINontrivialQSplitCarrier_eq
    {q : Nat} (hq : 0 < q) (f : Real → Real) :
    (∑ index ∈ typeINontrivialQSplitCarrier 10 q,
      f (typeISplitFractionValue index)) =
      ∑ d' ∈ Nat.divisors 10,
        ∑ q' ∈ (Nat.divisors q).filter (fun q' => 1 < q'),
          ∑ b'' ∈ (Finset.range (d' * q')).filter
              (fun b'' => Nat.Coprime b'' (d' * q')),
            f ((b'' : Real) / ((d' * q' : Nat) : Real)) := by
  classical
  simp only [typeINontrivialQSplitCarrier, typeISplitReducedCarrier,
    Finset.sum_filter, typeISplitFractionValue]
  refine Eq.trans (Finset.sum_product
    ((Nat.divisors 10).product (Nat.divisors q))
    (Finset.range (10 * q))
    (fun index : TypeISplitIndex =>
      if index.2 < index.1.1 * index.1.2 ∧
          index.2.Coprime (index.1.1 * index.1.2) then
        if 1 < index.1.2 then f
          ((index.2 : Real) / ((index.1.1 * index.1.2 : Nat) : Real)) else 0
      else 0)) ?_
  refine Eq.trans (Finset.sum_product
    (Nat.divisors 10) (Nat.divisors q)
    (fun pair : Nat × Nat =>
      ∑ b'' ∈ Finset.range (10 * q),
        if b'' < pair.1 * pair.2 ∧ b''.Coprime (pair.1 * pair.2) then
          if 1 < pair.2 then
            f ((b'' : Real) / ((pair.1 * pair.2 : Nat) : Real)) else 0
        else 0)) ?_
  apply Finset.sum_congr rfl
  intro d' hd'
  apply Finset.sum_congr rfl
  intro q' hq'
  by_cases hq'Nontrivial : 1 < q'
  · rw [if_pos hq'Nontrivial]
    rw [← Finset.sum_filter]
    rw [typeIReducedRange_filter_eq hq hd' hq']
    simp [Finset.sum_filter, hq'Nontrivial]
  · rw [if_neg hq'Nontrivial]
    simp [hq'Nontrivial]

private theorem sum_filter_dvd_eq_sum_range_mul
    {M : Type*} [AddCommMonoid M] (d q : Nat) (hq : 0 < q)
    (f : Nat → M) :
    (∑ b ∈ (Finset.range (d * q)).filter (fun b => q ∣ b), f b) =
      ∑ c ∈ Finset.range d, f (c * q) := by
  classical
  symm
  apply Finset.sum_bij (fun c _ => c * q)
  · intro c hc
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_range.mpr ?_, dvd_mul_left q c⟩
    exact Nat.mul_lt_mul_of_pos_right (Finset.mem_range.mp hc) hq
  · intro c₁ hc₁ c₂ hc₂ h
    exact Nat.eq_of_mul_eq_mul_right hq h
  · intro b hb
    rcases Finset.mem_filter.mp hb with ⟨hbRange, ⟨c, rfl⟩⟩
    refine ⟨c, Finset.mem_range.mpr ?_, Nat.mul_comm c q⟩
    exact (Nat.mul_lt_mul_right hq).mp (by
      simpa [Nat.mul_comm] using Finset.mem_range.mp hbRange)
  · intro c hc
    rfl

private theorem paddedFourier_sum_filter_dvd_eq
    (digit : Fin 10) (length d q : Nat) (hd : 0 < d) (hq : 0 < q) :
    (∑ b ∈ (Finset.range (d * q)).filter (fun b => q ∣ b),
      paddedDigitFourierSumAt digit length
        ((b : Real) / ((d * q : Nat) : Real))) =
      ∑ c ∈ Finset.range d,
        paddedDigitFourierSumAt digit length
          ((c : Real) / (d : Real)) := by
  rw [sum_filter_dvd_eq_sum_range_mul d q hq]
  apply Finset.sum_congr rfl
  intro c hc
  congr 1
  push_cast
  field_simp

private theorem typeIMainBlock_eq_coprimeCard_div
    (digit : Fin 10) (length q : Nat) (hq10 : Nat.Coprime q 10) :
    (∑ d ∈ Nat.divisors 10,
      (ArithmeticFunction.moebius d : Complex) /
          ((d * q : Nat) : Complex) *
        ∑ b ∈ (Finset.range (d * q)).filter (fun b => q ∣ b),
          paddedDigitFourierSumAt digit length
            ((b : Real) / ((d * q : Nat) : Real))) =
      (((((paddedRestrictedNumbers digit length).filter
        (fun n => Nat.Coprime n 10)).card : Complex)) / (q : Complex)) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (by
    intro h
    subst q
    norm_num [Nat.Coprime] at hq10)
  have hidentity :=
    card_filter_dvd_coprime_paddedRestrictedNumbers_eq_moebius_fourier
      digit length 1 (by norm_num)
  simp only [one_dvd, true_and, Nat.mul_one] at hidentity
  rw [hidentity]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hdMem
  have hd : 0 < d := Nat.pos_of_ne_zero
    (ne_zero_of_dvd_ne_zero (by norm_num) (Nat.dvd_of_mem_divisors hdMem))
  rw [paddedFourier_sum_filter_dvd_eq digit length d q hd hq]
  push_cast
  field_simp

private theorem typeIErrorBlock_eq
    (digit : Fin 10) (length q : Nat) (hq10 : Nat.Coprime q 10) :
    (((paddedRestrictedNumbers digit length).filter
          (fun n => q ∣ n ∧ Nat.Coprime n 10)).card : Complex) -
        (((paddedRestrictedNumbers digit length).filter
          (fun n => Nat.Coprime n 10)).card : Complex) / (q : Complex) =
      ∑ d ∈ Nat.divisors 10,
        (ArithmeticFunction.moebius d : Complex) /
            ((d * q : Nat) : Complex) *
          ∑ b ∈ (Finset.range (d * q)).filter (fun b => ¬q ∣ b),
            paddedDigitFourierSumAt digit length
              ((b : Real) / ((d * q : Nat) : Real)) := by
  rw [card_filter_dvd_coprime_paddedRestrictedNumbers_eq_moebius_fourier
    digit length q hq10]
  rw [← typeIMainBlock_eq_coprimeCard_div digit length q hq10]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← mul_sub]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.range (d * q)) (fun b => q ∣ b)
    (fun b => paddedDigitFourierSumAt digit length
      ((b : Real) / ((d * q : Nat) : Real)))]
  abel

private theorem norm_moebius_div_mul_le_inv
    {d q : Nat} (hd : 0 < d) (hq : 0 < q) :
    ‖(ArithmeticFunction.moebius d : Complex) /
        ((d * q : Nat) : Complex)‖ ≤ 1 / (q : Real) := by
  have hmoebius :
      ‖(ArithmeticFunction.moebius d : Complex)‖ ≤ 1 := by
    have h : (((|ArithmeticFunction.moebius d| : Int) : Real)) ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
    simpa [Complex.norm_intCast, ← Int.cast_abs] using h
  have hdenominator : (q : Real) ≤ ((d * q : Nat) : Real) := by
    exact_mod_cast Nat.le_mul_of_pos_left q hd
  rw [norm_div, Complex.norm_natCast]
  exact div_le_div₀ zero_le_one hmoebius (by exact_mod_cast hq) hdenominator

private theorem norm_paddedDigitFourierSumAt_eq_card_mul_normalized
    (digit : Fin 10) (length : Nat) (theta : Real) :
    ‖paddedDigitFourierSumAt digit length theta‖ =
      ((paddedRestrictedNumbers digit length).card : Real) *
        normalizedPaddedDigitFourierMagnitudeAt digit length theta := by
  rw [normalizedPaddedDigitFourierMagnitudeAt,
    card_paddedRestrictedNumbers]
  push_cast
  field_simp

private theorem norm_typeIExactError_le_sourceSum
    (digit : Fin 10) (length q : Nat) (hq10 : Nat.Coprime q 10) :
    ‖(((paddedRestrictedNumbers digit length).filter
        (fun n => q ∣ n ∧ Nat.Coprime n 10)).card : Complex) -
      (((paddedRestrictedNumbers digit length).filter
        (fun n => Nat.Coprime n 10)).card : Complex) / (q : Complex)‖ ≤
      (((paddedRestrictedNumbers digit length).card : Real) / (q : Real)) *
        ∑ d ∈ Nat.divisors 10,
          ∑ b ∈ (Finset.range (d * q)).filter (fun b => ¬q ∣ b),
            normalizedPaddedDigitFourierMagnitudeAt digit length
              ((b : Real) / ((d * q : Nat) : Real)) := by
  rw [typeIErrorBlock_eq digit length q hq10]
  calc
    ‖∑ d ∈ Nat.divisors 10,
        (ArithmeticFunction.moebius d : Complex) /
            ((d * q : Nat) : Complex) *
          ∑ b ∈ (Finset.range (d * q)).filter (fun b => ¬q ∣ b),
            paddedDigitFourierSumAt digit length
              ((b : Real) / ((d * q : Nat) : Real))‖ ≤
        ∑ d ∈ Nat.divisors 10,
          ‖(ArithmeticFunction.moebius d : Complex) /
              ((d * q : Nat) : Complex) *
            ∑ b ∈ (Finset.range (d * q)).filter (fun b => ¬q ∣ b),
              paddedDigitFourierSumAt digit length
                ((b : Real) / ((d * q : Nat) : Real))‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ Nat.divisors 10,
        (((paddedRestrictedNumbers digit length).card : Real) / (q : Real)) *
          ∑ b ∈ (Finset.range (d * q)).filter (fun b => ¬q ∣ b),
            normalizedPaddedDigitFourierMagnitudeAt digit length
              ((b : Real) / ((d * q : Nat) : Real)) := by
      apply Finset.sum_le_sum
      intro d hd
      have hq : 0 < q := Nat.pos_of_ne_zero (by
        intro h
        subst q
        norm_num [Nat.Coprime] at hq10)
      have hdPos : 0 < d := Nat.pos_of_ne_zero
        (ne_zero_of_dvd_ne_zero (by norm_num) (Nat.dvd_of_mem_divisors hd))
      have hscalar := norm_moebius_div_mul_le_inv hdPos hq
      calc
        ‖(ArithmeticFunction.moebius d : Complex) /
              ((d * q : Nat) : Complex) *
            ∑ b ∈ (Finset.range (d * q)).filter (fun b => ¬q ∣ b),
              paddedDigitFourierSumAt digit length
                ((b : Real) / ((d * q : Nat) : Real))‖ =
            ‖(ArithmeticFunction.moebius d : Complex) /
              ((d * q : Nat) : Complex)‖ *
              ‖∑ b ∈ (Finset.range (d * q)).filter (fun b => ¬q ∣ b),
                paddedDigitFourierSumAt digit length
                  ((b : Real) / ((d * q : Nat) : Real))‖ := norm_mul _ _
        _ ≤ ‖(ArithmeticFunction.moebius d : Complex) /
              ((d * q : Nat) : Complex)‖ *
            ∑ b ∈ (Finset.range (d * q)).filter (fun b => ¬q ∣ b),
              ‖paddedDigitFourierSumAt digit length
                ((b : Real) / ((d * q : Nat) : Real))‖ := by
          gcongr
          exact norm_sum_le _ _
        _ ≤ (1 / (q : Real)) *
            ∑ b ∈ (Finset.range (d * q)).filter (fun b => ¬q ∣ b),
              ‖paddedDigitFourierSumAt digit length
                ((b : Real) / ((d * q : Nat) : Real))‖ := by
          gcongr
        _ = (((paddedRestrictedNumbers digit length).card : Real) / (q : Real)) *
            ∑ b ∈ (Finset.range (d * q)).filter (fun b => ¬q ∣ b),
              normalizedPaddedDigitFourierMagnitudeAt digit length
                ((b : Real) / ((d * q : Nat) : Real)) := by
          simp_rw [norm_paddedDigitFourierSumAt_eq_card_mul_normalized]
          rw [← Finset.mul_sum]
          ring
    _ = (((paddedRestrictedNumbers digit length).card : Real) / (q : Real)) *
        ∑ d ∈ Nat.divisors 10,
          ∑ b ∈ (Finset.range (d * q)).filter (fun b => ¬q ∣ b),
            normalizedPaddedDigitFourierMagnitudeAt digit length
              ((b : Real) / ((d * q : Nat) : Real)) := by
      rw [Finset.mul_sum]

/-- Corrected explicit denominator-reduction estimate in the proof of
published Proposition 7.1. The coefficient four bounds the non-injective
fibers across the four original divisors of ten. -/
theorem norm_typeIProgressionCount_sub_coprimeMain_le
    (digit : Fin 10) (length q : Nat) (hq10 : Nat.Coprime q 10) :
    ‖(((paddedRestrictedNumbers digit length).filter
        (fun n => q ∣ n ∧ Nat.Coprime n 10)).card : Complex) -
      (((paddedRestrictedNumbers digit length).filter
        (fun n => Nat.Coprime n 10)).card : Complex) / (q : Complex)‖ ≤
    4 * (((paddedRestrictedNumbers digit length).card : Real) / (q : Real)) *
      typeIReducedErrorFourierSum digit length q := by
  have hq : 0 < q := Nat.pos_of_ne_zero (by
    intro h
    subst q
    norm_num [Nat.Coprime] at hq10)
  have hReduction :
      (∑ d ∈ Nat.divisors 10,
        ∑ b ∈ (Finset.range (d * q)).filter (fun b => ¬q ∣ b),
          normalizedPaddedDigitFourierMagnitudeAt digit length
            ((b : Real) / ((d * q : Nat) : Real))) ≤
        4 * typeIReducedErrorFourierSum digit length q := by
    calc
      _ ≤ 4 * ∑ index ∈ typeINontrivialQSplitCarrier 10 q,
          normalizedPaddedDigitFourierMagnitudeAt digit length
            (typeISplitFractionValue index) :=
        sum_divisors_ten_typeIErrorFraction_le hq hq10
          (normalizedPaddedDigitFourierMagnitudeAt digit length)
          (normalizedPaddedDigitFourierMagnitudeAt_nonneg digit length)
      _ = 4 * typeIReducedErrorFourierSum digit length q := by
        rw [sum_typeINontrivialQSplitCarrier_eq hq]
        rfl
  have hscale :
      0 ≤ ((paddedRestrictedNumbers digit length).card : Real) / (q : Real) := by
    positivity
  calc
    _ ≤ (((paddedRestrictedNumbers digit length).card : Real) / (q : Real)) *
        ∑ d ∈ Nat.divisors 10,
          ∑ b ∈ (Finset.range (d * q)).filter (fun b => ¬q ∣ b),
            normalizedPaddedDigitFourierMagnitudeAt digit length
              ((b : Real) / ((d * q : Nat) : Real)) :=
      norm_typeIExactError_le_sourceSum digit length q hq10
    _ ≤ (((paddedRestrictedNumbers digit length).card : Real) / (q : Real)) *
        (4 * typeIReducedErrorFourierSum digit length q) :=
      mul_le_mul_of_nonneg_left hReduction hscale
    _ = 4 * (((paddedRestrictedNumbers digit length).card : Real) / (q : Real)) *
        typeIReducedErrorFourierSum digit length q := by ring

end PrimesRestrictedDigits
