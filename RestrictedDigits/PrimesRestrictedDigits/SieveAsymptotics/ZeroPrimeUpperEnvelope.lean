import PrimesRestrictedDigits.SieveAsymptotics.FixedLengthPrimeUpperEnvelope
import PrimesRestrictedDigits.SieveAsymptotics.ZeroPrimeBlockPaddedBridge
import PrimesRestrictedDigits.Foundations.CutoffMonotonicity
import PrimesRestrictedDigits.Foundations.DecimalScale
import PrimesRestrictedDigits.Foundations.GeometricPowOverIndex
import PrimesRestrictedDigits.Foundations.RestrictedCountPositivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Excluded-zero real-cutoff prime upper envelope

The positive digit-length blocks for the excluded-zero case are summed after the fixed-length
prime estimate. The finite initial lengths are absorbed in one coefficient, and the
geometric-over-index lemma controls the resulting block sum.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, p. 136.
-/

namespace PrimesRestrictedDigits

noncomputable section

private theorem log_decimal_scale_ge_length {length : Nat} (hlength : 1 <= length) :
    (length : Real) <= Real.log (((10 ^ length : Nat) : Real)) := by
  have hlog10 : (1 : Real) <= Real.log 10 := by
    have hstrict : (1 : Real) < Real.log 10 :=
      (Real.lt_log_iff_exp_lt (by norm_num)).2
        (Real.exp_one_lt_three.trans_le (by norm_num))
    exact hstrict.le
  rw [Nat.cast_pow, Real.log_pow]
  have hmul : (length : Real) * 1 <=
      (length : Real) * Real.log 10 :=
    mul_le_mul_of_nonneg_left hlog10 (by positivity)
  simpa using hmul

theorem exists_paddedRestrictedPrimeCount_over_length_upper :
    ∃ B : Real, 0 < B ∧
      ∀ length : Nat, 1 <= length ->
        (paddedRestrictedPrimeCount (0 : Fin 10) length : Real) <=
          B * (9 : Real) ^ length / (length : Real) := by
  obtain ⟨C0, hC0, length0, hlength0, hupper⟩ :=
    exists_paddedRestrictedPrimeCount_upper_envelope
  refine ⟨C0 + (length0 : Real), by positivity, ?_⟩
  intro length hlength
  by_cases hlarge : length0 <= length
  · have hfixed := hupper length hlarge (0 : Fin 10)
    dsimp only at hfixed
    have hcard :
        (paddedRestrictedNumbers (0 : Fin 10) length).card = 9 ^ length :=
      card_paddedRestrictedNumbers (0 : Fin 10) length
    rw [hcard] at hfixed
    have hfixed' :
        (paddedRestrictedPrimeCount (0 : Fin 10) length : Real) <=
          C0 * (9 : Real) ^ length /
            Real.log (((10 ^ length : Nat) : Real)) := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using hfixed
    have hlog := log_decimal_scale_ge_length hlength
    have hlogPos : 0 < Real.log (((10 ^ length : Nat) : Real)) := by
      exact lt_of_lt_of_le (by positivity) hlog
    have hlenPos : 0 < (length : Real) := by positivity
    have hnumNonneg : 0 <= C0 * (9 : Real) ^ length := by positivity
    have hden := div_le_div_of_nonneg_left hnumNonneg hlenPos hlog
    have hcoef : C0 * (9 : Real) ^ length <=
        (C0 + (length0 : Real)) * (9 : Real) ^ length := by
      apply mul_le_mul_of_nonneg_right
      · linarith
      · positivity
    have hcoefDiv := div_le_div_of_nonneg_right hcoef hlenPos.le
    exact hfixed'.trans (hden.trans hcoefDiv)
  · have hlt : length < length0 := Nat.lt_of_not_ge hlarge
    have hle : length <= length0 := hlt.le
    have hleReal : (length : Real) <= (length0 : Real) := by
      exact_mod_cast hle
    have hprimeNat :
        paddedRestrictedPrimeCount (0 : Fin 10) length <=
          (paddedRestrictedNumbers (0 : Fin 10) length).card := by
      exact Finset.card_filter_le _ _
    have hprime :
        (paddedRestrictedPrimeCount (0 : Fin 10) length : Real) <=
          (9 : Real) ^ length := by
      exact_mod_cast (hprimeNat.trans_eq
        (card_paddedRestrictedNumbers (0 : Fin 10) length))
    have hlenPos : 0 < (length : Real) := by positivity
    have hpowPos : 0 < (9 : Real) ^ length := by positivity
    have hbound : (length : Real) <= C0 + (length0 : Real) := by
      linarith
    have hscaled : (9 : Real) ^ length <=
        (C0 + (length0 : Real)) * (9 : Real) ^ length / (length : Real) := by
      apply (le_div_iff₀ hlenPos).2
      nlinarith
    exact hprime.trans hscaled

theorem exists_restrictedPrimeCount_upper_envelope_of_zero :
    ∃ C : Real, 0 < C ∧ ∃ X0 : Real, 4 <= X0 ∧
      ∀ X : Real, X0 <= X ->
        (restrictedPrimeCount (0 : Fin 10) X : Real) <=
          C * (restrictedCount (0 : Fin 10) X : Real) / Real.log X := by
  obtain ⟨B, hB, hblock⟩ := exists_paddedRestrictedPrimeCount_over_length_upper
  let X0 : Real := 10
  refine ⟨162 * B, by positivity, X0, by norm_num, ?_⟩
  intro X hX
  obtain ⟨k, hlo, hupp⟩ := exists_decimalPower_interval (show (4 : Real) <= X by
    dsimp [X0] at hX
    linarith)
  have hk : 1 <= k := by
    by_contra hk0
    have hkz : k = 0 := Nat.eq_zero_of_not_pos hk0
    subst k
    norm_num at hupp
    linarith
  have hK : 1 <= k + 1 := by omega
  have hsumNat := restrictedPrimeCount_zero_cutoff_block_sandwich hlo hupp
  have hsumReal :
      (restrictedPrimeCount (0 : Fin 10) X : Real) <=
        ∑ i ∈ Finset.range (k + 1),
          ((zeroRestrictedPrimeBlock i).card : Real) := by
    have hsumReal0 :
        (restrictedPrimeCount (0 : Fin 10) X : Real) <=
          ((∑ i ∈ Finset.range (k + 1),
            (zeroRestrictedPrimeBlock i).card : Nat) : Real) := by
      exact_mod_cast hsumNat.2
    simpa only [Nat.cast_sum] using hsumReal0
  have hblockBound : ∀ i ∈ Finset.range (k + 1),
      ((zeroRestrictedPrimeBlock i).card : Real) <=
        B * (9 : Real) ^ (i + 1) / (i + 1 : Real) := by
    intro i hi
    have hiLength : 1 <= i + 1 := by omega
    have hbi := hblock (i + 1) hiLength
    have heq :
        (zeroRestrictedPrimeBlock i).card =
          paddedRestrictedPrimeCount (0 : Fin 10) (i + 1) := by
      rw [zeroRestrictedPrimeBlock_eq_paddedRestrictedPrimes]
      rfl
    rw [heq]
    simpa using hbi
  have hsumBound :
      (∑ i ∈ Finset.range (k + 1),
          (zeroRestrictedPrimeBlock i).card : Real) <=
        ∑ i ∈ Finset.range (k + 1),
          B * (9 : Real) ^ (i + 1) / (i + 1 : Real) := by
    apply Finset.sum_le_sum
    intro i hi
    exact hblockBound i hi
  have hgeom0 := sum_nine_pow_over_index_le (k + 1) hK
  have hgeom :
      (∑ i ∈ Finset.range (k + 1),
          (9 : Real) ^ (i + 1) / (i + 1 : Real)) <=
        2 * (9 : Real) ^ (k + 1) / (k + 1 : Real) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hgeom0
  have hsumGeom :
      (∑ i ∈ Finset.range (k + 1),
          B * (9 : Real) ^ (i + 1) / (i + 1 : Real)) <=
        B * (2 * (9 : Real) ^ (k + 1) / (k + 1 : Real)) := by
    calc
      (∑ i ∈ Finset.range (k + 1),
          B * (9 : Real) ^ (i + 1) / (i + 1 : Real)) =
          B * (∑ i ∈ Finset.range (k + 1),
            (9 : Real) ^ (i + 1) / (i + 1 : Real)) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              ring
      _ <= B * (2 * (9 : Real) ^ (k + 1) / (k + 1 : Real)) := by
        exact mul_le_mul_of_nonneg_left hgeom hB.le
  have hagg :
      (restrictedPrimeCount (0 : Fin 10) X : Real) <=
        B * (2 * (9 : Real) ^ (k + 1) / (k + 1 : Real)) :=
    hsumReal.trans (hsumBound.trans hsumGeom)
  have hcountLowerNat :
      9 ^ k <= restrictedCount (0 : Fin 10)
        (((10 ^ k : Nat) : Real)) := by
    rw [restrictedCount_zero_power]
    have hmem : k - 1 ∈ Finset.range k := by
      rw [Finset.mem_range]
      omega
    have hterm : (9 : Nat) ^ ((k - 1) + 1) <=
        ∑ i ∈ Finset.range k, 9 ^ (i + 1) :=
      Finset.single_le_sum (f := fun i : Nat => (9 : Nat) ^ (i + 1))
        (fun i hi => Nat.zero_le _) hmem
    simpa [Nat.sub_add_cancel hk] using hterm
  have hcountLower : (9 : Real) ^ k <=
      (restrictedCount (0 : Fin 10) X : Real) := by
    have hmono := restrictedCount_le_of_le (a := (0 : Fin 10)) hlo
    exact_mod_cast hcountLowerNat.trans hmono
  have hlogX : 0 < Real.log X :=
    log_pos_of_four_le (show (4 : Real) <= X by
      dsimp [X0] at hX
      linarith)
  have hlogUpper : Real.log X <=
      (k + 1 : Real) * Real.log 10 := by
    have hlogOrder : Real.log X <=
        Real.log ((10 ^ (k + 1) : Nat) : Real) := by
      exact Real.log_le_log (by linarith) hupp.le
    rw [Nat.cast_pow, Real.log_pow] at hlogOrder
    convert hlogOrder using 1; norm_num
  have hKReal : 0 < (k + 1 : Real) := by positivity
  have hlog10Pos : 0 < Real.log (10 : Real) := log_ten_pos
  have hlog10Upper : Real.log (10 : Real) <= 9 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 10)
    linarith
  have hfrac : (1 : Real) / (k + 1 : Real) <=
      Real.log 10 / Real.log X := by
    apply (div_le_div_iff₀ hKReal hlogX).2
    nlinarith [hlogUpper]
  have hpowNonneg : 0 <= (9 : Real) ^ (k + 1) := by positivity
  have hscale := mul_le_mul_of_nonneg_left hfrac
    (show 0 <= 2 * B * (9 : Real) ^ (k + 1) by positivity)
  have haggLog :
      B * (2 * (9 : Real) ^ (k + 1) / (k + 1 : Real)) <=
        18 * B * (9 : Real) ^ (k + 1) / Real.log X := by
    calc
      B * (2 * (9 : Real) ^ (k + 1) / (k + 1 : Real)) =
          (2 * B * (9 : Real) ^ (k + 1)) *
            (1 / (k + 1 : Real)) := by ring
      _ <= (2 * B * (9 : Real) ^ (k + 1)) *
            (Real.log 10 / Real.log X) := hscale
      _ <= (2 * B * (9 : Real) ^ (k + 1)) *
            (9 / Real.log X) := by
        apply mul_le_mul_of_nonneg_left
        · exact div_le_div_of_nonneg_right hlog10Upper hlogX.le
        · positivity
      _ = 18 * B * (9 : Real) ^ (k + 1) / Real.log X := by ring
  have hnum : 18 * B * (9 : Real) ^ (k + 1) <=
      162 * B * (restrictedCount (0 : Fin 10) X : Real) := by
    have hmul := mul_le_mul_of_nonneg_left hcountLower
      (show 0 <= 162 * B by positivity)
    calc
      18 * B * (9 : Real) ^ (k + 1) =
          162 * B * (9 : Real) ^ k := by rw [pow_succ]; ring
      _ <= 162 * B * (restrictedCount (0 : Fin 10) X : Real) := hmul
  have hnumDiv := div_le_div_of_nonneg_right hnum hlogX.le
  exact hagg.trans (haggLog.trans hnumDiv)

theorem exists_restrictedPrimeCount_strict_upper_envelope_of_zero :
    ∃ C : Real, 0 < C ∧ ∃ X0 : Real, 4 <= X0 ∧
      ∀ X : Real, X0 <= X ->
        (restrictedPrimeCount (0 : Fin 10) X : Real) <
          C * ((restrictedCount (0 : Fin 10) X : Real) / Real.log X) := by
  obtain ⟨C0, hC0, X0, hX0, hweak⟩ :=
    exists_restrictedPrimeCount_upper_envelope_of_zero
  refine ⟨2 * C0, by positivity, X0, hX0, ?_⟩
  intro X hX
  have hweak' := hweak X hX
  have hlog : 0 < Real.log X := log_pos_of_four_le (hX0.trans hX)
  have hcount : 0 < (restrictedCount (0 : Fin 10) X : Real) :=
    restrictedCount_pos_of_four_le (hX0.trans hX)
  have hratio : 0 <
      (restrictedCount (0 : Fin 10) X : Real) / Real.log X :=
    div_pos hcount hlog
  have hCratio : 0 < C0 *
      ((restrictedCount (0 : Fin 10) X : Real) / Real.log X) :=
    mul_pos hC0 hratio
  calc
    (restrictedPrimeCount (0 : Fin 10) X : Real) <=
        C0 * ((restrictedCount (0 : Fin 10) X : Real) / Real.log X) := by
      convert hweak' using 1; ring
    _ < (2 * C0) *
        ((restrictedCount (0 : Fin 10) X : Real) / Real.log X) := by
      nlinarith

end

end PrimesRestrictedDigits
