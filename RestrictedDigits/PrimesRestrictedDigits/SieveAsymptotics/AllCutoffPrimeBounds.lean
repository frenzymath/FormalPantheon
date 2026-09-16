import PrimesRestrictedDigits.SieveAsymptotics.RealCutoffPrimeLowerEnvelope
import PrimesRestrictedDigits.SieveAsymptotics.AllDigitUpperEnvelope
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Strict restricted-prime bounds at every public cutoff

The eventual lower and upper envelopes are extended over the bounded initial cutoff ranges by
elementary finite counting. The constants remain uniform in the excluded digit and the real
cutoff.

Source: `MAYNARD-PRD-PUBLISHED`, Theorem 1.1 and Section 6, p. 136.
-/

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private theorem one_le_restrictedPrimeCount_of_four_le
    {digit : Fin 10} {X : Real} (hX : 4 <= X) :
    1 <= (restrictedPrimeCount digit X : Real) := by
  have hcount : 1 <= restrictedPrimeCount digit X := by
    rw [restrictedPrimeCount]
    apply Finset.one_le_card.mpr
    by_cases hdigit : digit.val = 2
    · have hne : (3 : Nat) ≠ digit.val := by omega
      refine ⟨3, Finset.mem_filter.mpr ⟨?_, Nat.prime_three⟩⟩
      rw [mem_restrictedNumbers]
      refine And.intro (by norm_num only [Nat.cast_ofNat]; linarith) ?_
      simp [omitsDecimalDigit, standardDecimalDigits, hne]
    · have hne : (2 : Nat) ≠ digit.val := by omega
      refine ⟨2, Finset.mem_filter.mpr ⟨?_, Nat.prime_two⟩⟩
      rw [mem_restrictedNumbers]
      refine And.intro (by norm_num only [Nat.cast_ofNat]; linarith) ?_
      simp [omitsDecimalDigit, standardDecimalDigits, hne]
  have hcast : ((1 : Nat) : Real) <=
      (restrictedPrimeCount digit X : Real) := Nat.cast_le.mpr hcount
  simpa only [Nat.cast_one] using hcast

theorem exists_restrictedPrimeCount_strict_lower_bound_of_integral_sum_lt_one
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hepsilonRosser :
      2 * (Real.exp 5000 + 2) * epsilon ^ (3 : Nat) <= 1)
    (hIntegralSum :
      sectionSixFirstLowFarIntegral epsilon +
          sectionSixFirstLowCentralLargeTerminalIntegral epsilon +
        sectionSixFirstLowCentralLargeBelowIntegral epsilon +
      sectionSixFirstLowCentralLargeAboveIntegral epsilon +
        sectionSixFirstLowCentralSmallQuadrupleIntegral epsilon +
      sectionSixFirstLowBelowQuadrupleIntegral epsilon +
        sectionSixFirstHighFarIntegral epsilon +
      sectionSixFirstHighCentralLargeIntegral epsilon +
        sectionSixFirstHighCentralSmallQuadrupleIntegral epsilon < 1) :
    exists C : Real, 0 < C /\
      forall digit : Fin 10, forall X : Real, 4 <= X ->
        C * ((restrictedCount digit X : Real) / Real.log X) <
          (restrictedPrimeCount digit X : Real) := by
  obtain ⟨C0, hC0, X0, hX0, hlarge⟩ :=
    exists_restrictedPrimeCount_lower_envelope_of_integral_sum_lt_one
      epsilon hepsilon hepsilonSmall hepsilonRosser hIntegralSum
  let N : Nat := ∑ digit : Fin 10, restrictedCount digit X0
  let Csmall : Real := Real.log 4 / ((N : Real) + 1)
  let C : Real := min (C0 / 2) Csmall
  have hlogFour : 0 < Real.log (4 : Real) := Real.log_pos (by norm_num)
  have hden : 0 < (N : Real) + 1 := by positivity
  have hCsmall : 0 < Csmall := by
    dsimp only [Csmall]
    exact div_pos hlogFour hden
  have hC : 0 < C := by
    dsimp only [C]
    exact lt_min (by linarith) hCsmall
  refine ⟨C, hC, ?_⟩
  intro digit X hX
  have hlogX : 0 < Real.log X := log_pos_of_four_le hX
  have hcountPos : 0 < (restrictedCount digit X : Real) :=
    restrictedCount_pos_of_four_le hX
  have hratio : 0 < (restrictedCount digit X : Real) / Real.log X :=
    div_pos hcountPos hlogX
  by_cases hXX0 : X0 <= X
  · calc
      C * ((restrictedCount digit X : Real) / Real.log X) <=
          (C0 / 2) * ((restrictedCount digit X : Real) / Real.log X) :=
        mul_le_mul_of_nonneg_right (by
          dsimp only [C]
          exact min_le_left _ _) hratio.le
      _ < C0 * ((restrictedCount digit X : Real) / Real.log X) := by
        apply mul_lt_mul_of_pos_right _ hratio
        linarith
      _ <= (restrictedPrimeCount digit X : Real) := hlarge digit X hXX0
  · have hXlt : X < X0 := lt_of_not_ge hXX0
    have hcountNat : restrictedCount digit X <= N := by
      apply (restrictedCount_le_of_le hXlt.le).trans
      dsimp only [N]
      exact Finset.single_le_sum
        (f := fun current : Fin 10 => restrictedCount current X0)
        (fun current _ => Nat.zero_le _) (Finset.mem_univ digit)
    have hcountN : (restrictedCount digit X : Real) <= (N : Real) := by
      exact_mod_cast hcountNat
    have hCsmallBound : C <= Csmall := by
      dsimp only [C]
      exact min_le_right _ _
    have hratioN : (N : Real) / ((N : Real) + 1) < 1 := by
      rw [div_lt_iff₀ hden]
      linarith
    have hsmallN : Csmall * (N : Real) < Real.log 4 := by
      calc
        Csmall * (N : Real) =
            Real.log 4 * ((N : Real) / ((N : Real) + 1)) := by
          dsimp only [Csmall]
          ring
        _ < Real.log 4 * 1 := mul_lt_mul_of_pos_left hratioN hlogFour
        _ = Real.log 4 := mul_one _
    have hlogOrder : Real.log 4 <= Real.log X :=
      Real.log_le_log (by norm_num) hX
    have hnumerator :
        C * (restrictedCount digit X : Real) < Real.log X := by
      calc
        C * (restrictedCount digit X : Real) <=
            Csmall * (restrictedCount digit X : Real) :=
          mul_le_mul_of_nonneg_right hCsmallBound (Nat.cast_nonneg _)
        _ <= Csmall * (N : Real) :=
          mul_le_mul_of_nonneg_left hcountN hCsmall.le
        _ < Real.log 4 := hsmallN
        _ <= Real.log X := hlogOrder
    have hbelowOne :
        C * ((restrictedCount digit X : Real) / Real.log X) < 1 := by
      calc
        C * ((restrictedCount digit X : Real) / Real.log X) =
            (C * (restrictedCount digit X : Real)) / Real.log X := by ring
        _ < 1 := (div_lt_one hlogX).2 hnumerator
    exact hbelowOne.trans_le (one_le_restrictedPrimeCount_of_four_le hX)

theorem exists_restrictedPrimeCount_strict_upper_bound :
    exists C : Real, 0 < C /\
      forall digit : Fin 10, forall X : Real, 4 <= X ->
        (restrictedPrimeCount digit X : Real) <
          C * ((restrictedCount digit X : Real) / Real.log X) := by
  obtain ⟨C0, hC0, X0, hX0, hlarge⟩ :=
    exists_restrictedPrimeCount_strict_upper_envelope
  let C : Real := max C0 (Real.log X0 + 1)
  have hC : 0 < C := by
    dsimp only [C]
    exact hC0.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro digit X hX
  have hlogX : 0 < Real.log X := log_pos_of_four_le hX
  have hratio : 0 < (restrictedCount digit X : Real) / Real.log X :=
    div_pos (restrictedCount_pos_of_four_le hX) hlogX
  by_cases hXX0 : X0 <= X
  · calc
      (restrictedPrimeCount digit X : Real) <
          C0 * ((restrictedCount digit X : Real) / Real.log X) :=
        hlarge digit X hXX0
      _ <= C * ((restrictedCount digit X : Real) / Real.log X) :=
        mul_le_mul_of_nonneg_right (by
          dsimp only [C]
          exact le_max_left _ _) hratio.le
  · have hXlt : X < X0 := lt_of_not_ge hXX0
    have hprimeNat :
        restrictedPrimeCount digit X <= restrictedCount digit X := by
      simpa [restrictedPrimeCount, restrictedCount] using
        (Finset.card_filter_le (restrictedNumbers digit X) Nat.Prime)
    have hprimeCount :
        (restrictedPrimeCount digit X : Real) <=
          (restrictedCount digit X : Real) := by
      exact_mod_cast hprimeNat
    have hlogOrder : Real.log X <= Real.log X0 :=
      Real.log_le_log (by linarith) hXlt.le
    have hlogLtC : Real.log X < C := by
      calc
        Real.log X <= Real.log X0 := hlogOrder
        _ < Real.log X0 + 1 := by linarith
        _ <= C := by
          dsimp only [C]
          exact le_max_right _ _
    have hcountEq :
        (restrictedCount digit X : Real) =
          Real.log X * ((restrictedCount digit X : Real) / Real.log X) := by
      field_simp
    calc
      (restrictedPrimeCount digit X : Real) <=
          (restrictedCount digit X : Real) := hprimeCount
      _ = Real.log X *
          ((restrictedCount digit X : Real) / Real.log X) := hcountEq
      _ < C * ((restrictedCount digit X : Real) / Real.log X) :=
        mul_lt_mul_of_pos_right hlogLtC hratio

end

end PrimesRestrictedDigits
