import PrimesRestrictedDigits.SieveAsymptotics.FundamentalLargeDeltaReduction
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Corrected Fundamental Lemma

The fixed-epsilon Fundamental Lemma holds for every positive delta. The endpoint
`delta = epsilon^4` belongs to the small branch.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

theorem exists_correctedFundamentalLemma :
    ∀ epsilon : Real, 0 < epsilon -> epsilon <= 1 / 64 ->
      2 * (Real.exp 5000 + 2) * epsilon ^ (3 : Nat) <= 1 ->
      ∃ C : Real, 1 <= C ∧
        ∃ length0 : Nat, 1 <= length0 ∧
          ∀ length : Nat, length0 <= length ->
            ∀ (digit : Fin 10) (delta : Real),
              0 < delta ->
              let X : Real := ((10 ^ length : Nat) : Real)
              5 <= X ^ delta ->
              (∑ d ∈ maynardStrictRoughCarrier
                  (X ^ (50 / 77 - epsilon)) (X ^ delta),
                |((strictSiftedCarrier
                    (sieveDilation
                      (paddedRestrictedNumbers digit length) d.toPNat')
                    (X ^ delta)).card : Real) -
                  (restrictedDigitDensity digit : Real) *
                    ((paddedRestrictedNumbers digit length).card : Real) / X *
                  ((strictSiftedCarrier
                    (sieveDilation (maynardAmbientCarrier X) d.toPNat')
                    (X ^ delta)).card : Real)|) <=
                C * ((paddedRestrictedNumbers digit length).card : Real) *
                    Real.exp (-(delta ^ (-(2 / 3 : Real)))) / Real.log X +
                  C * ((paddedRestrictedNumbers digit length).card : Real) /
                    Real.log X ^ (100 : Nat) := by
  intro epsilon hepsilon hepsilonSmall hepsilonRosser
  obtain ⟨Csmall, hCsmall, hSmall⟩ :=
    exists_correctedFundamentalSmallDeltaSplit
  obtain ⟨lengthSmall, _, hlengthSmall⟩ :=
    hSmall epsilon hepsilon hepsilonSmall hepsilonRosser
  obtain ⟨Clarge, hClarge, lengthLarge, _, hlengthLarge⟩ :=
    exists_correctedFundamentalLargeDeltaReduction epsilon hepsilon
      hepsilonSmall hepsilonRosser
  let C : Real := max Csmall Clarge
  have hC : 1 <= C := hCsmall.trans (le_max_left _ _)
  have hCsmallC : Csmall <= C := le_max_left _ _
  have hClargeC : Clarge <= C := le_max_right _ _
  refine ⟨C, hC, ?_⟩
  let length0 : Nat := max 1 (max lengthSmall lengthLarge)
  refine ⟨length0, ?_, ?_⟩
  · dsimp [length0]
    omega
  · intro length hlength digit delta hdelta
    dsimp
    intro hcutoff
    have hrest : max lengthSmall lengthLarge <= length :=
      (Nat.le_max_right 1 _).trans hlength
    have hlengthSmall' : lengthSmall <= length :=
      (Nat.le_max_left _ _).trans hrest
    have hlengthLarge' : lengthLarge <= length :=
      (Nat.le_max_right _ _).trans hrest
    have hlengthOne : 1 <= length := by
      have hone : 1 <= length0 := by
        dsimp [length0]
        omega
      exact hone.trans hlength
    have hX : 1 < ((10 ^ length : Nat) : Real) := by
      exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
        (by norm_num : 1 < (10 : Nat))
    have hlogX : 0 < Real.log ((10 ^ length : Nat) : Real) :=
      Real.log_pos hX
    by_cases hsmall : delta <= epsilon ^ (4 : Nat)
    · have hbound := hlengthSmall length hlengthSmall' digit delta
        hdelta hsmall
      dsimp at hbound
      have hbound := hbound hcutoff
      calc
        _ <= Csmall * ((paddedRestrictedNumbers digit length).card : Real) *
              Real.exp (-(delta ^ (-(2 / 3 : Real)))) /
                Real.log ((10 ^ length : Nat) : Real) +
            Csmall * ((paddedRestrictedNumbers digit length).card : Real) /
              Real.log ((10 ^ length : Nat) : Real) ^ (100 : Nat) := hbound
        _ <= C * ((paddedRestrictedNumbers digit length).card : Real) *
              Real.exp (-(delta ^ (-(2 / 3 : Real)))) /
                Real.log ((10 ^ length : Nat) : Real) +
            C * ((paddedRestrictedNumbers digit length).card : Real) /
              Real.log ((10 ^ length : Nat) : Real) ^ (100 : Nat) := by
          gcongr
    · have hlarge : epsilon ^ (4 : Nat) < delta := lt_of_not_ge hsmall
      have hbound := hlengthLarge length hlengthLarge' digit delta hlarge
      dsimp at hbound
      have hbound := hbound hcutoff
      calc
        _ <= Clarge * ((paddedRestrictedNumbers digit length).card : Real) *
              Real.exp (-(delta ^ (-(2 / 3 : Real)))) /
                Real.log ((10 ^ length : Nat) : Real) +
            Clarge * ((paddedRestrictedNumbers digit length).card : Real) /
              Real.log ((10 ^ length : Nat) : Real) ^ (100 : Nat) := hbound
        _ <= C * ((paddedRestrictedNumbers digit length).card : Real) *
              Real.exp (-(delta ^ (-(2 / 3 : Real)))) /
                Real.log ((10 ^ length : Nat) : Real) +
            C * ((paddedRestrictedNumbers digit length).card : Real) /
              Real.log ((10 ^ length : Nat) : Real) ^ (100 : Nat) := by
          gcongr

end

end PrimesRestrictedDigits
