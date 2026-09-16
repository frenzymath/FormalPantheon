import PrimesRestrictedDigits.SieveAsymptotics.DecimalSievePrimeProduct
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Explicit small-parameter data for the repaired Fundamental Lemma

This records the exact level, cutoff, and coordinate inequalities needed by the weak-to-strict
Rosser adapter.
-/

namespace PrimesRestrictedDigits

noncomputable section

theorem fundamentalSieve_smallParameter_data
    {X epsilon delta : Real} (hX : 1 < X)
    (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hepsilonRosser :
      2 * (Real.exp 5000 + 2) * epsilon ^ (3 : Nat) <= 1)
    (hdelta : 0 < delta)
    (hdeltaEpsilon : delta <= epsilon ^ (4 : Nat))
    (hcutoff : 5 <= X ^ delta) :
    let level := X ^ (epsilon / 2)
    let z := X ^ delta
    let s := epsilon / (2 * delta)
    let alpha := 50 / 77 - epsilon
    2 <= level ∧
      2 <= z ∧
      s = Real.log level / Real.log z ∧
      Real.exp 5000 + 2 <= s ∧
      (∀ p : Nat, p.Prime ->
        p ∣ decimalSievePrimeProduct z -> (p : Real) < level) ∧
      0 <= alpha ∧ alpha <= 1 ∧ delta <= alpha := by
  have hX0 : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hepsilonOne : epsilon <= 1 := by
    exact hepsilonSmall.trans (by norm_num)
  have hepsilonCubeLe : epsilon ^ (3 : Nat) <= (1 / 64 : Real) ^ (3 : Nat) := by
    gcongr
  have hepsilonCubeLtHalf : epsilon ^ (3 : Nat) < (1 / 2 : Real) := by
    exact lt_of_le_of_lt hepsilonCubeLe (by norm_num)
  have hepsilonFourthLtHalf : epsilon ^ (4 : Nat) < epsilon / 2 := by
    calc
      epsilon ^ (4 : Nat) = epsilon * epsilon ^ (3 : Nat) := by ring
      _ < epsilon * (1 / 2 : Real) :=
        mul_lt_mul_of_pos_left hepsilonCubeLtHalf hepsilon
      _ = epsilon / 2 := by ring
  have hdeltaHalf : delta < epsilon / 2 :=
    hdeltaEpsilon.trans_lt hepsilonFourthLtHalf
  have hzlevel : X ^ delta < X ^ (epsilon / 2) :=
    Real.rpow_lt_rpow_of_exponent_lt hX hdeltaHalf
  have hzTwo : 2 <= X ^ delta := by linarith
  have hlevelTwo : 2 <= X ^ (epsilon / 2) := by linarith
  have hcoordinate :
      epsilon / (2 * delta) =
        Real.log (X ^ (epsilon / 2)) / Real.log (X ^ delta) := by
    rw [Real.log_rpow hX0, Real.log_rpow hX0]
    field_simp [hdelta.ne', hlogX.ne']
  have hK : Real.exp 5000 + 2 <= epsilon / (2 * delta) := by
    have hKpos : 0 <= 2 * (Real.exp 5000 + 2) := by positivity
    have hscaledDelta :=
      mul_le_mul_of_nonneg_left hdeltaEpsilon hKpos
    have hmul :
        2 * (Real.exp 5000 + 2) * delta <= epsilon := by
      calc
        2 * (Real.exp 5000 + 2) * delta <=
            2 * (Real.exp 5000 + 2) * epsilon ^ (4 : Nat) :=
          hscaledDelta
        _ = epsilon *
            (2 * (Real.exp 5000 + 2) * epsilon ^ (3 : Nat)) := by ring
        _ <= epsilon * 1 :=
          mul_le_mul_of_nonneg_left hepsilonRosser hepsilon.le
        _ = epsilon := by ring
    apply (le_div_iff₀ (mul_pos (by norm_num) hdelta)).2
    nlinarith
  have hfactor : ∀ p : Nat, p.Prime ->
      p ∣ decimalSievePrimeProduct (X ^ delta) ->
        (p : Real) < X ^ (epsilon / 2) := by
    intro p hp hpd
    have hpMem : p ∈ (decimalSievePrimeProduct (X ^ delta)).primeFactors :=
      (Nat.mem_primeFactors).2
        ⟨hp, hpd, decimalSievePrimeProduct_ne_zero (X ^ delta)⟩
    have hpz := (mem_decimalSievePrimeProductFactors_iff.mp hpMem).2.2
    exact hpz.trans_lt hzlevel
  have hAlpha0 : 0 <= 50 / 77 - epsilon := by
    nlinarith
  have hAlpha1 : 50 / 77 - epsilon <= 1 := by
    nlinarith
  have hdeltaAlpha : delta <= 50 / 77 - epsilon := by
    have hdeltaSmall : delta <= (1 / 64 : Real) ^ (4 : Nat) := by
      calc
        delta <= epsilon ^ (4 : Nat) := hdeltaEpsilon
        _ <= (1 / 64 : Real) ^ (4 : Nat) := by gcongr
    nlinarith
  exact ⟨hlevelTwo, hzTwo, hcoordinate, hK, hfactor,
    hAlpha0, hAlpha1, hdeltaAlpha⟩

theorem fundamentalSieve_roughRatio_pow_le
    {alpha delta : Real} (hdelta : 0 < delta)
    (halpha : 0 <= alpha) (halphaOne : alpha <= 1) :
    (alpha / delta) ^ (16 : Nat) <= delta⁻¹ ^ (16 : Nat) := by
  have hratio : alpha / delta <= delta⁻¹ := by
    rw [← one_div]
    exact (div_le_div_iff_of_pos_right hdelta).2 halphaOne
  have hratioNonneg : 0 <= alpha / delta := div_nonneg halpha hdelta.le
  exact pow_le_pow_left₀ hratioNonneg hratio 16

end

end PrimesRestrictedDigits
