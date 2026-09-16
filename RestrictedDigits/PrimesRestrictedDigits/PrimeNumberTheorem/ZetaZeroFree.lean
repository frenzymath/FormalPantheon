import Mathlib.NumberTheory.LSeries.Nonvanishing
import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaZeroFreeHigh
import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaZeroFreeLow

/-!
# A quantitative zero-free region for the Riemann zeta function

This formalizes `MONTGOMERY-VAUGHAN-MNT-I`, Chapter 6, Theorem 6.6. The
constant is normalized for later use in the logarithmic-derivative estimate.
-/

open Complex

namespace PrimesRestrictedDigits

/-- A normalized absolute constant for the classical zeta zero-free region. -/
def IsRiemannZetaZeroFreeConstant (c : Real) : Prop :=
  0 < c ∧ c ≤ 1 / 9 ∧
    ∀ t sigma : Real,
      1 - c / Real.log (|t| + 4) ≤ sigma →
      riemannZeta
        ((sigma : Complex) + Complex.I * (t : Complex)) ≠ 0

private lemma one_lt_log_abs_add_four (t : Real) :
    1 < Real.log (|t| + 4) := by
  rw [Real.lt_log_iff_exp_lt (by positivity)]
  exact Real.exp_one_lt_three.trans (by linarith [abs_nonneg t])

/-- Shrinking a positive zero-free constant preserves the normalized
zero-free-region predicate. -/
theorem IsRiemannZetaZeroFreeConstant.mono
    {c d : Real} (hc : IsRiemannZetaZeroFreeConstant c)
    (hdPos : 0 < d) (hdc : d ≤ c) :
    IsRiemannZetaZeroFreeConstant d := by
  refine ⟨hdPos, hdc.trans hc.2.1, ?_⟩
  intro t sigma hSigma
  apply hc.2.2 t sigma
  have hLog : 0 < Real.log (|t| + 4) :=
    zero_lt_one.trans (one_lt_log_abs_add_four t)
  have hDiv : d / Real.log (|t| + 4) ≤
      c / Real.log (|t| + 4) := by
    exact div_le_div_of_nonneg_right hdc hLog.le
  linarith

/-- Montgomery--Vaughan, Chapter 6, Theorem 6.6: the Riemann zeta function
has no zero in one absolute logarithmic region to the left of one. -/
theorem exists_isRiemannZetaZeroFreeConstant :
    ∃ c : Real, IsRiemannZetaZeroFreeConstant c := by
  obtain ⟨K, hK, hZeroDistance⟩ :=
    exists_riemannZeta_high_zero_distance
  have hKPos : 0 < K := zero_lt_one.trans_le hK
  let c : Real := min (1 / 18) (1 / (28 * K))
  have hcPos : 0 < c := by
    dsimp [c]
    exact lt_min (by norm_num) (by positivity)
  have hcEighteen : c ≤ 1 / 18 := by
    exact min_le_left _ _
  have hcK : c ≤ 1 / (28 * K) := by
    exact min_le_right _ _
  refine ⟨c, hcPos, hcEighteen.trans (by norm_num), ?_⟩
  intro t sigma hRegion
  have hLog : 1 < Real.log (|t| + 4) :=
    one_lt_log_abs_add_four t
  have hLogPos : 0 < Real.log (|t| + 4) := zero_lt_one.trans hLog
  by_cases hSigma : 1 ≤ sigma
  · apply riemannZeta_ne_zero_of_one_le_re
    simpa using hSigma
  have hSigmaLt : sigma < 1 := lt_of_not_ge hSigma
  have hcDivLt : c / Real.log (|t| + 4) < 1 / 18 :=
    (div_lt_self hcPos hLog).trans_le hcEighteen
  have hSigmaFiveSixths : 5 / 6 ≤ sigma := by
    linarith
  by_cases hT : |t| ≤ 7 / 8
  · apply riemannZeta_ne_zero_of_low_rectangle
    · linarith
    · exact hSigmaLt.le
    · exact hT
  · have hTHigh : 7 / 8 ≤ |t| := by
      exact (lt_of_not_ge hT).le
    intro hZero
    have hDistance := hZeroDistance t sigma hTHigh hSigmaFiveSixths hZero
    have hRegionUpper :
        1 - sigma ≤ c / Real.log (|t| + 4) := by
      linarith
    have hcDiv :
        c / Real.log (|t| + 4) ≤
          1 / (28 * K * Real.log (|t| + 4)) := by
      calc
        c / Real.log (|t| + 4) ≤
            (1 / (28 * K)) / Real.log (|t| + 4) :=
          div_le_div_of_nonneg_right hcK hLogPos.le
        _ = 1 / (28 * K * Real.log (|t| + 4)) := by
          field_simp
    have hDenomPos :
        0 < 14 * K * Real.log (|t| + 4) := by positivity
    have hDenomLt :
        14 * K * Real.log (|t| + 4) <
          28 * K * Real.log (|t| + 4) := by
      nlinarith [mul_pos hKPos hLogPos]
    have hReciprocal :
        1 / (28 * K * Real.log (|t| + 4)) <
          1 / (14 * K * Real.log (|t| + 4)) :=
      one_div_lt_one_div_of_lt hDenomPos hDenomLt
    linarith

end PrimesRestrictedDigits
