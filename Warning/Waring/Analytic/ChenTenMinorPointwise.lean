import Waring.Analytic.ChenNine
import Waring.Analytic.ChenSevenUnconditional
import Waring.Analytic.ChenTenMajorArcPointwise
import Waring.Analytic.ChenTenMinorArcApproximation

/-!
# A uniform pointwise estimate on Chen's minor arcs

This packages the Lemma 7/Lemma 9 denominator split used in the final estimate
[CHEN1964-EN, pp. 1567-1568; CHEN1964-ZH, pp. 733-734].
-/

set_option autoImplicit false

namespace Waring.Analytic

open scoped BigOperators

noncomputable section

/-- The corrected Lemma 9 envelope bounds the fifth-power sum throughout
Chen's minor arcs.  Reduced Dirichlet denominators below the cutoff use Lemma
7, while denominators above the cutoff use corrected Lemma 9. -/
theorem norm_fifthPowerExponentialSum_le_of_mem_chenTenMinorArcs
    {P : Nat} (hP : 10 ^ 157 ≤ P) {alpha : Real}
    (halpha : alpha ∈ chenTenMinorArcs P) :
    ‖fifthPowerExponentialSum P alpha‖ ≤
      (2 : Real) ^ (6 / 8 : Real) * (161 : Real) ^ (1 / 16 : Real) *
          (P : Real) ^ (19 / 20 : Real) *
            (Real.log P + 4) ^ (15 / 16 : Real) +
        (P : Real) ^ (24 / 25 : Real) := by
  have hPpos : 0 < P := lt_of_lt_of_le (by norm_num) hP
  have hP150 : 10 ^ 150 ≤ P :=
    (pow_le_pow_right' (by norm_num) (by norm_num : 150 ≤ 157)).trans hP
  have hP150Real : (10 : Real) ^ 150 ≤ P := by
    exact_mod_cast hP150
  obtain ⟨q, a, epsilon, hqPos, _haLt, _haCoprime, haUnit,
    hqLower, hqUpper, halphaEq, hepsilon⟩ :=
    exists_reducedDirichletApproximation_of_mem_chenTenMinorArcs
      hPpos halpha
  letI : NeZero q := ⟨Nat.ne_of_gt hqPos⟩
  by_cases hqCut :
      (q : Real) ≤ (P : Real) ^ (26 / 25 : Real)
  · have hsmallRaw :=
      chen_lemma_seven_unconditional q a epsilon P hP150Real
        hqLower hqCut haUnit hepsilon
    have hsmall :
        ‖fifthPowerExponentialSum P alpha‖ ≤
          (P : Real) ^ (24 / 25 : Real) := by
      rw [halphaEq, fifthPowerExponentialSum_eq_sum_range]
      convert hsmallRaw using 1
      congr 1
      apply Finset.sum_congr rfl
      intro i _hi
      unfold realFifthPowerExponential realFifthPowerPhase
      congr 1
      push_cast
      ring
    have hPone : (1 : Real) ≤ P := by
      exact_mod_cast (show 1 ≤ P by omega)
    have hlogNonneg : 0 ≤ Real.log P + 4 :=
      add_nonneg (Real.log_nonneg hPone) (by norm_num)
    have hfirstNonneg :
        0 ≤ (2 : Real) ^ (6 / 8 : Real) *
          (161 : Real) ^ (1 / 16 : Real) *
            (P : Real) ^ (19 / 20 : Real) *
              (Real.log P + 4) ^ (15 / 16 : Real) := by
      positivity
    exact hsmall.trans (le_add_of_nonneg_left hfirstNonneg)
  · have hqCutLower :
        (P : Real) ^ (26 / 25 : Real) ≤ q :=
      (lt_of_not_ge hqCut).le
    rw [fifthPowerExponentialSum_eq_sum_range]
    exact chen_lemma_nine_corrected a alpha epsilon haUnit halphaEq
      hP150 hqCutLower hqUpper hepsilon

end

end Waring.Analytic
