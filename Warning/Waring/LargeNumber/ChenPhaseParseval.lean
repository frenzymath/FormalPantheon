import Waring.LargeNumber.ChenMinorConvolution

/-!
# Parseval for Chen's eleven-sum phase polynomial

This supplies the Parseval step used between English equations (42)-(44) and
Chinese equations (32)-(34) [CHEN1964-EN, p. 1568; CHEN1964-ZH, p. 734].
-/

set_option autoImplicit false

namespace Waring.LargeNumber

open MeasureTheory
open scoped BigOperators Interval

noncomputable section

private def natPhaseSum (U : Finset Nat) (alpha : Real) : Complex :=
  ∑ u ∈ U,
    Complex.exp
      (2 * Real.pi * Complex.I * (alpha * (u : Real)))

private theorem conj_natPhase_mul_natPhase
    (u v : Nat) (alpha : Real) :
    (starRingEnd Complex)
        (Complex.exp
          (2 * Real.pi * Complex.I * (alpha * (u : Real)))) *
      Complex.exp
        (2 * Real.pi * Complex.I * (alpha * (v : Real))) =
      Complex.exp
        (2 * Real.pi * Complex.I *
          (((((v : Nat) : Int) - (u : Nat) : Int) : Real) * alpha)) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  push_cast
  simp
  rw [map_ofNat]
  ring

private theorem natPhaseSum_norm_sq_expansion
    (U : Finset Nat) (alpha : Real) :
    ((‖natPhaseSum U alpha‖ ^ 2 : Real) : Complex) =
      ∑ u ∈ U, ∑ v ∈ U,
        Complex.exp
          (2 * Real.pi * Complex.I *
            (((((v : Nat) : Int) - (u : Nat) : Int) : Real) * alpha)) := by
  rw [show ((‖natPhaseSum U alpha‖ ^ 2 : Real) : Complex) =
      (‖natPhaseSum U alpha‖ : Complex) ^ 2 by push_cast; rfl]
  rw [← Complex.conj_mul']
  unfold natPhaseSum
  simp only [map_sum, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  exact conj_natPhase_mul_natPhase u v alpha

private theorem continuous_natPhaseSum (U : Finset Nat) :
    Continuous (natPhaseSum U) := by
  unfold natPhaseSum
  apply continuous_finsetSum
  intro u hu
  fun_prop

private theorem intervalIntegral_norm_natPhaseSum_sq_eq_card
    (U : Finset Nat) (c : Real) :
    (∫ alpha in c..c + 1, ‖natPhaseSum U alpha‖ ^ 2) =
      (U.card : Real) := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [natPhaseSum_norm_sq_expansion]
  rw [intervalIntegral.integral_finsetSum]
  · rw [show (((U.card : Nat) : Real) : Complex) =
        ∑ _u ∈ U, (1 : Complex) by simp]
    apply Finset.sum_congr rfl
    intro u hu
    rw [intervalIntegral.integral_finsetSum]
    · simp_rw [Analytic.intervalIntegral_exp_int_frequency]
      simp [sub_eq_zero, hu]
    · intro v hv
      apply Continuous.intervalIntegrable
      fun_prop
  · intro u hu
    apply Continuous.intervalIntegrable
    apply continuous_finsetSum
    intro v hv
    fun_prop

/-- Parseval's identity for Chen's finite family of eleven-power sums, on
every interval of length one. -/
theorem intervalIntegral_norm_chenElevenPhaseSum_sq_eq_card
    (N : Nat) (c : Real) :
    (∫ alpha in c..c + 1, ‖chenElevenPhaseSum N alpha‖ ^ 2) =
      ((chenElevenSums N).card : Real) := by
  simpa only [natPhaseSum, chenElevenPhaseSum] using
    intervalIntegral_norm_natPhaseSum_sq_eq_card (chenElevenSums N) c

/-- Parseval's identity on Chen's translated fundamental interval. -/
theorem setIntegral_norm_chenElevenPhaseSum_sq_eq_card
    (P N : Nat) :
    (∫ alpha in Analytic.chenTenArcFundamentalInterval P,
        ‖chenElevenPhaseSum N alpha‖ ^ 2) =
      ((chenElevenSums N).card : Real) := by
  rw [← Analytic.intervalIntegral_eq_setIntegral_chenTenArcFundamentalInterval]
  have hright : Analytic.chenTenArcRightEndpoint P =
      Analytic.chenTenArcLeftEndpoint P + 1 := by
    linarith [Analytic.chenTenArcFundamentalInterval_length P]
  rw [hright]
  exact intervalIntegral_norm_chenElevenPhaseSum_sq_eq_card
    N (Analytic.chenTenArcLeftEndpoint P)

/-- The phase polynomial has at most its Parseval mass on Chen's minor arcs. -/
theorem setIntegral_norm_chenElevenPhaseSum_sq_le_card
    (P N : Nat) :
    (∫ alpha in Analytic.chenTenMinorArcs P,
        ‖chenElevenPhaseSum N alpha‖ ^ 2) ≤
      ((chenElevenSums N).card : Real) := by
  rw [← setIntegral_norm_chenElevenPhaseSum_sq_eq_card P N]
  apply setIntegral_mono_set
  · apply
      ((continuous_natPhaseSum (chenElevenSums N)).norm.fun_pow 2).integrableOn_Icc.mono_set
    unfold Analytic.chenTenArcFundamentalInterval
    exact Set.Ico_subset_Icc_self
  · exact Filter.Eventually.of_forall fun alpha => sq_nonneg _
  · exact Filter.Eventually.of_forall Set.sdiff_subset

end

end Waring.LargeNumber
