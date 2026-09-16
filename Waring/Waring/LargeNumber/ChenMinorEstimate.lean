import Waring.LargeNumber.ChenMinorEnvelopeBounds
import Waring.LargeNumber.ChenPhaseParseval
import Waring.LargeNumber.ChenMinorCardinality
import Waring.LargeNumber.MainScaleBounds

/-!
# The final minor-convolution estimate

This is the corrected form of the terminal estimate in English equation (44)
and Chinese equation (34) [CHEN1964-EN, p. 1568; CHEN1964-ZH, p. 734; D-016].
-/

set_option autoImplicit false

namespace Waring.LargeNumber

open MeasureTheory
open scoped BigOperators

noncomputable section

private theorem continuous_chenElevenPhaseSum (N : Nat) :
    Continuous (chenElevenPhaseSum N) := by
  unfold chenElevenPhaseSum
  apply continuous_finsetSum
  intro u hu
  fun_prop

/-- The analytic and cardinality estimates reduce the final minor-convolution
bound to the numerical absorption of the corrected fifteenth-power envelope. -/
theorem norm_chenMinorConvolution_lt_of_envelope_scaled_lt
    {N : Nat} (hN : 10 ^ 785 <= N)
    (hscaled :
      chenMinorFifteenthEnvelope (mainScale N) * 80000 *
          (mainScale N : Real) ^
            (-(5 - 5 * scaleRatio ^ 11)) <
        (1 / 2000 : Real) * (mainScale N : Real) ^ 10) :
    ‖chenMinorConvolution N‖ <
      (1 / 2000 : Real) * (mainScale N : Real) ^ 10 *
        ((chenElevenSums N).card : Real) ^ 2 := by
  let P : Nat := mainScale N
  let U : Real := (chenElevenSums N).card
  let F : Real := chenMinorFifteenthEnvelope P
  let E : Real := 5 - 5 * scaleRatio ^ 11
  have hP157 : 10 ^ 157 <= P := by
    simpa [P] using ten_pow_oneFiftySeven_le_mainScale hN
  have hN780 : 10 ^ 780 <= N :=
    (pow_le_pow_right' (by norm_num) (by norm_num : 780 <= 785)).trans hN
  have hphaseIntegrable :
      IntegrableOn (fun alpha : Real => ‖chenElevenPhaseSum N alpha‖ ^ 2)
        (Analytic.chenTenMinorArcs P) := by
    apply
      ((continuous_chenElevenPhaseSum N).norm.fun_pow 2).integrableOn_Icc.mono_set
    exact Set.sdiff_subset.trans (by
      unfold Analytic.chenTenArcFundamentalInterval
      exact Set.Ico_subset_Icc_self)
  have hweightedIntegrable :
      IntegrableOn
        (fun alpha : Real => F * ‖chenElevenPhaseSum N alpha‖ ^ 2)
        (Analytic.chenTenMinorArcs P) :=
    hphaseIntegrable.const_mul F
  have hintegralEnvelope :
      ‖∫ alpha in Analytic.chenTenMinorArcs P,
          Analytic.chenTenRepresentationIntegrand P N alpha *
            chenElevenPhaseSum N alpha ^ 2‖ <=
        F *
          ∫ alpha in Analytic.chenTenMinorArcs P,
            ‖chenElevenPhaseSum N alpha‖ ^ 2 := by
    calc
      ‖∫ alpha in Analytic.chenTenMinorArcs P,
          Analytic.chenTenRepresentationIntegrand P N alpha *
            chenElevenPhaseSum N alpha ^ 2‖ <=
          ∫ alpha in Analytic.chenTenMinorArcs P,
            ‖Analytic.chenTenRepresentationIntegrand P N alpha *
              chenElevenPhaseSum N alpha ^ 2‖ :=
        norm_integral_le_integral_norm _
      _ <= ∫ alpha in Analytic.chenTenMinorArcs P,
          F * ‖chenElevenPhaseSum N alpha‖ ^ 2 := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall fun alpha => norm_nonneg _
        · exact hweightedIntegrable
        · filter_upwards
            [ae_restrict_mem (Analytic.measurableSet_chenTenMinorArcs P)]
            with alpha halpha
          rw [norm_mul, norm_pow]
          exact mul_le_mul_of_nonneg_right
            (by
              simpa [F, P] using
                norm_chenTenRepresentationIntegrand_le_minorEnvelope
                  hP157 N halpha)
            (sq_nonneg _)
      _ = F *
          ∫ alpha in Analytic.chenTenMinorArcs P,
            ‖chenElevenPhaseSum N alpha‖ ^ 2 := by
        rw [integral_const_mul]
  have hparseval :
      (∫ alpha in Analytic.chenTenMinorArcs P,
          ‖chenElevenPhaseSum N alpha‖ ^ 2) <= U := by
    simpa [U] using setIntegral_norm_chenElevenPhaseSum_sq_le_card P N
  have hcardinality :
      U <= 80000 * (P : Real) ^ (-E) * U ^ 2 := by
    simpa [P, U, E] using chenElevenSums_card_le_scaled_square hN780
  have hUpos : 0 < U := by
    have hcardPos := Finset.card_pos.mpr (chenElevenSums_nonempty hN)
    have hcardPosReal :
        (0 : Real) < ((chenElevenSums N).card : Real) := by
      exact_mod_cast hcardPos
    simpa [U] using hcardPosReal
  calc
    ‖chenMinorConvolution N‖ =
        ‖∫ alpha in Analytic.chenTenMinorArcs P,
          Analytic.chenTenRepresentationIntegrand P N alpha *
            chenElevenPhaseSum N alpha ^ 2‖ := by
      rw [chenMinorConvolution_eq_integral hN]
    _ <= F *
        ∫ alpha in Analytic.chenTenMinorArcs P,
          ‖chenElevenPhaseSum N alpha‖ ^ 2 := hintegralEnvelope
    _ <= F * U :=
      mul_le_mul_of_nonneg_left hparseval
        (chenMinorFifteenthEnvelope_nonneg P)
    _ <= (F * 80000 * (P : Real) ^ (-E)) * U ^ 2 := by
      calc
        F * U <= F * (80000 * (P : Real) ^ (-E) * U ^ 2) :=
          mul_le_mul_of_nonneg_left hcardinality
            (chenMinorFifteenthEnvelope_nonneg P)
        _ = (F * 80000 * (P : Real) ^ (-E)) * U ^ 2 := by ring
    _ < ((1 / 2000 : Real) * (P : Real) ^ 10) * U ^ 2 := by
      apply mul_lt_mul_of_pos_right
      · simpa [F, P, E] using hscaled
      · positivity
    _ = (1 / 2000 : Real) * (mainScale N : Real) ^ 10 *
        ((chenElevenSums N).card : Real) ^ 2 := by
      simp [P, U]

/-- The final minor convolution is strictly smaller than the common major
lower-bound scale. -/
theorem norm_chenMinorConvolution_lt
    {N : Nat} (hN : 10 ^ 785 <= N) :
    ‖chenMinorConvolution N‖ <
      (1 / 2000 : Real) * (mainScale N : Real) ^ 10 *
        ((chenElevenSums N).card : Real) ^ 2 := by
  apply norm_chenMinorConvolution_lt_of_envelope_scaled_lt hN
  exact chenMinorFifteenthEnvelope_scaled_lt
    (ten_pow_oneFiftySeven_le_mainScale hN)

end

end Waring.LargeNumber
