import Waring.Analytic.ChenTen
import Waring.LargeNumber.ChenEleven
import Waring.LargeNumber.MainScaleBounds

/-!
# Chen's major/minor contributions at the main scale

These are the convolution quantities in the final proof
[CHEN1964-EN, pp. 1567-1568, equations (42)-(44); CHEN1964-ZH,
pp. 733-734, equations (32)-(34)].
-/

set_option autoImplicit false

namespace Waring.LargeNumber

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- The sum of the reduced major-arc integrals for a bounded target. -/
def chenMajorContribution (P n : Nat) : Complex :=
  ∑ i : Analytic.ChenTenArcIndex P,
    ∫ alpha in Analytic.chenTenArc P i,
      Analytic.chenTenRepresentationIntegrand P n alpha

/-- The complementary minor-arc integral for a bounded target. -/
def chenMinorContribution (P n : Nat) : Complex :=
  ∫ alpha in Analytic.chenTenMinorArcs P,
    Analytic.chenTenRepresentationIntegrand P n alpha

/-- The exact major/minor decomposition in named downstream notation. -/
theorem positiveFifthPowerRepresentationCount_eq_major_add_minor
    (P n : Nat) (hP : 0 < P) :
    (Analytic.positiveFifthPowerRepresentationCount 15 P n : Complex) =
      chenMajorContribution P n + chenMinorContribution P n := by
  simpa [chenMajorContribution, chenMinorContribution] using
    Analytic.positiveFifthPowerRepresentationCount_eq_majorArc_sum_add_minor
      P n hP

/-- The double major-arc convolution over Chen's eleven-power family. -/
def chenMajorConvolution (N : Nat) : Complex :=
  ∑ u ∈ chenElevenSums N, ∑ v ∈ chenElevenSums N,
    chenMajorContribution (mainScale N) (N - u - v)

/-- The corresponding double minor-arc convolution. -/
def chenMinorConvolution (N : Nat) : Complex :=
  ∑ u ∈ chenElevenSums N, ∑ v ∈ chenElevenSums N,
    chenMinorContribution (mainScale N) (N - u - v)

/-- The convolved bounded representation count. -/
def chenRepresentationConvolution (N : Nat) : Complex :=
  ∑ u ∈ chenElevenSums N, ∑ v ∈ chenElevenSums N,
    (Analytic.positiveFifthPowerRepresentationCount 15 (mainScale N)
      (N - u - v) : Complex)

/-- Summing the exact individual decompositions gives the convolution split. -/
theorem chenRepresentationConvolution_eq_major_add_minor
    {N : Nat} (hP : 0 < mainScale N) :
    chenRepresentationConvolution N =
      chenMajorConvolution N + chenMinorConvolution N := by
  unfold chenRepresentationConvolution chenMajorConvolution
    chenMinorConvolution
  simp_rw [positiveFifthPowerRepresentationCount_eq_major_add_minor
    (mainScale N) _ hP]
  simp only [Finset.sum_add_distrib]

/-- At the final threshold, Chen's eleven-power family is nonempty. -/
theorem chenElevenSums_nonempty
    {N : Nat} (hN : 10 ^ 785 ≤ N) :
    (chenElevenSums N).Nonempty := by
  have hN780 : 10 ^ 780 ≤ N :=
    (pow_le_pow_right' (by norm_num) (by norm_num : 780 ≤ 785)).trans hN
  have hcard := (chen_lemma_eleven hN780).2
  have hp157 := ten_pow_oneFiftySeven_le_mainScale hN
  have hp : 0 < mainScale N := lt_of_lt_of_le (by norm_num) hp157
  have hlowerPos :
      0 < (17 / 10 : Real) / 2 ^ 17 *
        (mainScale N : Real) ^ (5 - 5 * scaleRatio ^ 11) := by
    positivity
  have hcardPosReal : (0 : Real) < (chenElevenSums N).card :=
    hlowerPos.trans_le hcard
  have hcardPos : 0 < (chenElevenSums N).card := by
    exact_mod_cast hcardPosReal
  exact Finset.card_pos.mp hcardPos

/-- Every summand in the major convolution has the strict Lemma 10 lower
bound. -/
theorem one_2000_mul_mainScale_pow_ten_lt_chenMajorContribution
    {N u v : Nat} (hN : 10 ^ 785 ≤ N)
    (hu : u ∈ chenElevenSums N) (hv : v ∈ chenElevenSums N) :
    (1 / 2000 : Real) * (mainScale N : Real) ^ 10 <
      (chenMajorContribution (mainScale N) (N - u - v)).re := by
  have hN780 : 10 ^ 780 ≤ N :=
    (pow_le_pow_right' (by norm_num) (by norm_num : 780 ≤ 785)).trans hN
  have huBound := mem_chenElevenSums_le_quarter hN780 hu
  have hvBound := mem_chenElevenSums_le_quarter hN780 hv
  have hp157 := ten_pow_oneFiftySeven_le_mainScale hN
  have hp100 : 10 ^ 100 ≤ mainScale N :=
    (by norm_num : 10 ^ 100 ≤ 10 ^ 157).trans hp157
  simpa [chenMajorContribution] using
    Analytic.one_2000_mul_P_pow_ten_lt_chenTenMajorArc_re_source
      hp100
      (mainScale_fifth_half_le_sub_sub huBound hvBound)
      (sub_sub_le_mainScale_add_one_pow_five N u v)

/-- The complete major convolution retains the same strict lower bound times
the square of the family cardinality. -/
theorem chenMajorConvolution_re_lower
    {N : Nat} (hN : 10 ^ 785 ≤ N) :
    (1 / 2000 : Real) * (mainScale N : Real) ^ 10 *
        ((chenElevenSums N).card : Real) ^ 2 <
      (chenMajorConvolution N).re := by
  let U := chenElevenSums N
  let c : Real := (1 / 2000 : Real) * (mainScale N : Real) ^ 10
  have hU : U.Nonempty := by
    simpa [U] using chenElevenSums_nonempty hN
  have hdouble :
      (∑ u ∈ U, ∑ _v ∈ U, c) <
        ∑ u ∈ U, ∑ v ∈ U,
          (chenMajorContribution (mainScale N) (N - u - v)).re := by
    apply Finset.sum_lt_sum_of_nonempty hU
    intro u hu
    apply Finset.sum_lt_sum_of_nonempty hU
    intro v hv
    exact one_2000_mul_mainScale_pow_ten_lt_chenMajorContribution hN
      (by simpa [U] using hu) (by simpa [U] using hv)
  calc
    (1 / 2000 : Real) * (mainScale N : Real) ^ 10 *
          ((chenElevenSums N).card : Real) ^ 2 =
        ∑ u ∈ U, ∑ _v ∈ U, c := by
      simp [U, c]
      ring
    _ < ∑ u ∈ U, ∑ v ∈ U,
        (chenMajorContribution (mainScale N) (N - u - v)).re := hdouble
    _ = (chenMajorConvolution N).re := by
      simp [chenMajorConvolution, U]

end

end Waring.LargeNumber
