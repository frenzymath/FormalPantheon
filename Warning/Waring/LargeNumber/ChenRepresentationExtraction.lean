import Waring.Basic
import Waring.LargeNumber.ChenCircleMethod

/-!
# Positivity and representation extraction from Chen's convolution

This formalizes the last positivity argument following English equation (44)
and Chinese equation (34) [CHEN1964-EN, p. 1568; CHEN1964-ZH, p. 734].
-/

set_option autoImplicit false

namespace Waring.LargeNumber

open Waring.Statement
open scoped BigOperators

noncomputable section

/-- A minor convolution smaller than the strict major lower bound makes the
complete convolved representation count positive. -/
theorem chenRepresentationConvolution_re_pos_of_minor_lt
    {N : Nat} (hN : 10 ^ 785 ≤ N)
    (hminor :
      ‖chenMinorConvolution N‖ <
        (1 / 2000 : Real) * (mainScale N : Real) ^ 10 *
          ((chenElevenSums N).card : Real) ^ 2) :
    0 < (chenRepresentationConvolution N).re := by
  have hp157 := ten_pow_oneFiftySeven_le_mainScale hN
  have hp : 0 < mainScale N := lt_of_lt_of_le (by norm_num) hp157
  have hsplit := chenRepresentationConvolution_eq_major_add_minor
    (N := N) hp
  have hmajor := chenMajorConvolution_re_lower hN
  have hminorRe :
      -‖chenMinorConvolution N‖ ≤ (chenMinorConvolution N).re := by
    have habs := Complex.abs_re_le_norm (chenMinorConvolution N)
    exact (abs_le.mp habs).1
  rw [hsplit, Complex.add_re]
  linarith

/-- Positive real part of the convolved count yields a pair of family shifts
with a positive bounded fifteen-variable representation count. -/
theorem exists_positiveRepresentationCount_of_convolution_re_pos
    {N : Nat} (hpos : 0 < (chenRepresentationConvolution N).re) :
    ∃ u ∈ chenElevenSums N, ∃ v ∈ chenElevenSums N,
      0 < Analytic.positiveFifthPowerRepresentationCount
        15 (mainScale N) (N - u - v) := by
  have hsum :
      0 < ∑ u ∈ chenElevenSums N, ∑ v ∈ chenElevenSums N,
        Analytic.positiveFifthPowerRepresentationCount
          15 (mainScale N) (N - u - v) := by
    have hsumReal :
        (0 : Real) <
          ((∑ u ∈ chenElevenSums N, ∑ v ∈ chenElevenSums N,
            Analytic.positiveFifthPowerRepresentationCount
              15 (mainScale N) (N - u - v) : Nat) : Real) := by
      simpa [chenRepresentationConvolution] using hpos
    exact_mod_cast hsumReal
  obtain ⟨u, hu, huPos⟩ := Finset.sum_pos_iff.mp hsum
  obtain ⟨v, hv, hvPos⟩ := Finset.sum_pos_iff.mp huPos
  exact ⟨u, hu, v, hv, hvPos⟩

/-- A positive term in Chen's convolution unpacks to a 37-slot fifth-power
representation of the original target. -/
theorem hasPowerSumRepresentation_thirtySeven_of_convolution_re_pos
    {N : Nat} (hN : 10 ^ 785 ≤ N)
    (hpos : 0 < (chenRepresentationConvolution N).re) :
    HasPowerSumRepresentation 5 37 N := by
  obtain ⟨u, hu, v, hv, hcount⟩ :=
    exists_positiveRepresentationCount_of_convolution_re_pos hpos
  obtain ⟨x, hx⟩ :=
    (Analytic.positiveFifthPowerRepresentationCount_pos_iff
      15 (mainScale N) (N - u - v)).mp hcount
  have hresidual :
      HasPowerSumRepresentation 5 15 (N - u - v) := by
    refine ⟨fun i => (x i).val.succ, ?_⟩
    simpa [Analytic.positiveFifthPowerTupleSum] using hx.symm
  obtain ⟨xu, hxu⟩ := mem_chenElevenSums_has_fifthPowers hu
  obtain ⟨xv, hxv⟩ := mem_chenElevenSums_has_fifthPowers hv
  have huRepresentation : HasPowerSumRepresentation 5 11 u :=
    ⟨xu, hxu⟩
  have hvRepresentation : HasPowerSumRepresentation 5 11 v :=
    ⟨xv, hxv⟩
  have hcombined :=
    Waring.HasPowerSumRepresentation.add
      (Waring.HasPowerSumRepresentation.add hresidual huRepresentation)
      hvRepresentation
  have hN780 : 10 ^ 780 ≤ N :=
    (pow_le_pow_right' (by norm_num) (by norm_num : 780 ≤ 785)).trans hN
  have huBound := mem_chenElevenSums_le_quarter hN780 hu
  have hvBound := mem_chenElevenSums_le_quarter hN780 hv
  have hsum : N - u - v + u + v = N := by omega
  simpa [hsum] using hcombined

/-- Chen's large-number theorem reduced to the single strict minor-arc
convolution estimate. -/
theorem chen_large_number_representation_of_minor_bound
    {N : Nat} (hN : 10 ^ 785 ≤ N)
    (hminor :
      ‖chenMinorConvolution N‖ <
        (1 / 2000 : Real) * (mainScale N : Real) ^ 10 *
          ((chenElevenSums N).card : Real) ^ 2) :
    HasPowerSumRepresentation 5 37 N := by
  apply hasPowerSumRepresentation_thirtySeven_of_convolution_re_pos hN
  exact chenRepresentationConvolution_re_pos_of_minor_lt hN hminor

end

end Waring.LargeNumber
