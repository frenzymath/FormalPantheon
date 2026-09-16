import PrimesRestrictedDigits.BasicEstimates.BuchstabMiddleEnvelope
import PrimesRestrictedDigits.BasicEstimates.UniformRealGrid
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# eight-cell Buchstab middle envelope

The exact middle formula and rational logarithm certificates give a separate upper bound on
each cell of the uniform eight-cell partition of `[2, 3]`.
-/

set_option autoImplicit false
set_option warningAsError true

open Set

namespace PrimesRestrictedDigits

noncomputable section

def sectionSixBuchstabMiddleEightCellCap (i : Fin 8) : Real :=
  ![1315039 / 2500000,
    2718097 / 5000000,
    1110277 / 2000000,
    5621861 / 10000000,
    2829539 / 5000000,
    5671331 / 10000000,
    70893 / 125000,
    2832363 / 5000000] i

private def sectionSixBuchstabMiddleProfile (t : Real) : Real :=
  (1 + Real.log (t - 1)) / t

private theorem sectionSixBuchstabMiddleProfile_hasDerivAt
    {t : Real} (ht : 1 < t) :
    HasDerivAt sectionSixBuchstabMiddleProfile
      ((1 / (t - 1) - Real.log (t - 1)) / t ^ 2) t := by
  have htPos : 0 < t := by linarith
  have htSubPos : 0 < t - 1 := by linarith
  have hlog := ((hasDerivAt_id t).sub_const 1).log htSubPos.ne'
  have hquot := (hlog.const_add 1).fun_div (hasDerivAt_id t) htPos.ne'
  have hquot' : HasDerivAt
      (fun y : Real => (1 + Real.log (y - 1)) / y)
      ((1 / (t - 1) * t - (1 + Real.log (t - 1))) / t ^ 2) t := by
    simpa only [id_eq, mul_one] using hquot
  unfold sectionSixBuchstabMiddleProfile
  apply hquot'.congr_deriv
  field_simp
  ring

private theorem sectionSixBuchstabMiddle_log_sevenFour_lt :
    Real.log (7 / 4 : Real) < 4 / 7 := by
  have hlog := log_cayley_le_cayleyLogSeriesUpper
    (x := (3 / 11 : Real)) (by norm_num) (by norm_num) 8
  have hratio :
      (1 + (3 / 11 : Real)) / (1 - 3 / 11) = 7 / 4 := by
    norm_num
  rw [hratio] at hlog
  norm_num [cayleyLogSeriesUpper, Finset.sum_range_succ] at hlog ⊢
  linarith

private theorem sectionSixBuchstabMiddleProfile_deriv_nonneg
    {t : Real} (htTwo : 2 < t) (htUpper : t < 11 / 4) :
    0 <= (1 / (t - 1) - Real.log (t - 1)) / t ^ 2 := by
  have hxPos : 0 < t - 1 := by linarith
  have hxUpper : t - 1 <= 7 / 4 := by linarith
  have hlogMono : Real.log (t - 1) <= Real.log (7 / 4 : Real) :=
    Real.log_le_log hxPos hxUpper
  have hinv : (4 / 7 : Real) <= 1 / (t - 1) := by
    rw [le_div_iff₀ hxPos]
    nlinarith
  have hlog := sectionSixBuchstabMiddle_log_sevenFour_lt
  have hnum : 0 <= 1 / (t - 1) - Real.log (t - 1) := by
    linarith
  exact div_nonneg hnum (sq_nonneg t)

private theorem sectionSixBuchstabMiddleProfile_monotoneOn :
    MonotoneOn sectionSixBuchstabMiddleProfile (Icc 2 (11 / 4)) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
  · intro t ht
    exact (sectionSixBuchstabMiddleProfile_hasDerivAt
      (by linarith [ht.1])).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    exact (sectionSixBuchstabMiddleProfile_hasDerivAt
      (by linarith [ht.1])).hasDerivWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    exact sectionSixBuchstabMiddleProfile_deriv_nonneg ht.1 ht.2

private theorem sectionSixBuchstabMiddle_eightFifteen_lt_log :
    (8 / 15 : Real) < Real.log (15 / 8) := by
  have hlog := Real.sum_range_le_log_div
    (x := (7 / 23 : Real)) (by norm_num) (by norm_num) 8
  have hratio :
      (1 + (7 / 23 : Real)) / (1 - 7 / 23) = 15 / 8 := by
    norm_num
  rw [hratio] at hlog
  norm_num [Finset.sum_range_succ] at hlog ⊢
  linarith

private theorem sectionSixBuchstabMiddleProfile_deriv_nonpos
    {t : Real} (htLower : 23 / 8 < t) (htThree : t < 3) :
    (1 / (t - 1) - Real.log (t - 1)) / t ^ 2 <= 0 := by
  have hxPos : 0 < t - 1 := by linarith
  have hxLower : (15 / 8 : Real) <= t - 1 := by linarith
  have hlogMono : Real.log (15 / 8 : Real) <= Real.log (t - 1) :=
    Real.log_le_log (by norm_num) hxLower
  have hinv : 1 / (t - 1) <= (8 / 15 : Real) := by
    simpa using (one_div_le_one_div_of_le
      (by norm_num : (0 : Real) < 15 / 8) hxLower)
  have hlog := sectionSixBuchstabMiddle_eightFifteen_lt_log
  have hnum : 1 / (t - 1) - Real.log (t - 1) <= 0 := by
    linarith
  exact div_nonpos_of_nonpos_of_nonneg hnum (sq_nonneg t)

private theorem sectionSixBuchstabMiddleProfile_antitoneOn :
    AntitoneOn sectionSixBuchstabMiddleProfile (Icc (23 / 8) 3) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
  · intro t ht
    exact (sectionSixBuchstabMiddleProfile_hasDerivAt
      (by linarith [ht.1])).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    exact (sectionSixBuchstabMiddleProfile_hasDerivAt
      (by linarith [ht.1])).hasDerivWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    exact sectionSixBuchstabMiddleProfile_deriv_nonpos ht.1 ht.2

private theorem sectionSixBuchstabMiddleProfile_le_of_cayley
    {t x C : Real} (ht : 0 < t) (hxNonneg : 0 <= x) (hxOne : x < 1)
    (hratio : (1 + x) / (1 - x) = t - 1)
    (hcap : (1 + cayleyLogSeriesUpper x 8) / t <= C) :
    sectionSixBuchstabMiddleProfile t <= C := by
  have hlog := log_cayley_le_cayleyLogSeriesUpper hxNonneg hxOne 8
  rw [hratio] at hlog
  unfold sectionSixBuchstabMiddleProfile
  have hmid :
      (1 + Real.log (t - 1)) / t <=
        (1 + cayleyLogSeriesUpper x 8) / t := by
    simpa only [add_comm] using
      (div_le_div_of_nonneg_right (add_le_add_left hlog 1) ht.le)
  exact hmid.trans hcap

private theorem sectionSixBuchstabMiddleProfile_seventeenEight_le :
    sectionSixBuchstabMiddleProfile (17 / 8) <= 1315039 / 2500000 := by
  apply sectionSixBuchstabMiddleProfile_le_of_cayley
      (x := (1 / 17 : Real))
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num [cayleyLogSeriesUpper, Finset.sum_range_succ]

private theorem sectionSixBuchstabMiddleProfile_nineFour_le :
    sectionSixBuchstabMiddleProfile (9 / 4) <= 2718097 / 5000000 := by
  apply sectionSixBuchstabMiddleProfile_le_of_cayley
      (x := (1 / 9 : Real))
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num [cayleyLogSeriesUpper, Finset.sum_range_succ]

private theorem sectionSixBuchstabMiddleProfile_nineteenEight_le :
    sectionSixBuchstabMiddleProfile (19 / 8) <= 1110277 / 2000000 := by
  apply sectionSixBuchstabMiddleProfile_le_of_cayley
      (x := (3 / 19 : Real))
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num [cayleyLogSeriesUpper, Finset.sum_range_succ]

private theorem sectionSixBuchstabMiddleProfile_fiveTwo_le :
    sectionSixBuchstabMiddleProfile (5 / 2) <= 5621861 / 10000000 := by
  apply sectionSixBuchstabMiddleProfile_le_of_cayley
      (x := (1 / 5 : Real))
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num [cayleyLogSeriesUpper, Finset.sum_range_succ]

private theorem sectionSixBuchstabMiddleProfile_twentyOneEight_le :
    sectionSixBuchstabMiddleProfile (21 / 8) <= 2829539 / 5000000 := by
  apply sectionSixBuchstabMiddleProfile_le_of_cayley
      (x := (5 / 21 : Real))
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num [cayleyLogSeriesUpper, Finset.sum_range_succ]

private theorem sectionSixBuchstabMiddleProfile_elevenFour_le :
    sectionSixBuchstabMiddleProfile (11 / 4) <= 5671331 / 10000000 := by
  apply sectionSixBuchstabMiddleProfile_le_of_cayley
      (x := (3 / 11 : Real))
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num [cayleyLogSeriesUpper, Finset.sum_range_succ]

private theorem sectionSixBuchstabMiddleProfile_twentyThreeEight_le :
    sectionSixBuchstabMiddleProfile (23 / 8) <= 2832363 / 5000000 := by
  apply sectionSixBuchstabMiddleProfile_le_of_cayley
      (x := (7 / 23 : Real))
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num [cayleyLogSeriesUpper, Finset.sum_range_succ]

private theorem buchstabFunction_le_middleIncreasingEndpoint
    {u e C : Real} (huTwo : 2 <= u) (hue : u <= e)
    (heUpper : e <= 11 / 4)
    (hend : sectionSixBuchstabMiddleProfile e <= C) :
    buchstabFunction u <= C := by
  have huThree : u <= 3 := by linarith
  rw [buchstabFunction_eq_one_add_log_sub_one_div huTwo huThree]
  change sectionSixBuchstabMiddleProfile u <= C
  exact (sectionSixBuchstabMiddleProfile_monotoneOn
    ⟨huTwo, hue.trans heUpper⟩ ⟨huTwo.trans hue, heUpper⟩ hue).trans hend

theorem buchstabFunction_le_middleEightCellEnvelope
    (i : Fin 8) {u : Real}
    (hlo : uniformRealGridLower (2 : Real) 3 i <= u)
    (hhi : u <= uniformRealGridUpper (2 : Real) 3 i) :
    buchstabFunction u <= sectionSixBuchstabMiddleEightCellCap i := by
  have hb := uniformRealGrid_bounds (n := 8) (by norm_num)
    (by norm_num : (2 : Real) <= 3) i
  have huTwo : (2 : Real) <= u := hb.1.trans hlo
  have huThree : u <= (3 : Real) := hhi.trans hb.2.2
  fin_cases i <;>
    norm_num [uniformRealGridLower, uniformRealGridUpper,
      sectionSixBuchstabMiddleEightCellCap] at hlo hhi ⊢
  · exact buchstabFunction_le_middleIncreasingEndpoint huTwo hhi
      (by norm_num) sectionSixBuchstabMiddleProfile_seventeenEight_le
  · exact buchstabFunction_le_middleIncreasingEndpoint huTwo hhi
      (by norm_num) sectionSixBuchstabMiddleProfile_nineFour_le
  · exact buchstabFunction_le_middleIncreasingEndpoint huTwo hhi
      (by norm_num) sectionSixBuchstabMiddleProfile_nineteenEight_le
  · exact buchstabFunction_le_middleIncreasingEndpoint huTwo hhi
      (by norm_num) sectionSixBuchstabMiddleProfile_fiveTwo_le
  · exact buchstabFunction_le_middleIncreasingEndpoint huTwo hhi
      (by norm_num) sectionSixBuchstabMiddleProfile_twentyOneEight_le
  · exact buchstabFunction_le_middleIncreasingEndpoint huTwo hhi
      (by norm_num) sectionSixBuchstabMiddleProfile_elevenFour_le
  · exact buchstabFunction_le_middleEnvelope huTwo huThree
  · rw [buchstabFunction_eq_one_add_log_sub_one_div huTwo huThree]
    change sectionSixBuchstabMiddleProfile u <= 2832363 / 5000000
    exact (sectionSixBuchstabMiddleProfile_antitoneOn
      (⟨by norm_num, by norm_num⟩ : (23 / 8 : Real) ∈ Icc (23 / 8) 3)
      (⟨hlo, huThree⟩ : u ∈ Icc (23 / 8) 3) hlo).trans
        sectionSixBuchstabMiddleProfile_twentyThreeEight_le

end

end PrimesRestrictedDigits
