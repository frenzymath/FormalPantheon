import PrimesRestrictedDigits.BasicEstimates.CayleyLogUpper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighFarFiberReduction
/-! # SectionSixFirstHighFarCellAnalytic -/

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section
theorem highFar_cayley_bounds {r s : Real} (hr : 1 ≤ r) (hrs : r ≤ s) :
    let x := (r - 1) / (r + 1)
    let y := (s - 1) / (s + 1)
    0 ≤ x ∧ x ≤ y ∧ y < 1 := by
  dsimp
  have hrden : 0 < r + 1 := by linarith
  have hsden : 0 < s + 1 := by linarith
  refine ⟨div_nonneg (by linarith) hrden.le, ?_, ?_⟩
  · rw [div_le_div_iff₀ hrden hsden]
    nlinarith
  · rw [div_lt_one hsden]
    linarith

theorem highFar_cayley_mono {x y : Real} (hx : 0 ≤ x) (hxy : x ≤ y)
    (hy : y < 1) : cayleyLogSeriesUpper x 5 ≤ cayleyLogSeriesUpper y 5 := by
  have hyNonneg : 0 ≤ y := hx.trans hxy
  have hpow : ∀ n : Nat, x ^ n ≤ y ^ n := fun n => pow_le_pow_left₀ hx hxy n
  unfold cayleyLogSeriesUpper
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact add_le_add
    (Finset.sum_le_sum fun i _ => div_le_div_of_nonneg_right (hpow _) (by positivity))
    (div_le_div₀ (pow_nonneg hyNonneg _) (hpow _)
      (sub_pos.mpr (by nlinarith [(sq_lt_sq₀ hyNonneg zero_le_one).2 hy]))
      (by nlinarith [(sq_le_sq₀ hx hyNonneg).2 hxy]))

theorem highFar_log_ratio_le_endpoint {r s : Real} (hr : 1 ≤ r) (hrs : r ≤ s) :
    Real.log r ≤ cayleyLogSeriesUpper ((s - 1) / (s + 1)) 5 := by
  rcases highFar_cayley_bounds hr hrs with ⟨hx, hxy, hy⟩
  have hreconstruct :
      (1 + (r - 1) / (r + 1)) / (1 - (r - 1) / (r + 1)) = r := by
    have : r + 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [← hreconstruct]
  exact (log_cayley_le_cayleyLogSeriesUpper hx (lt_of_le_of_lt hxy hy) 5).trans
    (highFar_cayley_mono hx hxy hy)


theorem highFar_outer_facts (branch : Fin 2) {u : Real}
    (hu : u ∈ sectionSixFirstHighFarCertificateOuter branch) :
    0 < u ∧ 0 < sectionSixFirstHighFarCertificateLower u ∧
      sectionSixFirstHighFarCertificateLower u ≤
        sectionSixFirstHighFarCertificateUpper u ∧
      sectionSixFirstHighFarCertificateUpper u < 1 - u := by
  fin_cases branch
  · change (212499 / 500000 : Real) ≤ u ∧ u ≤ 459997 / 1000000 at hu
    change 0 < u ∧ 0 < (319999 / 500000 : Real) - u ∧
      (319999 / 500000 : Real) - u ≤ (1 - u) / 2 ∧
      (1 - u) / 2 < 1 - u
    norm_num at hu ⊢
    rcases hu with ⟨huL, huU⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · change (459997 / 1000000 : Real) ≤ u ∧ u ≤ 1 / 2 at hu
    change 0 < u ∧ 0 < (319999 / 500000 : Real) - u ∧
      (319999 / 500000 : Real) - u ≤ (1 - u) / 2 ∧
      (1 - u) / 2 < 1 - u
    norm_num at hu ⊢
    rcases hu with ⟨huL, huU⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem highFar_log_two_upper :
    Real.log 2 ≤ cayleyLogSeriesUpper (1 / 3 : Real) 5 := by
  have h := log_cayley_le_cayleyLogSeriesUpper
    (x := (1 / 3 : Real)) (by norm_num) (by norm_num) 5
  convert h using 1
  all_goals norm_num

theorem highFar_inner_intervalIntegrable (branch : Fin 2) {u : Real}
    (hu : u ∈ sectionSixFirstHighFarCertificateOuter branch) :
    IntervalIntegrable
      (fun v => sectionSixFirstHighFarCertificateTransposedKernel (u, v))
      volume (sectionSixFirstHighFarCertificateLower u)
        (sectionSixFirstHighFarCertificateUpper u) := by
  have ho := highFar_outer_facts branch hu
  let l : Real := sectionSixFirstHighFarCertificateLower u
  let h : Real := sectionSixFirstHighFarCertificateUpper u
  have hratio : ContinuousOn (fun v : Real => (1 - u - v) / v) (uIcc l h) := by
    apply (continuousOn_const.sub continuousOn_id).div continuousOn_id
    intro v hv
    rw [uIcc_of_le ho.2.2.1] at hv
    exact (ho.2.1.trans_le hv.1).ne'
  have hrange : MapsTo (fun v : Real => (1 - u - v) / v)
      (uIcc l h) (Ici 1) := by
    intro v hv
    rw [uIcc_of_le ho.2.2.1] at hv
    rw [mem_Ici, le_div_iff₀ (ho.2.1.trans_le hv.1)]
    have hvUpper : v ≤ (1 - u) / 2 := by
      have hUpper := hv.2
      change v ≤ (1 - u) / 2 at hUpper
      exact hUpper
    linarith [hvUpper]
  have hcont : ContinuousOn
      (fun v : Real => buchstabFunction ((1 - u - v) / v) /
        (u * v ^ 2)) (uIcc l h) := by
    apply (continuousOn_buchstabFunction.comp hratio hrange).div
      (by fun_prop (disch := positivity))
    intro v hv
    rw [uIcc_of_le ho.2.2.1] at hv
    have hvPos : 0 < v := ho.2.1.trans_le hv.1
    exact (mul_pos ho.1 (sq_pos_of_pos hvPos)).ne'
  change IntervalIntegrable _ volume l h
  apply ContinuousOn.intervalIntegrable
  exact hcont


end
end PrimesRestrictedDigits
