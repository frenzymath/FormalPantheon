import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6AllLabelFiberRegularityD1007
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixI6ChamberAffineKernelD1006

/-!
# The reciprocal majorant and its inverse-branch bound

The first branch uses omega(s) = 1/s <= 1, not the logarithmic payload. Source:
`MAYNARD-PRD-PUBLISHED`, Section 6, p.144, Eq. (6.13).
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

def i6D1008Majorant (label : i6D691Label) (z : (Real × Real) × Real) : Real :=
  (i6D1006BranchCap label.2.1 : Real) / (z.1.1 * z.1.2 * z.2) *
    (1 / i6D1007Lower label z - 1 / i6D1007Upper label z)

theorem i6D1008Majorant_continuousOn (label : i6D691Label) :
    ContinuousOn (i6D1008Majorant label) (i6D1007OrderedBase label) := by
  have he := i6D1007_endpoints_continuous label
  unfold i6D1008Majorant
  refine (continuousOn_const.div (by fun_prop) ?_).mul
    ((continuousOn_const.div he.1.continuousOn ?_).sub
      (continuousOn_const.div he.2.continuousOn ?_))
  · intro z hz
    have hp := i6D1007OrderedBase_positive label hz
    exact mul_ne_zero (mul_ne_zero hp.1.ne' hp.2.1.ne') hp.2.2.1.ne'
  · intro z hz
    exact (i6D1007OrderedBase_positive label hz).2.2.2.1.ne'
  · intro z hz
    exact (i6D1007OrderedBase_positive label hz).2.2.2.2.ne'

theorem i6D1008Majorant_integrable (label : i6D691Label) :
    IntegrableOn (i6D1008Majorant label) (i6D1007OrderedBase label) volume := by
  exact (i6D1008Majorant_continuousOn label).integrableOn_compact
    (i6D1007OrderedBase_compact_measurable label).1

theorem i6D1008Majorant_nonneg (label : i6D691Label) {z : (Real × Real) × Real}
    (hz : z ∈ i6D1007OrderedBase label) : 0 ≤ i6D1008Majorant label z := by
  have hp := i6D1007OrderedBase_positive label hz
  have hcap : 0 ≤ (i6D1006BranchCap label.2.1 : Real) := by
    generalize label.2.1 = b
    fin_cases b <;> norm_num [i6D1006BranchCap]
  exact mul_nonneg (div_nonneg hcap
    (mul_nonneg (mul_nonneg hp.1.le hp.2.1.le) hp.2.2.1.le))
      (sub_nonneg.mpr (one_div_le_one_div_of_le hp.2.2.2.1 hz.2))

theorem i6D1008_inverseBranch_fiberIntegral_le {u v w S l h : Real}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) (hl : 0 < l) (hlh : l ≤ h)
    (hrange : ∀ t ∈ Icc l h, 1 ≤ (S - t) / t ∧ (S - t) / t ≤ 2) :
    (∫ t in l..h, buchstabFunction ((S - t) / t) / (u * v * w * t ^ 2)) ≤
      1 / (u * v * w) * (1 / l - 1 / h) := by
  rcases hlh.eq_or_lt with rfl | hlh
  · simp
  · have hS : 2 * h ≤ S := by
      have harg := (hrange h ⟨hlh.le, le_rfl⟩).1
      rw [le_div_iff₀ (hl.trans hlh)] at harg
      linarith
    have hf := sectionSixBuchstabFiber_intervalIntegrable hu hv hw hl hlh.le hS
    have hg : IntervalIntegrable (fun t : Real => 1 / (u * v * w * t ^ 2)) volume l h := by
      apply ContinuousOn.intervalIntegrable
      apply continuousOn_of_forall_continuousAt
      intro t ht
      rw [uIcc_of_le hlh.le] at ht
      have htpos : 0 < t := hl.trans_le ht.1
      have hden : u * v * w * t ^ 2 ≠ 0 := by positivity
      fun_prop
    calc
      _ ≤ ∫ t in l..h, 1 / (u * v * w * t ^ 2) := by
        apply intervalIntegral.integral_mono_on hlh.le hf hg
        intro t ht
        have htpos : 0 < t := hl.trans_le ht.1
        have hden : 0 < u * v * w * t ^ 2 := by positivity
        apply (div_le_div_iff_of_pos_right hden).mpr
        rw [buchstabFunction_eq_inv (hrange t ht).1 (hrange t ht).2]
        exact inv_le_one_of_one_le₀ (hrange t ht).1
      _ = _ := sectionSixFiber_integral_constant_inv_sq hu hv hw hl hlh

end

end PrimesRestrictedDigits
