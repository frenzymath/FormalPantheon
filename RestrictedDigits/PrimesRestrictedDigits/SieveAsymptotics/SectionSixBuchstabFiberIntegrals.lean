import PrimesRestrictedDigits.BasicEstimates.BuchstabMiddleEnvelope
import PrimesRestrictedDigits.BasicEstimates.BuchstabTailEnvelope
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixBuchstabInverseFiberIntegral
/-!
# Section Six Buchstab fiber integrals

The three weak-endpoint branch formulas expose the exact fiber API used by
the directed Section 6 integral certificate.
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

theorem sectionSixFiber_integral_constant_inv_sq
    {C u v w l h : Real}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hl : 0 < l) (hlh : l < h) :
    (∫ t in l..h, C / (u * v * w * t ^ 2)) =
      C / (u * v * w) * (1 / l - 1 / h) := by
  let K : Real := C / (u * v * w)
  have hderiv : forall t : Real, t ∈ uIcc l h ->
      HasDerivAt (fun s : Real => -K * s⁻¹)
        (C / (u * v * w * t ^ 2)) t := by
    intro t ht
    rw [uIcc_of_le hlh.le] at ht
    have htPos : 0 < t := hl.trans_le ht.1
    dsimp only [K]
    convert (hasDerivAt_inv htPos.ne').const_mul
      (-(C / (u * v * w))) using 1 <;>
        first | rfl | field_simp
  have hint : IntervalIntegrable
      (fun t : Real => C / (u * v * w * t ^ 2)) volume l h := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro t ht
    rw [uIcc_of_le hlh.le] at ht
    have htPos : 0 < t := hl.trans_le ht.1
    have hden : u * v * w * t ^ 2 ≠ 0 := by positivity
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  dsimp [K]
  field_simp
  ring

private theorem sectionSixFiber_buchstab_intervalIntegrable_strict
    {u v w B l h : Real}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hl : 0 < l) (hlh : l < h) (hAOne : 2 * h <= B) :
    IntervalIntegrable
      (fun t : Real =>
        buchstabFunction ((B - t) / t) / (u * v * w * t ^ 2))
      volume l h := by
  have hratioContinuous : ContinuousOn (fun t : Real => (B - t) / t)
      (uIcc l h) := by
    apply (continuousOn_const.sub continuousOn_id).div continuousOn_id
    intro t ht
    rw [uIcc_of_le hlh.le] at ht
    exact (ne_of_gt (hl.trans_le ht.1))
  have hratioRange : MapsTo (fun t : Real => (B - t) / t)
      (uIcc l h) (Ici 1) := by
    intro t ht
    rw [uIcc_of_le hlh.le] at ht
    rw [mem_Ici, le_div_iff₀ (hl.trans_le ht.1)]
    linarith [ht.2]
  have homega : ContinuousOn
      (fun t : Real => buchstabFunction ((B - t) / t)) (uIcc l h) :=
    continuousOn_buchstabFunction.comp hratioContinuous hratioRange
  apply ContinuousOn.intervalIntegrable
  apply homega.div (by fun_prop)
  intro t ht
  rw [uIcc_of_le hlh.le] at ht
  have htPos : 0 < t := hl.trans_le ht.1
  positivity

theorem sectionSixBuchstabFiber_intervalIntegrable
    {u v w B l h : Real}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hl : 0 < l) (hlh : l <= h) (hAOne : 2 * h <= B) :
    IntervalIntegrable
      (fun t : Real =>
        buchstabFunction ((B - t) / t) / (u * v * w * t ^ 2))
      volume l h := by
  rcases hlh.eq_or_lt with rfl | hlh
  · simp
  · exact sectionSixFiber_buchstab_intervalIntegrable_strict
      hu hv hw hl hlh hAOne

private theorem sectionSixFiber_middle_strict
    {u v w B l h : Real}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hl : 0 < l) (hlh : l < h)
    (hATwo : 3 * h <= B) (hAThree : B <= 4 * l) :
    (∫ t in l..h,
      buchstabFunction ((B - t) / t) / (u * v * w * t ^ 2)) <=
      (70893 / 125000 : Real) / (u * v * w) * (1 / l - 1 / h) := by
  have hfunInt := sectionSixFiber_buchstab_intervalIntegrable_strict
    hu hv hw hl hlh (by linarith : 2 * h <= B)
  have hconstInt : IntervalIntegrable
      (fun t : Real => (70893 / 125000 : Real) /
        (u * v * w * t ^ 2)) volume l h := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro t ht
    rw [uIcc_of_le hlh.le] at ht
    have htPos : 0 < t := hl.trans_le ht.1
    have hden : u * v * w * t ^ 2 ≠ 0 := by positivity
    fun_prop
  calc
    (∫ t in l..h,
        buchstabFunction ((B - t) / t) / (u * v * w * t ^ 2)) <=
        ∫ t in l..h, (70893 / 125000 : Real) /
          (u * v * w * t ^ 2) := by
      apply intervalIntegral.integral_mono_on hlh.le hfunInt hconstInt
      intro t ht
      have htPos : 0 < t := hl.trans_le ht.1
      have hArgTwo : 2 <= (B - t) / t := by
        rw [le_div_iff₀ htPos]
        linarith [ht.2]
      have hArgThree : (B - t) / t <= 3 := by
        rw [div_le_iff₀ htPos]
        linarith [ht.1]
      have hden : 0 < u * v * w * t ^ 2 := by positivity
      exact (div_le_div_iff_of_pos_right hden).2
        (buchstabFunction_le_middleEnvelope hArgTwo hArgThree)
    _ = (70893 / 125000 : Real) / (u * v * w) *
        (1 / l - 1 / h) :=
      sectionSixFiber_integral_constant_inv_sq hu hv hw hl hlh

private theorem sectionSixFiber_tail_strict
    {u v w B l h : Real}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hl : 0 < l) (hlh : l < h) (hAThree : 4 * h <= B) :
    (∫ t in l..h,
      buchstabFunction ((B - t) / t) / (u * v * w * t ^ 2)) <=
      (564383 / 1000000 : Real) / (u * v * w) *
        (1 / l - 1 / h) := by
  have hfunInt := sectionSixFiber_buchstab_intervalIntegrable_strict
    hu hv hw hl hlh (by linarith : 2 * h <= B)
  have hconstInt : IntervalIntegrable
      (fun t : Real => (564383 / 1000000 : Real) /
        (u * v * w * t ^ 2)) volume l h := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro t ht
    rw [uIcc_of_le hlh.le] at ht
    have htPos : 0 < t := hl.trans_le ht.1
    have hden : u * v * w * t ^ 2 ≠ 0 := by positivity
    fun_prop
  calc
    (∫ t in l..h,
        buchstabFunction ((B - t) / t) / (u * v * w * t ^ 2)) <=
        ∫ t in l..h, (564383 / 1000000 : Real) /
          (u * v * w * t ^ 2) := by
      apply intervalIntegral.integral_mono_on hlh.le hfunInt hconstInt
      intro t ht
      have htPos : 0 < t := hl.trans_le ht.1
      have hArgThree : 3 <= (B - t) / t := by
        rw [le_div_iff₀ htPos]
        linarith [ht.2]
      have hden : 0 < u * v * w * t ^ 2 := by positivity
      exact (div_le_div_iff_of_pos_right hden).2
        (buchstabFunction_le_tailEnvelope hArgThree)
    _ = (564383 / 1000000 : Real) / (u * v * w) *
        (1 / l - 1 / h) :=
      sectionSixFiber_integral_constant_inv_sq hu hv hw hl hlh

theorem integral_sectionSixBuchstabMiddleBranch_le
    {u v w B l h : Real}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hl : 0 < l) (hlh : l <= h)
    (hATwo : 3 * h <= B) (hAThree : B <= 4 * l) :
    (∫ t in l..h,
      buchstabFunction ((B - t) / t) / (u * v * w * t ^ 2)) <=
      (70893 / 125000 : Real) / (u * v * w) * (1 / l - 1 / h) := by
  rcases hlh.eq_or_lt with rfl | hlh
  · simp
  · exact sectionSixFiber_middle_strict
      hu hv hw hl hlh hATwo hAThree

theorem integral_sectionSixBuchstabTailBranch_le
    {u v w B l h : Real}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hl : 0 < l) (hlh : l <= h) (hAThree : 4 * h <= B) :
    (∫ t in l..h,
      buchstabFunction ((B - t) / t) / (u * v * w * t ^ 2)) <=
      (564383 / 1000000 : Real) / (u * v * w) *
        (1 / l - 1 / h) := by
  rcases hlh.eq_or_lt with rfl | hlh
  · simp
  · exact sectionSixFiber_tail_strict
      hu hv hw hl hlh hAThree

end

end PrimesRestrictedDigits
