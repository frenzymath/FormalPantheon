import PrimesRestrictedDigits.SieveAsymptotics.SectionSixBuchstabFiberIntegrals
import PrimesRestrictedDigits.BasicEstimates.BuchstabShortMiddleEnvelope

/-!
# clamped four-branch Buchstab fiber bound

This module refines the middle Buchstab branch at the rational short-middle breakpoint while
retaining the exact inverse-branch logarithm.
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

def sectionSixBuchstabClamp (l h x : Real) : Real :=
  max l (min h x)

private abbrev sectionSixBuchstabShortMiddleArgument : Real :=
  180001 / 69999

def sectionSixBuchstabShortMiddleBreakpoint (B : Real) : Real :=
  B * 69999 / 250000

private theorem sectionSixBuchstabClamp_mem {l h x : Real} (hlh : l <= h) :
    l <= sectionSixBuchstabClamp l h x ∧
      sectionSixBuchstabClamp l h x <= h := by
  constructor
  · exact le_max_left _ _
  · exact max_le hlh (min_le_left _ _)

private theorem sectionSixBuchstabClamp_eq_left {l h x : Real}
    (hlh : l <= h) (hx : x <= l) :
    sectionSixBuchstabClamp l h x = l := by
  rw [sectionSixBuchstabClamp, min_eq_right (hx.trans hlh), max_eq_left hx]

private theorem sectionSixBuchstabClamp_eq_right {l h x : Real}
    (hlh : l <= h) (hx : h <= x) :
    sectionSixBuchstabClamp l h x = h := by
  rw [sectionSixBuchstabClamp, min_eq_left hx, max_eq_right hlh]

private theorem sectionSixBuchstabConstantInvSq
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

private theorem sectionSixBuchstabShortMiddleFiber_le
    {u v w B l h : Real}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hl : 0 < l) (hlh : l <= h)
    (hthree : 3 * h <= B)
    (hbreak : sectionSixBuchstabShortMiddleBreakpoint B <= l) :
    (∫ t in l..h,
      buchstabFunction ((B - t) / t) / (u * v * w * t ^ 2)) <=
      (564663 / 1000000 : Real) / (u * v * w) *
        (1 / l - 1 / h) := by
  rcases hlh.eq_or_lt with rfl | hlh
  · simp
  · have hfun := sectionSixBuchstabFiber_intervalIntegrable
      hu hv hw hl hlh.le (by linarith : 2 * h <= B)
    have hconst : IntervalIntegrable
        (fun t : Real => (564663 / 1000000 : Real) /
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
          ∫ t in l..h, (564663 / 1000000 : Real) /
            (u * v * w * t ^ 2) := by
        apply intervalIntegral.integral_mono_on hlh.le hfun hconst
        intro t ht
        have htPos : 0 < t := hl.trans_le ht.1
        have htwo : 2 <= (B - t) / t := by
          rw [le_div_iff₀ htPos]
          linarith [ht.2]
        have htop :
            (B - t) / t <= sectionSixBuchstabShortMiddleArgument := by
          have hbreakT : sectionSixBuchstabShortMiddleBreakpoint B <= t :=
            hbreak.trans ht.1
          rw [div_le_iff₀ htPos]
          dsimp [sectionSixBuchstabShortMiddleBreakpoint] at hbreakT
          dsimp [sectionSixBuchstabShortMiddleArgument]
          norm_num at hbreakT ⊢
          nlinarith
        have hden : 0 < u * v * w * t ^ 2 := by positivity
        exact (div_le_div_iff_of_pos_right hden).2
          (buchstabFunction_le_shortMiddleEnvelope htwo (by
            simpa [sectionSixBuchstabShortMiddleArgument] using htop))
      _ = (564663 / 1000000 : Real) / (u * v * w) *
          (1 / l - 1 / h) :=
        sectionSixBuchstabConstantInvSq hu hv hw hl hlh

theorem sectionSixBuchstabClampedFourBranchFiber_le
    {u v w B l h : Real}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hl : 0 < l) (hlh : l <= h) (hB : 2 * h <= B) :
    let m4 := sectionSixBuchstabClamp l h (B / 4)
    let m3 := sectionSixBuchstabClamp m4 h (B / 3)
    let my0 := sectionSixBuchstabClamp m4 m3
      (sectionSixBuchstabShortMiddleBreakpoint B)
    (∫ t in l..h,
      buchstabFunction ((B - t) / t) / (u * v * w * t ^ 2)) <=
      (564383 / 1000000 : Real) / (u * v * w) * (1 / l - 1 / m4) +
      (70893 / 125000 : Real) / (u * v * w) * (1 / m4 - 1 / my0) +
      (564663 / 1000000 : Real) / (u * v * w) * (1 / my0 - 1 / m3) +
      1 / (u * v * w * B) *
        Real.log (h * (B - m3) / (m3 * (B - h))) := by
  dsimp only
  let m4 := sectionSixBuchstabClamp l h (B / 4)
  let m3 := sectionSixBuchstabClamp m4 h (B / 3)
  let my0 := sectionSixBuchstabClamp m4 m3
    (sectionSixBuchstabShortMiddleBreakpoint B)
  let f : Real -> Real := fun t =>
    buchstabFunction ((B - t) / t) / (u * v * w * t ^ 2)
  have hm4 := sectionSixBuchstabClamp_mem (x := B / 4) hlh
  change l <= m4 ∧ m4 <= h at hm4
  have hm3 := sectionSixBuchstabClamp_mem (x := B / 3) hm4.2
  change m4 <= m3 ∧ m3 <= h at hm3
  have hmy0 := sectionSixBuchstabClamp_mem
    (x := sectionSixBuchstabShortMiddleBreakpoint B) hm3.1
  change m4 <= my0 ∧ my0 <= m3 at hmy0
  have hm4pos : 0 < m4 := hl.trans_le hm4.1
  have hmy0pos : 0 < my0 := hm4pos.trans_le hmy0.1
  have hm3pos : 0 < m3 := hmy0pos.trans_le hmy0.2
  have hhpos : 0 < h := hl.trans_le hlh
  have hBm4 : 2 * m4 <= B := by linarith [hm4.2]
  have hBmy0 : 2 * my0 <= B := by linarith [hmy0.2, hm3.2]
  have hBm3 : 2 * m3 <= B := by linarith [hm3.2]
  have hintTail := sectionSixBuchstabFiber_intervalIntegrable
    hu hv hw hl hm4.1 hBm4
  have hintUpperMiddle := sectionSixBuchstabFiber_intervalIntegrable
    hu hv hw hm4pos hmy0.1 hBmy0
  have hintShortMiddle := sectionSixBuchstabFiber_intervalIntegrable
    hu hv hw hmy0pos hmy0.2 hBm3
  have hintInverse := sectionSixBuchstabFiber_intervalIntegrable
    hu hv hw hm3pos hm3.2 hB
  have htail :
      (∫ t in l..m4, f t) <=
        (564383 / 1000000 : Real) / (u * v * w) *
          (1 / l - 1 / m4) := by
    by_cases hcut : B / 4 <= l
    · have hm4eq : m4 = l := by
        exact sectionSixBuchstabClamp_eq_left hlh hcut
      rw [hm4eq]
      simp
    · have hm4cut : m4 <= B / 4 := by
        change sectionSixBuchstabClamp l h (B / 4) <= B / 4
        exact max_le (le_of_not_ge hcut) (min_le_right _ _)
      change
        (∫ t in l..m4,
          buchstabFunction ((B - t) / t) / (u * v * w * t ^ 2)) <= _
      exact integral_sectionSixBuchstabTailBranch_le
        hu hv hw hl hm4.1 (by linarith)
  have hupperMiddle :
      (∫ t in m4..my0, f t) <=
        (70893 / 125000 : Real) / (u * v * w) *
          (1 / m4 - 1 / my0) := by
    by_cases hcutFour : h <= B / 4
    · have hm4eq : m4 = h := by
        exact sectionSixBuchstabClamp_eq_right hlh hcutFour
      have hm3eq : m3 = h := by
        change sectionSixBuchstabClamp m4 h (B / 3) = h
        exact sectionSixBuchstabClamp_eq_right hm4.2 (by linarith)
      have hmy0eq : my0 = h := by
        change sectionSixBuchstabClamp m4 m3
          (sectionSixBuchstabShortMiddleBreakpoint B) = h
        rw [hm4eq, hm3eq, sectionSixBuchstabClamp]
        simp
      rw [hm4eq, hmy0eq]
      simp
    · have hfour : B <= 4 * m4 := by
        have hcut : B / 4 <= m4 := by
          change B / 4 <= sectionSixBuchstabClamp l h (B / 4)
          rw [sectionSixBuchstabClamp,
            min_eq_right (le_of_not_ge hcutFour)]
          exact le_max_right _ _
        linarith
      by_cases hcutThree : B / 3 <= m4
      · have hm3eq : m3 = m4 := by
          change sectionSixBuchstabClamp m4 h (B / 3) = m4
          exact sectionSixBuchstabClamp_eq_left hm4.2 hcutThree
        have hmy0eq : my0 = m4 := by
          change sectionSixBuchstabClamp m4 m3
            (sectionSixBuchstabShortMiddleBreakpoint B) = m4
          rw [hm3eq, sectionSixBuchstabClamp]
          simp
        rw [hmy0eq]
        simp
      · have hm3cut : m3 <= B / 3 := by
          change sectionSixBuchstabClamp m4 h (B / 3) <= B / 3
          exact max_le (le_of_not_ge hcutThree) (min_le_right _ _)
        change
          (∫ t in m4..my0,
            buchstabFunction ((B - t) / t) / (u * v * w * t ^ 2)) <= _
        exact integral_sectionSixBuchstabMiddleBranch_le
          hu hv hw hm4pos hmy0.1 (by linarith [hmy0.2]) hfour
  have hshortMiddle :
      (∫ t in my0..m3, f t) <=
        (564663 / 1000000 : Real) / (u * v * w) *
          (1 / my0 - 1 / m3) := by
    by_cases hcutThree : B / 3 <= m4
    · have hm3eq : m3 = m4 := by
        change sectionSixBuchstabClamp m4 h (B / 3) = m4
        exact sectionSixBuchstabClamp_eq_left hm4.2 hcutThree
      have hmy0eq : my0 = m3 := by
        change sectionSixBuchstabClamp m4 m3
          (sectionSixBuchstabShortMiddleBreakpoint B) = m3
        rw [hm3eq, sectionSixBuchstabClamp]
        simp
      rw [hmy0eq]
      simp
    · have hm3cut : m3 <= B / 3 := by
        change sectionSixBuchstabClamp m4 h (B / 3) <= B / 3
        exact max_le (le_of_not_ge hcutThree) (min_le_right _ _)
      by_cases hbreakHigh :
          m3 <= sectionSixBuchstabShortMiddleBreakpoint B
      · have hmy0eq : my0 = m3 := by
          change sectionSixBuchstabClamp m4 m3
            (sectionSixBuchstabShortMiddleBreakpoint B) = m3
          exact sectionSixBuchstabClamp_eq_right hm3.1 hbreakHigh
        rw [hmy0eq]
        simp
      · have hbreakLow :
          sectionSixBuchstabShortMiddleBreakpoint B <= my0 := by
          change sectionSixBuchstabShortMiddleBreakpoint B <=
            sectionSixBuchstabClamp m4 m3
              (sectionSixBuchstabShortMiddleBreakpoint B)
          rw [sectionSixBuchstabClamp,
            min_eq_right (le_of_not_ge hbreakHigh)]
          exact le_max_right _ _
        change
          (∫ t in my0..m3,
            buchstabFunction ((B - t) / t) / (u * v * w * t ^ 2)) <= _
        exact sectionSixBuchstabShortMiddleFiber_le
          hu hv hw hmy0pos hmy0.2 (by linarith) hbreakLow
  have hinverse :
      (∫ t in m3..h, f t) <=
        1 / (u * v * w * B) *
          Real.log (h * (B - m3) / (m3 * (B - h))) := by
    by_cases hcut : h <= B / 3
    · have hm3eq : m3 = h := by
        change sectionSixBuchstabClamp m4 h (B / 3) = h
        exact sectionSixBuchstabClamp_eq_right hm4.2 hcut
      have hBh : B - h ≠ 0 := by linarith
      rw [hm3eq]
      simp [hhpos.ne', hBh]
    · have hthree : B <= 3 * m3 := by
        have hcut' : B / 3 <= m3 := by
          change B / 3 <= sectionSixBuchstabClamp m4 h (B / 3)
          rw [sectionSixBuchstabClamp, min_eq_right (le_of_not_ge hcut)]
          exact le_max_right _ _
        linarith
      change
        (∫ t in m3..h,
          buchstabFunction ((B - t) / t) / (u * v * w * t ^ 2)) <= _
      rw [integral_sectionSixBuchstabInverseBranch_eq
        hu hv hw hm3pos hm3.2 hB hthree]
  have hsplitTailUpper := intervalIntegral.integral_add_adjacent_intervals
    hintTail hintUpperMiddle
  have hsplitThroughShort := intervalIntegral.integral_add_adjacent_intervals
    (hintTail.trans hintUpperMiddle) hintShortMiddle
  have hsplitAll := intervalIntegral.integral_add_adjacent_intervals
    ((hintTail.trans hintUpperMiddle).trans hintShortMiddle) hintInverse
  change (∫ t in l..h, f t) <= _
  calc
    (∫ t in l..h, f t) =
        (((∫ t in l..m4, f t) + ∫ t in m4..my0, f t) +
          ∫ t in my0..m3, f t) + ∫ t in m3..h, f t := by
      rw [hsplitTailUpper, hsplitThroughShort, hsplitAll]
    _ <= _ := add_le_add
      (add_le_add (add_le_add htail hupperMiddle) hshortMiddle) hinverse

end

end PrimesRestrictedDigits
