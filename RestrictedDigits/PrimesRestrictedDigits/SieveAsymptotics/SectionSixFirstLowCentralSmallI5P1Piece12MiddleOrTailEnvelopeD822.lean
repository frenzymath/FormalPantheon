import PrimesRestrictedDigits.SieveAsymptotics.SectionSixBuchstabFiberIntegrals
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1TransformedGeometryD807
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece0Row0CompositionD817
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-! # SectionSixFirstLowCentralSmallI5P1Piece12MiddleOrTailEnvelopeD822 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set

namespace PrimesRestrictedDigits
noncomputable section

/-!
# transformed P1 Piece1/Piece2 middle-or-tail fiber envelope

This fixed-delta module ports the conditional fiber bridge. It provides the global Buchstab
envelope, the inverse-square interval adapter, the common pair-sum wall, closed-piece
wrappers, and the transformed-kernel adapter. It makes no outer integral, cap, aggregate, or
source claim.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.12).
-/

private abbrev d822Beta : Real :=
  sectionSixFirstLowCentralSmallI5P1D807Beta
private abbrev d822Gap : Real :=
  sectionSixFirstLowCentralSmallI5P1D807Gap
private abbrev d822A : Real :=
  sectionSixFirstLowCentralSmallI5P1D807A
private abbrev d822Ds : Real :=
  sectionSixFirstLowCentralSmallI5P1D807Ds
private abbrev d822Dr : Real :=
  sectionSixFirstLowCentralSmallI5P1D807Dr
private abbrev d822D1 : Real :=
  sectionSixFirstLowCentralSmallI5P1D807D1
private abbrev d822L : Real → Real :=
  sectionSixFirstLowCentralSmallI5P1D807L

theorem sectionSixFirstLowCentralSmallI5P1D822_buchstab_le_middle_constant_of_two_le
    {y : Real} (hy : 2 <= y) :
    buchstabFunction y <= (70893 / 125000 : Real) := by
  by_cases hy3 : y <= 3
  · exact buchstabFunction_le_middleEnvelope hy hy3
  · have htail := buchstabFunction_le_tailEnvelope
      (show 3 <= y by linarith)
    exact htail.trans (by norm_num)

private theorem d822_integral_constant_inv_sq
    {C u v w l h : Real}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hl : 0 < l) (hlh : l < h) :
    (∫ t in l..h, C / (u * v * w * t ^ 2)) =
      C / (u * v * w) * (1 / l - 1 / h) := by
  let k : Real := C / (u * v * w)
  have hderiv : forall t : Real, t ∈ uIcc l h ->
      HasDerivAt (fun s : Real => -k * s⁻¹)
        (C / (u * v * w * t ^ 2)) t := by
    intro t ht
    rw [uIcc_of_le hlh.le] at ht
    have htPos : 0 < t := hl.trans_le ht.1
    dsimp only [k]
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
  dsimp [k]
  field_simp
  ring

theorem sectionSixFirstLowCentralSmallI5P1D822_integral_middle_or_tail_le
    {u v w B l h : Real}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hl : 0 < l) (hlh : l <= h) (hTwoWall : 3 * h <= B) :
    (∫ t in l..h,
      buchstabFunction ((B - t) / t) /
        (u * v * w * t ^ 2)) <=
      (70893 / 125000 : Real) / (u * v * w) *
        (1 / l - 1 / h) := by
  rcases hlh.eq_or_lt with rfl | hlh
  · simp
  · have hfunInt := sectionSixBuchstabFiber_intervalIntegrable
      hu hv hw hl hlh.le (by linarith : 2 * h <= B)
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
          buchstabFunction ((B - t) / t) /
            (u * v * w * t ^ 2)) <=
          ∫ t in l..h, (70893 / 125000 : Real) /
            (u * v * w * t ^ 2) := by
        apply intervalIntegral.integral_mono_on hlh.le hfunInt hconstInt
        intro t ht
        have htPos : 0 < t := hl.trans_le ht.1
        have hyTwo : 2 <= (B - t) / t := by
          rw [le_div_iff₀ htPos]
          linarith [ht.2]
        have hden : 0 < u * v * w * t ^ 2 := by positivity
        exact (div_le_div_iff_of_pos_right hden).2
          (sectionSixFirstLowCentralSmallI5P1D822_buchstab_le_middle_constant_of_two_le
            hyTwo)
      _ = (70893 / 125000 : Real) / (u * v * w) *
          (1 / l - 1 / h) :=
        d822_integral_constant_inv_sq hu hv hw hl hlh

theorem sectionSixFirstLowCentralSmallI5P1D822_piece12_three_upper
    {d r s : Real}
    (hd : d <= sectionSixFirstLowCentralSmallI5P1D807D1)
    (hrs : r + s <= sectionSixFirstLowCentralSmallI5P1D807L d) :
    3 * (d - sectionSixFirstLowCentralSmallI5P1D807Gap) <=
      1 - sectionSixFirstLowCentralSmallI5P1D807Beta - d - r - s := by
  rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
    ⟨ha, hbeta, hgap, hd0, hds, hdr, hd1⟩
  change r + s <= sectionSixFirstLowCentralSmallI5P1D807A - 2 * d at hrs
  change d <= sectionSixFirstLowCentralSmallI5P1D807D1 at hd
  rw [hd1] at hd
  rw [ha] at hrs
  rw [hbeta, hgap]
  norm_num at hd hrs ⊢
  linarith [hd, hrs]

theorem sectionSixFirstLowCentralSmallI5P1D822_dr_le_d1 :
    sectionSixFirstLowCentralSmallI5P1D807Dr <=
      sectionSixFirstLowCentralSmallI5P1D807D1 := by
  rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
    ⟨ha, hbeta, hgap, hd0, hds, hdr, hd1⟩
  rw [hdr, hd1]
  norm_num

theorem sectionSixFirstLowCentralSmallI5P1D822_piece1_pair_sum_le
    {d r s : Real}
    (_hd : d ∈ Set.Icc
      sectionSixFirstLowCentralSmallI5P1D807Ds
      sectionSixFirstLowCentralSmallI5P1D807Dr)
    (_hr : r ∈ Set.Icc 0
      (sectionSixFirstLowCentralSmallI5P1D807H d))
    (hs : s ∈ Set.Icc 0
      (min r (sectionSixFirstLowCentralSmallI5P1D807L d - r))) :
    r + s <= sectionSixFirstLowCentralSmallI5P1D807L d := by
  have hsL := (le_min_iff.mp hs.2).2
  linarith

theorem sectionSixFirstLowCentralSmallI5P1D822_piece2_pair_sum_le
    {d r s : Real}
    (_hd : d ∈ Set.Icc
      sectionSixFirstLowCentralSmallI5P1D807Dr
      sectionSixFirstLowCentralSmallI5P1D807D1)
    (_hr : r ∈ Set.Icc 0
      (sectionSixFirstLowCentralSmallI5P1D807L d))
    (hs : s ∈ Set.Icc 0
      (min r (sectionSixFirstLowCentralSmallI5P1D807L d - r))) :
    r + s <= sectionSixFirstLowCentralSmallI5P1D807L d := by
  have hsL := (le_min_iff.mp hs.2).2
  linarith

theorem sectionSixFirstLowCentralSmallI5P1D822_piece1_three_upper
    {d r s t : Real}
    (hz : (((d, r), s), t) ∈
      sectionSixFirstLowCentralSmallI5P1D807Piece1) :
    3 * (d - sectionSixFirstLowCentralSmallI5P1D807Gap) <=
      1 - sectionSixFirstLowCentralSmallI5P1D807Beta - d - r - s := by
  rcases hz with ⟨hd, hr, hs, ht⟩
  have hrs := sectionSixFirstLowCentralSmallI5P1D822_piece1_pair_sum_le
    hd hr hs
  exact sectionSixFirstLowCentralSmallI5P1D822_piece12_three_upper
    (hd.2.trans sectionSixFirstLowCentralSmallI5P1D822_dr_le_d1) hrs

theorem sectionSixFirstLowCentralSmallI5P1D822_piece2_three_upper
    {d r s t : Real}
    (hz : (((d, r), s), t) ∈
      sectionSixFirstLowCentralSmallI5P1D807Piece2) :
    3 * (d - sectionSixFirstLowCentralSmallI5P1D807Gap) <=
      1 - sectionSixFirstLowCentralSmallI5P1D807Beta - d - r - s := by
  rcases hz with ⟨hd, hr, hs, ht⟩
  have hrs := sectionSixFirstLowCentralSmallI5P1D822_piece2_pair_sum_le
    hd hr hs
  exact sectionSixFirstLowCentralSmallI5P1D822_piece12_three_upper hd.2 hrs

theorem sectionSixFirstLowCentralSmallI5P1D822_piece12_fiber_le
    {d r s : Real}
    (hdLower : sectionSixFirstLowCentralSmallI5P1D807Ds <= d)
    (hdUpper : d <= sectionSixFirstLowCentralSmallI5P1D807D1)
    (hr : 0 <= r) (hs : 0 <= s)
    (hrs : r + s <= sectionSixFirstLowCentralSmallI5P1D807L d) :
    (∫ t in sectionSixFirstLowCentralSmallI5P1D807Gap..
        (d - sectionSixFirstLowCentralSmallI5P1D807Gap),
      buchstabFunction
          ((1 - sectionSixFirstLowCentralSmallI5P1D807Beta - d - r - s - t) / t) /
        ((sectionSixFirstLowCentralSmallI5P1D807Beta - d) *
          (d + r) * (d + s) * t ^ 2)) <=
      (70893 / 125000 : Real) /
          ((sectionSixFirstLowCentralSmallI5P1D807Beta - d) *
            (d + r) * (d + s)) *
        (1 / sectionSixFirstLowCentralSmallI5P1D807Gap -
          1 / (d - sectionSixFirstLowCentralSmallI5P1D807Gap)) := by
  have hGap : 0 < d822Gap := by
    rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
      ⟨_, _, hgap, _, _, _, _⟩
    simpa [d822Gap] using hgap ▸ (by norm_num : (0 : Real) < 16249 / 250000)
  have hDs : 0 < d822Ds := by
    rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
      ⟨_, _, _, _, hds, _, _⟩
    simpa [d822Ds] using hds ▸ (by norm_num : (0 : Real) < 29 / 200)
  have hBeta : d822D1 < d822Beta := by
    rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
      ⟨_, hbeta, _, _, _, _, hd1⟩
    change sectionSixFirstLowCentralSmallI5P1D807D1 <
      sectionSixFirstLowCentralSmallI5P1D807Beta
    rw [hd1, hbeta]
    norm_num
  have hu : 0 < d822Beta - d := by linarith
  have hv : 0 < d + r := by linarith
  have hw : 0 < d + s := by linarith
  have hlh : d822Gap <= d - d822Gap := by
    rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
      ⟨_, _, hgap, _, hds, _, _⟩
    change sectionSixFirstLowCentralSmallI5P1D807Gap <= d -
      sectionSixFirstLowCentralSmallI5P1D807Gap
    rw [hgap] at ⊢
    rw [hds] at hdLower
    norm_num at hdLower ⊢
    linarith
  exact sectionSixFirstLowCentralSmallI5P1D822_integral_middle_or_tail_le
    hu hv hw hGap hlh
    (sectionSixFirstLowCentralSmallI5P1D822_piece12_three_upper hdUpper hrs)

theorem sectionSixFirstLowCentralSmallI5P1D822_kernel_fiber_le
    {d r s : Real}
    (hdLower : sectionSixFirstLowCentralSmallI5P1D807Ds <= d)
    (hdUpper : d <= sectionSixFirstLowCentralSmallI5P1D807D1)
    (hr : 0 <= r) (hs : 0 <= s)
    (hrs : r + s <= sectionSixFirstLowCentralSmallI5P1D807L d) :
    (∫ t in sectionSixFirstLowCentralSmallI5P1D807Gap..
        (d - sectionSixFirstLowCentralSmallI5P1D807Gap),
      sectionSixFirstLowCentralSmallI5P1D817Kernel (((d, r), s), t)) <=
      (70893 / 125000 : Real) /
        ((sectionSixFirstLowCentralSmallI5P1D807Beta - d) *
          (d + r) * (d + s)) *
        (1 / sectionSixFirstLowCentralSmallI5P1D807Gap -
          1 / (d - sectionSixFirstLowCentralSmallI5P1D807Gap)) := by
  calc
    (∫ t in sectionSixFirstLowCentralSmallI5P1D807Gap..
        (d - sectionSixFirstLowCentralSmallI5P1D807Gap),
      sectionSixFirstLowCentralSmallI5P1D817Kernel (((d, r), s), t)) =
      ∫ t in sectionSixFirstLowCentralSmallI5P1D807Gap..
        (d - sectionSixFirstLowCentralSmallI5P1D807Gap),
        buchstabFunction
            ((1 - sectionSixFirstLowCentralSmallI5P1D807Beta - d - r - s - t) / t) /
          ((sectionSixFirstLowCentralSmallI5P1D807Beta - d) *
            (d + r) * (d + s) * t ^ (2 : Nat)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      convert (sectionSixFirstLowCentralSmallI5P1D817_kernel_formula d r s t) using 1;
        norm_num [sectionSixFirstLowCentralSmallI5P1D816Row0Beta,
          sectionSixFirstLowCentralSmallI5P1D807Beta, sectionSixThetaTwo,
          sectionSixFirstLowCentralSmallI5P1D807Delta]
    _ <= _ := by
      simpa only [pow_two] using
        (sectionSixFirstLowCentralSmallI5P1D822_piece12_fiber_le
          hdLower hdUpper hr hs hrs)


end
end PrimesRestrictedDigits
