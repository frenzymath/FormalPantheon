import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece12MiddleOrTailEnvelopeD822
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece0Row0AnalyticD816
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-! # SectionSixFirstLowCentralSmallI5P1Piece2Q4FiberAdapterD880 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits
noncomputable section

/-!
# variable-d Piece2 Q4 fiber adapter

This module composes the transformed-kernel fiber envelope with the Q4 reciprocal majorants at
the variable anchor d. It proves only the pointwise t-fiber inequality; outer integration and
numerical caps remain outside this module.
-/

private abbrev G : Real :=
  sectionSixFirstLowCentralSmallI5P1D807Gap
private abbrev Beta : Real :=
  sectionSixFirstLowCentralSmallI5P1D807Beta
private abbrev Ds : Real :=
  sectionSixFirstLowCentralSmallI5P1D807Ds
private abbrev Dr : Real :=
  sectionSixFirstLowCentralSmallI5P1D807Dr
private abbrev D1 : Real :=
  sectionSixFirstLowCentralSmallI5P1D807D1
private abbrev Q4 : Real → Real → Real :=
  sectionSixFirstLowCentralSmallI5P1D816Row0Q4

theorem sectionSixFirstLowCentralSmallI5P1D880_piece2_kernel_fiber_le_q4_self
    {d r s : Real}
    (hd : d ∈ Set.Icc
      sectionSixFirstLowCentralSmallI5P1D807Dr
      sectionSixFirstLowCentralSmallI5P1D807D1)
    (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hrs : r + s ≤ sectionSixFirstLowCentralSmallI5P1D807L d) :
    (∫ t in sectionSixFirstLowCentralSmallI5P1D807Gap..
        (d - sectionSixFirstLowCentralSmallI5P1D807Gap),
      sectionSixFirstLowCentralSmallI5P1D817Kernel (((d, r), s), t)) ≤
      ((70893 / 125000 : Real) /
          (sectionSixFirstLowCentralSmallI5P1D807Beta - d) *
        (1 / sectionSixFirstLowCentralSmallI5P1D807Gap -
          1 / (d - sectionSixFirstLowCentralSmallI5P1D807Gap))) *
        sectionSixFirstLowCentralSmallI5P1D816Row0Q4 d r *
        sectionSixFirstLowCentralSmallI5P1D816Row0Q4 d s := by
  rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
    ⟨hA, hBeta, hGap, hD0, hDs, hDr, hD1⟩
  have hDsDr : Ds ≤ Dr := by
    change sectionSixFirstLowCentralSmallI5P1D807Ds ≤
      sectionSixFirstLowCentralSmallI5P1D807Dr
    rw [hDs, hDr]
    norm_num
  have hDrPos : 0 < Dr := by
    change 0 < sectionSixFirstLowCentralSmallI5P1D807Dr
    rw [hDr]
    norm_num
  have hGapPos : 0 < G := by
    change 0 < sectionSixFirstLowCentralSmallI5P1D807Gap
    rw [hGap]
    norm_num
  have hTwoGapDr : 2 * G ≤ Dr := by
    change 2 * sectionSixFirstLowCentralSmallI5P1D807Gap ≤
      sectionSixFirstLowCentralSmallI5P1D807Dr
    rw [hGap, hDr]
    norm_num
  have hD1Beta : D1 < Beta := by
    change sectionSixFirstLowCentralSmallI5P1D807D1 <
      sectionSixFirstLowCentralSmallI5P1D807Beta
    rw [hD1, hBeta]
    norm_num
  have hdLower : Ds ≤ d := hDsDr.trans hd.1
  have hdPos : 0 < d := hDrPos.trans_le hd.1
  have hGapLe : G ≤ d - G := by
    linarith [hTwoGapDr, hd.1]
  have hdGapPos : 0 < d - G := lt_of_lt_of_le hGapPos hGapLe
  have hBetaDPos : 0 < Beta - d := by
    linarith [hD1Beta, hd.2]
  have hdRPos : 0 < d + r := by linarith
  have hdSPos : 0 < d + s := by linarith
  have hInvBeta0 : 0 ≤ 1 / (Beta - d) :=
    one_div_nonneg.mpr hBetaDPos.le
  have hInvR0 : 0 ≤ 1 / (d + r) :=
    one_div_nonneg.mpr hdRPos.le
  have hInvS0 : 0 ≤ 1 / (d + s) :=
    one_div_nonneg.mpr hdSPos.le
  have hTail0 : 0 ≤ 1 / G - 1 / (d - G) := by
    exact sub_nonneg.mpr (one_div_le_one_div_of_le hGapPos hGapLe)
  have hQr : 1 / (d + r) ≤ Q4 d r := by
    exact sectionSixFirstLowCentralSmallI5P1D816_q4_inv_le hdPos hr
  have hQs : 1 / (d + s) ≤ Q4 d s := by
    exact sectionSixFirstLowCentralSmallI5P1D816_q4_inv_le hdPos hs
  have hQr0 : 0 ≤ Q4 d r := hInvR0.trans hQr
  have hQs0 : 0 ≤ Q4 d s := hInvS0.trans hQs
  have hprod :
      (1 / (Beta - d)) * (1 / (d + r)) * (1 / (d + s)) ≤
        (1 / (Beta - d)) * Q4 d r * Q4 d s := by
    calc
      (1 / (Beta - d)) * (1 / (d + r)) * (1 / (d + s)) ≤
          (1 / (Beta - d)) * Q4 d r * (1 / (d + s)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hQr hInvBeta0) hInvS0
      _ ≤ (1 / (Beta - d)) * Q4 d r * Q4 d s := by
        exact mul_le_mul_of_nonneg_left hQs
          (mul_nonneg hInvBeta0 hQr0)
  have hleft :
      (70893 / 125000 : Real) /
          ((Beta - d) * (d + r) * (d + s)) *
          (1 / G - 1 / (d - G)) =
        (70893 / 125000 : Real) *
          ((1 / (Beta - d)) * (1 / (d + r)) * (1 / (d + s))) *
          (1 / G - 1 / (d - G)) := by
    field_simp [ne_of_gt hBetaDPos, ne_of_gt hdRPos,
      ne_of_gt hdSPos, ne_of_gt hGapPos, ne_of_gt hdGapPos]
  have hbase := sectionSixFirstLowCentralSmallI5P1D822_kernel_fiber_le
    hdLower hd.2 hr hs hrs
  have hbase' :
      (∫ t in G..(d - G),
        sectionSixFirstLowCentralSmallI5P1D817Kernel (((d, r), s), t)) ≤
      (70893 / 125000 : Real) /
          ((Beta - d) * (d + r) * (d + s)) *
          (1 / G - 1 / (d - G)) := by
    simpa [Beta, G, pow_two] using hbase
  have hcoef : 0 ≤ (70893 / 125000 : Real) := by norm_num
  calc
    (∫ t in G..(d - G),
        sectionSixFirstLowCentralSmallI5P1D817Kernel (((d, r), s), t)) ≤
        (70893 / 125000 : Real) /
          ((Beta - d) * (d + r) * (d + s)) *
          (1 / G - 1 / (d - G)) := hbase'
    _ = (70893 / 125000 : Real) *
          ((1 / (Beta - d)) * (1 / (d + r)) * (1 / (d + s))) *
          (1 / G - 1 / (d - G)) := hleft
    _ ≤ (70893 / 125000 : Real) *
          ((1 / (Beta - d)) * Q4 d r * Q4 d s) *
          (1 / G - 1 / (d - G)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hprod hcoef) hTail0
    _ = ((70893 / 125000 : Real) / (Beta - d) *
          (1 / G - 1 / (d - G))) * Q4 d r * Q4 d s := by
      ring


end
end PrimesRestrictedDigits
