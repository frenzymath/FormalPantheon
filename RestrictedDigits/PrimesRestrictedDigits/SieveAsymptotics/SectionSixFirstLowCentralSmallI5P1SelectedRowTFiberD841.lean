import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1SelectedRowBridgeD838
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-! # SectionSixFirstLowCentralSmallI5P1SelectedRowTFiberD841 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits
noncomputable section

private abbrev A : Real :=
  sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower
private abbrev B : Real :=
  sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper
private abbrev G : Real :=
  sectionSixFirstLowCentralSmallI5P1D807Gap
private abbrev Beta : Real :=
  sectionSixFirstLowCentralSmallI5P1D807Beta
private abbrev Ds : Real :=
  sectionSixFirstLowCentralSmallI5P1D807Ds
private abbrev D1 : Real :=
  sectionSixFirstLowCentralSmallI5P1D807D1
private abbrev L : Real → Real :=
  sectionSixFirstLowCentralSmallI5P1D807L
private abbrev H : Real → Real :=
  sectionSixFirstLowCentralSmallI5P1D807H
private abbrev Q4 : Real → Real → Real :=
  sectionSixFirstLowCentralSmallI5P1D816Row0Q4
private abbrev Factor : Real :=
  sectionSixFirstLowCentralSmallI5P1D838P1Row1Factor

theorem sectionSixFirstLowCentralSmallI5P1D841_p1Row1_tfiber_le_q4
    {d r s : Real}
    (hd : d ∈ Set.Icc
      sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower
      sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper)
    (hr : r ∈ Set.Icc 0
      (sectionSixFirstLowCentralSmallI5P1D807H d))
    (hs : s ∈ Set.Icc 0
      (min r (sectionSixFirstLowCentralSmallI5P1D807L d - r))) :
    (∫ t in sectionSixFirstLowCentralSmallI5P1D807Gap..
      (d - sectionSixFirstLowCentralSmallI5P1D807Gap),
      sectionSixFirstLowCentralSmallI5P1D809Kernel (((d, r), s), t)) ≤
      sectionSixFirstLowCentralSmallI5P1D838P1Row1Factor *
        sectionSixFirstLowCentralSmallI5P1D816Row0Q4
          sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower r *
        sectionSixFirstLowCentralSmallI5P1D816Row0Q4
          sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower s := by
  have hd' := sectionSixFirstLowCentralSmallI5P1D838_p1Row1_slab_subset_piece_interval hd
  have hd1 : d ≤ D1 := by
    exact hd'.2.trans sectionSixFirstLowCentralSmallI5P1D822_dr_le_d1
  have hrs : r + s ≤ L d := by
    have hsL := (le_min_iff.mp hs.2).2
    linarith [hr.1, hsL]
  have hbase := sectionSixFirstLowCentralSmallI5P1D822_kernel_fiber_le
    hd'.1 hd1 hr.1 hs.1 hrs
  have hbase' :
      (∫ t in G..(d - G),
        sectionSixFirstLowCentralSmallI5P1D809Kernel (((d, r), s), t)) ≤
        (70893 / 125000 : Real) /
          ((Beta - d) * (d + r) * (d + s)) *
          (1 / G - 1 / (d - G)) := by
    calc
      (∫ t in G..(d - G),
        sectionSixFirstLowCentralSmallI5P1D809Kernel (((d, r), s), t)) =
          ∫ t in G..(d - G),
            sectionSixFirstLowCentralSmallI5P1D817Kernel (((d, r), s), t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        unfold sectionSixFirstLowCentralSmallI5P1D809Kernel
          sectionSixFirstLowCentralSmallQuadrupleKernel
        simp only [sectionSixP1SharpPhiD806, Prod.fst_add, Prod.snd_add, zero_add]
        convert (sectionSixFirstLowCentralSmallI5P1D817_kernel_formula d r s t).symm using 1
        norm_num [sectionSixFirstLowCentralSmallI5P1D816Row0Beta,
          sectionSixFirstLowCentralSmallI5P1D807Beta, sectionSixThetaTwo,
          sectionSixFirstLowCentralSmallI5P1D807Delta]
        ring
      _ ≤ _ := by
        simpa [Beta, G, pow_two] using hbase
  have hApos : 0 < A := by
    norm_num [A, sectionSixFirstLowCentralSmallI5P1D838P1Row1Lower]
  have hBbeta : 0 < Beta - B := by
    rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
      ⟨_, hbeta, _, _, _, _, _⟩
    change 0 < sectionSixFirstLowCentralSmallI5P1D807Beta -
      sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper
    rw [hbeta]
    norm_num [B, sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper]
  have hbetaD : 0 < Beta - d := by linarith [hBbeta, hd.2]
  have hDplusR : 0 < d + r := by linarith [hApos, hd.1, hr.1]
  have hDplusS : 0 < d + s := by linarith [hApos, hd.1, hs.1]
  have hAplusR : 0 < A + r := by linarith [hApos, hr.1]
  have hAplusS : 0 < A + s := by linarith [hApos, hs.1]
  have hInvBeta : 1 / (Beta - d) ≤ 1 / (Beta - B) := by
    have hdb : d ≤ B := hd.2
    exact one_div_le_one_div_of_le hBbeta (by linarith [hdb])
  have hInvR : 1 / (d + r) ≤ 1 / (A + r) := by
    have had : A ≤ d := hd.1
    exact one_div_le_one_div_of_le hAplusR (by linarith [had])
  have hInvS : 1 / (d + s) ≤ 1 / (A + s) := by
    have had : A ≤ d := hd.1
    exact one_div_le_one_div_of_le hAplusS (by linarith [had])
  have hQ4R : 1 / (A + r) ≤ Q4 A r := by
    simpa [Q4] using
      (sectionSixFirstLowCentralSmallI5P1D816_q4_inv_le hApos hr.1)
  have hQ4S : 1 / (A + s) ≤ Q4 A s := by
    simpa [Q4] using
      (sectionSixFirstLowCentralSmallI5P1D816_q4_inv_le hApos hs.1)
  have hQ4R0 : 0 ≤ Q4 A r :=
    (show 0 ≤ 1 / (A + r) by positivity).trans hQ4R
  have hQ4S0 : 0 ≤ Q4 A s :=
    (show 0 ≤ 1 / (A + s) by positivity).trans hQ4S
  have hprod :
      (1 / (Beta - d)) * (1 / (d + r)) * (1 / (d + s)) ≤
        (1 / (Beta - B)) * Q4 A r * Q4 A s := by
    calc
      (1 / (Beta - d)) * (1 / (d + r)) * (1 / (d + s)) ≤
          (1 / (Beta - B)) * (1 / (d + r)) * (1 / (d + s)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hInvBeta (by positivity)) (by positivity)
      _ ≤ (1 / (Beta - B)) * Q4 A r * (1 / (d + s)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hInvR.trans hQ4R) (by positivity)) (by positivity)
      _ ≤ (1 / (Beta - B)) * Q4 A r * Q4 A s := by
        exact mul_le_mul_of_nonneg_left (hInvS.trans hQ4S)
          (mul_nonneg (by positivity) hQ4R0)
  have hGpos : 0 < G := by
    rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
      ⟨_, _, hgap, _, _, _, _⟩
    change 0 < sectionSixFirstLowCentralSmallI5P1D807Gap
    rw [hgap]
    norm_num
  have h2G : 2 * G ≤ Ds := by
    rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
      ⟨_, _, hgap, _, hds, _, _⟩
    change 2 * sectionSixFirstLowCentralSmallI5P1D807Gap ≤
      sectionSixFirstLowCentralSmallI5P1D807Ds
    rw [hgap, hds]
    norm_num
  have hGle : G ≤ d - G := by linarith [h2G, hd'.1]
  have hDGpos : 0 < d - G := lt_of_lt_of_le hGpos hGle
  have hBGpos : 0 < B - G := by
    change 0 < sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper -
      sectionSixFirstLowCentralSmallI5P1D807Gap
    rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
      ⟨_, _, hgap, _, _, _, _⟩
    rw [hgap]
    norm_num [sectionSixFirstLowCentralSmallI5P1D838P1Row1Upper]
  have hTail :
      1 / G - 1 / (d - G) ≤ 1 / G - 1 / (B - G) := by
    have hcmp : d - G ≤ B - G := by linarith [hd.2]
    have hi := one_div_le_one_div_of_le hDGpos hcmp
    exact sub_le_sub_left hi _
  have hTail0 : 0 ≤ 1 / G - 1 / (d - G) := by
    have hi := one_div_le_one_div_of_le hGpos hGle
    linarith
  have hleft :
      (70893 / 125000 : Real) /
          ((Beta - d) * (d + r) * (d + s)) *
          (1 / G - 1 / (d - G)) =
        (70893 / 125000 : Real) *
          ((1 / (Beta - d)) * (1 / (d + r)) * (1 / (d + s))) *
          (1 / G - 1 / (d - G)) := by
    field_simp [ne_of_gt hbetaD, ne_of_gt hDplusR, ne_of_gt hDplusS]
  have hcoef : 0 ≤ (70893 / 125000 : Real) := by norm_num
  have htarget0 : 0 ≤
      (70893 / 125000 : Real) *
        ((1 / (Beta - B)) * Q4 A r * Q4 A s) := by
    positivity
  calc
    (∫ t in G..(d - G),
        sectionSixFirstLowCentralSmallI5P1D809Kernel (((d, r), s), t)) ≤
        (70893 / 125000 : Real) /
          ((Beta - d) * (d + r) * (d + s)) *
          (1 / G - 1 / (d - G)) := hbase'
    _ = (70893 / 125000 : Real) *
          ((1 / (Beta - d)) * (1 / (d + r)) * (1 / (d + s))) *
          (1 / G - 1 / (d - G)) := hleft
    _ ≤ (70893 / 125000 : Real) *
          ((1 / (Beta - B)) * Q4 A r * Q4 A s) *
          (1 / G - 1 / (d - G)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hprod hcoef) hTail0
    _ ≤ (70893 / 125000 : Real) *
          ((1 / (Beta - B)) * Q4 A r * Q4 A s) *
          (1 / G - 1 / (B - G)) := by
      exact mul_le_mul_of_nonneg_left hTail htarget0
    _ = Factor * Q4 A r * Q4 A s := by
      unfold Factor sectionSixFirstLowCentralSmallI5P1D838P1Row1Factor
      ring


end
end PrimesRestrictedDigits
