import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1RowEndpointOrderD850
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece12MiddleOrTailEnvelopeD822
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece0Row0CompositionD817
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1TransformedKernelRegularityD809
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# parameterized Piece1 t-fiber envelope

This module exports only the two alias-free wrapper theorems. All abbreviations and arithmetic
comparison lemmas below are private.
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits
noncomputable section

private abbrev G : Real :=
  sectionSixFirstLowCentralSmallI5P1D807Gap
private abbrev Beta : Real :=
  sectionSixFirstLowCentralSmallI5P1D807Beta
private abbrev Ds : Real :=
  sectionSixFirstLowCentralSmallI5P1D807Ds
private abbrev D1 : Real :=
  sectionSixFirstLowCentralSmallI5P1D807D1
private abbrev H : Real → Real :=
  sectionSixFirstLowCentralSmallI5P1D807H
private abbrev L : Real → Real :=
  sectionSixFirstLowCentralSmallI5P1D807L
private abbrev Q4 : Real → Real → Real :=
  sectionSixFirstLowCentralSmallI5P1D816Row0Q4

private def d851Factor (i : Fin 256) : Real :=
  (70893 / 125000 : Real) /
      (Beta - sectionSixFirstLowCentralSmallI5P1D849RowUpper i) *
    (1 / G - 1 /
      (sectionSixFirstLowCentralSmallI5P1D849RowUpper i - G))

private theorem d851_row_mem_interval {i : Fin 256} {d : Real}
    (hd : d ∈ sectionSixFirstLowCentralSmallI5P1D846P1RowSlab i) :
    d ∈ Set.Icc Ds
      sectionSixFirstLowCentralSmallI5P1D807Dr := by
  have hdi : d ∈ Set.Icc
      (sectionSixFirstLowCentralSmallI5P1D849RowLower i)
      (sectionSixFirstLowCentralSmallI5P1D849RowUpper i) := by
    rw [← sectionSixFirstLowCentralSmallI5P1D849_rowSlab_eq_Icc i]
    exact hd
  exact ⟨(sectionSixFirstLowCentralSmallI5P1D850_ds_le_row_lower i).trans hdi.1,
    hdi.2.trans (sectionSixFirstLowCentralSmallI5P1D850_row_upper_le_dr i)⟩

private theorem d851_lower_pos (i : Fin 256) :
    0 < sectionSixFirstLowCentralSmallI5P1D849RowLower i := by
  have hds : 0 < Ds := by
    rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
      ⟨_, _, _, _, h, _, _⟩
    change 0 < sectionSixFirstLowCentralSmallI5P1D807Ds
    rw [h]
    norm_num
  exact lt_of_lt_of_le hds
    (sectionSixFirstLowCentralSmallI5P1D850_ds_le_row_lower i)

private theorem d851_beta_upper_pos (i : Fin 256) :
    0 < Beta - sectionSixFirstLowCentralSmallI5P1D849RowUpper i := by
  have hD1beta : D1 < Beta := by
    rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
      ⟨_, hbeta, _, _, _, _, hd1⟩
    change sectionSixFirstLowCentralSmallI5P1D807D1 <
      sectionSixFirstLowCentralSmallI5P1D807Beta
    rw [hd1, hbeta]
    norm_num
  have hu : sectionSixFirstLowCentralSmallI5P1D849RowUpper i ≤ D1 :=
    (sectionSixFirstLowCentralSmallI5P1D850_row_upper_le_dr i).trans
      sectionSixFirstLowCentralSmallI5P1D822_dr_le_d1
  linarith

private theorem d851_denominator_q4_product_bound
    {i : Fin 256} {d r s : Real}
    (hd : d ∈ Set.Icc
      (sectionSixFirstLowCentralSmallI5P1D849RowLower i)
      (sectionSixFirstLowCentralSmallI5P1D849RowUpper i))
    (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (1 / (Beta - d)) * (1 / (d + r)) * (1 / (d + s)) ≤
      (1 / (Beta - sectionSixFirstLowCentralSmallI5P1D849RowUpper i)) *
        Q4 (sectionSixFirstLowCentralSmallI5P1D849RowLower i) r *
        Q4 (sectionSixFirstLowCentralSmallI5P1D849RowLower i) s := by
  let A : Real := sectionSixFirstLowCentralSmallI5P1D849RowLower i
  let B : Real := sectionSixFirstLowCentralSmallI5P1D849RowUpper i
  have hApos : 0 < A := by
    exact d851_lower_pos i
  have hBbeta : 0 < Beta - B := by
    exact d851_beta_upper_pos i
  have hbetaD : 0 < Beta - d := by linarith [hd.2]
  have hDplusR : 0 < d + r := by linarith [hApos, hd.1, hr]
  have hDplusS : 0 < d + s := by linarith [hApos, hd.1, hs]
  have hAplusR : 0 < A + r := by linarith [hApos, hr]
  have hAplusS : 0 < A + s := by linarith [hApos, hs]
  have hInvBeta : 1 / (Beta - d) ≤ 1 / (Beta - B) := by
    exact one_div_le_one_div_of_le hBbeta (by linarith [hd.2])
  have hInvR : 1 / (d + r) ≤ 1 / (A + r) := by
    exact one_div_le_one_div_of_le hAplusR (by linarith [hd.1])
  have hInvS : 1 / (d + s) ≤ 1 / (A + s) := by
    exact one_div_le_one_div_of_le hAplusS (by linarith [hd.1])
  have hQ4R : 1 / (A + r) ≤ Q4 A r := by
    simpa [A, Q4] using
      (sectionSixFirstLowCentralSmallI5P1D816_q4_inv_le
        (a := A) (x := r) hApos hr)
  have hQ4S : 1 / (A + s) ≤ Q4 A s := by
    simpa [A, Q4] using
      (sectionSixFirstLowCentralSmallI5P1D816_q4_inv_le
        (a := A) (x := s) hApos hs)
  have hQ4R0 : 0 ≤ Q4 A r :=
    (show 0 ≤ 1 / (A + r) by positivity).trans hQ4R
  have hQ4S0 : 0 ≤ Q4 A s :=
    (show 0 ≤ 1 / (A + s) by positivity).trans hQ4S
  calc
    (1 / (Beta - d)) * (1 / (d + r)) * (1 / (d + s)) ≤
        (1 / (Beta - B)) * (1 / (d + r)) * (1 / (d + s)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hInvBeta (by positivity)) (by positivity)
    _ ≤ (1 / (Beta - B)) * Q4 A r * (1 / (d + s)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hInvR.trans hQ4R) (by positivity))
          (by positivity)
    _ ≤ (1 / (Beta - B)) * Q4 A r * Q4 A s := by
      exact mul_le_mul_of_nonneg_left (hInvS.trans hQ4S)
        (mul_nonneg (by positivity) hQ4R0)

private theorem sectionSixFirstLowCentralSmallI5P1D851_generic_tfiber_le_q4
    {i : Fin 256} {d r s : Real}
    (hd : d ∈ sectionSixFirstLowCentralSmallI5P1D846P1RowSlab i)
    (hr : r ∈ Set.Icc 0 (H d))
    (hs : s ∈ Set.Icc 0 (min r (L d - r))) :
    (∫ t in G..(d - G),
      sectionSixFirstLowCentralSmallI5P1D817Kernel (((d, r), s), t)) ≤
      d851Factor i * Q4
          (sectionSixFirstLowCentralSmallI5P1D849RowLower i) r *
        Q4 (sectionSixFirstLowCentralSmallI5P1D849RowLower i) s := by
  have hdi : d ∈ Set.Icc
      (sectionSixFirstLowCentralSmallI5P1D849RowLower i)
      (sectionSixFirstLowCentralSmallI5P1D849RowUpper i) := by
    rw [← sectionSixFirstLowCentralSmallI5P1D849_rowSlab_eq_Icc i]
    exact hd
  have hpiece := d851_row_mem_interval hd
  have hd1 : d ≤ D1 := hpiece.2.trans
    sectionSixFirstLowCentralSmallI5P1D822_dr_le_d1
  have hrs : r + s ≤ L d := by
    have hsL := (le_min_iff.mp hs.2).2
    linarith [hr.1, hsL]
  have hbase := sectionSixFirstLowCentralSmallI5P1D822_kernel_fiber_le
    hpiece.1 hd1 hr.1 hs.1 hrs
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
  have hGle : G ≤ d - G := by linarith [h2G, hpiece.1]
  have hDGpos : 0 < d - G := lt_of_lt_of_le hGpos hGle
  have hupperG : G ≤
      sectionSixFirstLowCentralSmallI5P1D849RowUpper i - G := by
    have hdsupper : Ds ≤
        sectionSixFirstLowCentralSmallI5P1D849RowUpper i :=
      (sectionSixFirstLowCentralSmallI5P1D850_ds_le_row_lower i).trans
        (sectionSixFirstLowCentralSmallI5P1D850_row_lower_le_upper i)
    linarith [h2G,
      hdsupper]
  have hBGpos : 0 <
      sectionSixFirstLowCentralSmallI5P1D849RowUpper i - G :=
    lt_of_lt_of_le hGpos hupperG
  have hTail : 1 / G - 1 / (d - G) ≤
      1 / G - 1 /
        (sectionSixFirstLowCentralSmallI5P1D849RowUpper i - G) := by
    have hcmp : d - G ≤
        sectionSixFirstLowCentralSmallI5P1D849RowUpper i - G :=
      by linarith [hdi.2]
    exact sub_le_sub_left (one_div_le_one_div_of_le hDGpos hcmp) _
  have hTail0 : 0 ≤ 1 / G - 1 / (d - G) := by
    linarith [one_div_le_one_div_of_le hGpos hGle]
  have hleft :
      (70893 / 125000 : Real) /
          ((Beta - d) * (d + r) * (d + s)) *
          (1 / G - 1 / (d - G)) =
        (70893 / 125000 : Real) *
          ((1 / (Beta - d)) * (1 / (d + r)) * (1 / (d + s))) *
          (1 / G - 1 / (d - G)) := by
    field_simp [ne_of_gt (show 0 < Beta - d by
        linarith [d851_beta_upper_pos i, hdi.2]),
      ne_of_gt (show 0 < d + r by linarith [hdi.1, hr.1]),
      ne_of_gt (show 0 < d + s by linarith [hdi.1, hs.1])]
  have hprod := d851_denominator_q4_product_bound hdi hr.1 hs.1
  have hcoef : 0 ≤ (70893 / 125000 : Real) := by norm_num
  have hApos : 0 <
      sectionSixFirstLowCentralSmallI5P1D849RowLower i :=
    d851_lower_pos i
  have hQ4R : 0 ≤ Q4
      (sectionSixFirstLowCentralSmallI5P1D849RowLower i) r := by
    have h := sectionSixFirstLowCentralSmallI5P1D816_q4_inv_le
      (a := sectionSixFirstLowCentralSmallI5P1D849RowLower i) (x := r)
      hApos hr.1
    have hAr : 0 ≤ sectionSixFirstLowCentralSmallI5P1D849RowLower i + r :=
      add_nonneg (le_of_lt hApos) hr.1
    exact (one_div_nonneg.mpr hAr).trans h
  have hQ4S : 0 ≤ Q4
      (sectionSixFirstLowCentralSmallI5P1D849RowLower i) s := by
    have h := sectionSixFirstLowCentralSmallI5P1D816_q4_inv_le
      (a := sectionSixFirstLowCentralSmallI5P1D849RowLower i) (x := s)
      hApos hs.1
    have hAs : 0 ≤ sectionSixFirstLowCentralSmallI5P1D849RowLower i + s :=
      add_nonneg (le_of_lt hApos) hs.1
    exact (one_div_nonneg.mpr hAs).trans h
  have hBetaU : 0 < Beta -
      sectionSixFirstLowCentralSmallI5P1D849RowUpper i :=
    d851_beta_upper_pos i
  have htarget0 : 0 ≤
      (70893 / 125000 : Real) *
        ((1 / (Beta - sectionSixFirstLowCentralSmallI5P1D849RowUpper i)) *
          Q4 (sectionSixFirstLowCentralSmallI5P1D849RowLower i) r *
          Q4 (sectionSixFirstLowCentralSmallI5P1D849RowLower i) s) := by
    have hInvU : 0 ≤ 1 /
        (Beta - sectionSixFirstLowCentralSmallI5P1D849RowUpper i) :=
      one_div_nonneg.mpr hBetaU.le
    exact mul_nonneg hcoef
      (mul_nonneg (mul_nonneg hInvU hQ4R) hQ4S)
  have hbase' :
      (∫ t in G..(d - G),
        sectionSixFirstLowCentralSmallI5P1D817Kernel (((d, r), s), t)) ≤
        (70893 / 125000 : Real) /
          ((Beta - d) * (d + r) * (d + s)) *
          (1 / G - 1 / (d - G)) := by
    simpa [Beta, G, pow_two] using hbase
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
          ((1 / (Beta - sectionSixFirstLowCentralSmallI5P1D849RowUpper i)) *
            Q4 (sectionSixFirstLowCentralSmallI5P1D849RowLower i) r *
            Q4 (sectionSixFirstLowCentralSmallI5P1D849RowLower i) s) *
          (1 / G - 1 / (d - G)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hprod hcoef) hTail0
    _ ≤ (70893 / 125000 : Real) *
          ((1 / (Beta - sectionSixFirstLowCentralSmallI5P1D849RowUpper i)) *
            Q4 (sectionSixFirstLowCentralSmallI5P1D849RowLower i) r *
            Q4 (sectionSixFirstLowCentralSmallI5P1D849RowLower i) s) *
          (1 / G - 1 /
            (sectionSixFirstLowCentralSmallI5P1D849RowUpper i - G)) := by
      exact mul_le_mul_of_nonneg_left hTail htarget0
    _ = d851Factor i * Q4
          (sectionSixFirstLowCentralSmallI5P1D849RowLower i) r *
        Q4 (sectionSixFirstLowCentralSmallI5P1D849RowLower i) s := by
      unfold d851Factor
      ring

private theorem sectionSixFirstLowCentralSmallI5P1D851_generic_tfiber_le_q4_d809
    {i : Fin 256} {d r s : Real}
    (hd : d ∈ sectionSixFirstLowCentralSmallI5P1D846P1RowSlab i)
    (hr : r ∈ Set.Icc 0 (H d))
    (hs : s ∈ Set.Icc 0 (min r (L d - r))) :
    (∫ t in G..(d - G),
      sectionSixFirstLowCentralSmallI5P1D809Kernel (((d, r), s), t)) ≤
      d851Factor i * Q4
          (sectionSixFirstLowCentralSmallI5P1D849RowLower i) r *
        Q4 (sectionSixFirstLowCentralSmallI5P1D849RowLower i) s := by
  have heq :
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
  rw [heq]
  exact sectionSixFirstLowCentralSmallI5P1D851_generic_tfiber_le_q4 hd hr hs


theorem sectionSixFirstLowCentralSmallI5P1D851_generic_tfiber_le_q4_public
    {i : Fin 256} {d r s : Real}
    (hd : d ∈ sectionSixFirstLowCentralSmallI5P1D846P1RowSlab i)
    (hr : r ∈ Set.Icc 0 (sectionSixFirstLowCentralSmallI5P1D807H d))
    (hs : s ∈ Set.Icc 0
      (min r (sectionSixFirstLowCentralSmallI5P1D807L d - r))) :
    (∫ t in sectionSixFirstLowCentralSmallI5P1D807Gap..
        (d - sectionSixFirstLowCentralSmallI5P1D807Gap),
      sectionSixFirstLowCentralSmallI5P1D817Kernel (((d, r), s), t)) ≤
      ((70893 / 125000 : Real) /
        (sectionSixFirstLowCentralSmallI5P1D807Beta -
          sectionSixFirstLowCentralSmallI5P1D849RowUpper i) *
        (1 / sectionSixFirstLowCentralSmallI5P1D807Gap -
          1 / (sectionSixFirstLowCentralSmallI5P1D849RowUpper i -
            sectionSixFirstLowCentralSmallI5P1D807Gap))) *
        sectionSixFirstLowCentralSmallI5P1D816Row0Q4
          (sectionSixFirstLowCentralSmallI5P1D849RowLower i) r *
        sectionSixFirstLowCentralSmallI5P1D816Row0Q4
          (sectionSixFirstLowCentralSmallI5P1D849RowLower i) s := by
  simpa [d851Factor, G, Beta, Q4, H, L] using
    (sectionSixFirstLowCentralSmallI5P1D851_generic_tfiber_le_q4 hd hr hs)

theorem sectionSixFirstLowCentralSmallI5P1D851_generic_tfiber_le_q4_d809_public
    {i : Fin 256} {d r s : Real}
    (hd : d ∈ sectionSixFirstLowCentralSmallI5P1D846P1RowSlab i)
    (hr : r ∈ Set.Icc 0 (sectionSixFirstLowCentralSmallI5P1D807H d))
    (hs : s ∈ Set.Icc 0
      (min r (sectionSixFirstLowCentralSmallI5P1D807L d - r))) :
    (∫ t in sectionSixFirstLowCentralSmallI5P1D807Gap..
        (d - sectionSixFirstLowCentralSmallI5P1D807Gap),
      sectionSixFirstLowCentralSmallI5P1D809Kernel (((d, r), s), t)) ≤
      ((70893 / 125000 : Real) /
        (sectionSixFirstLowCentralSmallI5P1D807Beta -
          sectionSixFirstLowCentralSmallI5P1D849RowUpper i) *
        (1 / sectionSixFirstLowCentralSmallI5P1D807Gap -
          1 / (sectionSixFirstLowCentralSmallI5P1D849RowUpper i -
            sectionSixFirstLowCentralSmallI5P1D807Gap))) *
        sectionSixFirstLowCentralSmallI5P1D816Row0Q4
          (sectionSixFirstLowCentralSmallI5P1D849RowLower i) r *
        sectionSixFirstLowCentralSmallI5P1D816Row0Q4
          (sectionSixFirstLowCentralSmallI5P1D849RowLower i) s := by
  simpa [d851Factor, G, Beta, Q4, H, L] using
    (sectionSixFirstLowCentralSmallI5P1D851_generic_tfiber_le_q4_d809 hd hr hs)


end
end PrimesRestrictedDigits
