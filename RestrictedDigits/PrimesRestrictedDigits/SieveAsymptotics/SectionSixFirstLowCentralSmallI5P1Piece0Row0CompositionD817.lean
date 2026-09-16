import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece0Row0AnalyticD816
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece0Row0FubiniD815
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1TransformedKernelRegularityD809
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixBuchstabFiberIntegrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
/-! # SectionSixFirstLowCentralSmallI5P1Piece0Row0CompositionD817 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-!
# transformed P1 Piece0 Row0 composition helpers

This fixed-delta module ports the pointwise composition slice. It exposes the row-height
bridge, the denominator/q4 product, the local t-fiber majorant, and the Row0
sign/integrability wrappers. It does not assert an outer set-integral cap, a source identity,
or an aggregate P1/I5 estimate.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.12).
-/

def sectionSixFirstLowCentralSmallI5P1D817Row0H (d : Real) : Real :=
  (sectionSixFirstLowCentralSmallI5P1D816Row0C -
    sectionSixFirstLowCentralSmallI5P1D816Row0Beta - d) / 2

def sectionSixFirstLowCentralSmallI5P1D817Kernel
    (z : SectionSixP1AffineT) : Real :=
  sectionSixFirstLowCentralSmallI5P1D816Row0Kernel z

private abbrev d817A : Real :=
  sectionSixFirstLowCentralSmallI5P1D816Row0A
private abbrev d817B : Real :=
  sectionSixFirstLowCentralSmallI5P1D816Row0B
private abbrev d817Beta : Real :=
  sectionSixFirstLowCentralSmallI5P1D816Row0Beta
private abbrev d817Gap : Real :=
  sectionSixFirstLowCentralSmallI5P1D816Row0Gap
private abbrev d817TailC : Real :=
  sectionSixFirstLowCentralSmallI5P1D816Row0TailC
private abbrev d817Q4 :=
  sectionSixFirstLowCentralSmallI5P1D816Row0Q4

theorem sectionSixFirstLowCentralSmallI5P1D817_row0H_eq_D814R
    (d : Real) :
    sectionSixFirstLowCentralSmallI5P1D817Row0H d =
      sectionSixFirstLowCentralSmallI5P1D814P0Row0R d := by
  unfold sectionSixFirstLowCentralSmallI5P1D817Row0H
    sectionSixFirstLowCentralSmallI5P1D814P0Row0R
  norm_num [sectionSixFirstLowCentralSmallI5P1D816Row0C,
    sectionSixFirstLowCentralSmallI5P1D816Row0Beta]

theorem sectionSixFirstLowCentralSmallI5P1D817_endpoint_identifications :
    sectionSixFirstLowCentralSmallI5P1D814P0Row0A =
        sectionSixFirstLowCentralSmallI5P1D816Row0A ∧
      sectionSixFirstLowCentralSmallI5P1D814P0Row0B =
        sectionSixFirstLowCentralSmallI5P1D816Row0B := by
  exact sectionSixFirstLowCentralSmallI5P1D816_endpoint_identifications

theorem sectionSixFirstLowCentralSmallI5P1D817_kernel_formula
    (d r s t : Real) :
    sectionSixFirstLowCentralSmallI5P1D817Kernel (((d, r), s), t) =
      buchstabFunction
          ((1 - sectionSixFirstLowCentralSmallI5P1D816Row0Beta - d - r - s - t) / t) /
        ((sectionSixFirstLowCentralSmallI5P1D816Row0Beta - d) *
          (d + r) * (d + s) * t ^ (2 : Nat)) := by
  simpa [sectionSixFirstLowCentralSmallI5P1D817Kernel] using
    sectionSixFirstLowCentralSmallI5P1D816_kernel_formula d r s t

theorem sectionSixFirstLowCentralSmallI5P1D817_row0_tail_fiber_le
    {d r s : Real}
    (hd0 : sectionSixFirstLowCentralSmallI5P1D816Row0A ≤ d)
    (hd1 : d ≤ sectionSixFirstLowCentralSmallI5P1D816Row0B)
    (hr0 : 0 ≤ r)
    (hr1 : r ≤ sectionSixFirstLowCentralSmallI5P1D817Row0H d)
    (hs0 : 0 ≤ s) (hs1 : s ≤ r) :
    (∫ t in sectionSixFirstLowCentralSmallI5P1D816Row0Gap..
        (d - sectionSixFirstLowCentralSmallI5P1D816Row0Gap),
      sectionSixFirstLowCentralSmallI5P1D817Kernel (((d, r), s), t)) ≤
      sectionSixFirstLowCentralSmallI5P1D816Row0TailC /
          ((sectionSixFirstLowCentralSmallI5P1D816Row0Beta - d) *
            (d + r) * (d + s)) *
        (1 / sectionSixFirstLowCentralSmallI5P1D816Row0Gap -
          1 / (d - sectionSixFirstLowCentralSmallI5P1D816Row0Gap)) := by
  simpa [sectionSixFirstLowCentralSmallI5P1D817Kernel,
    sectionSixFirstLowCentralSmallI5P1D817Row0H] using
    (sectionSixFirstLowCentralSmallI5P1D816_row0_tail_fiber_le
      hd0 hd1 hr0 hr1 hs0 hs1)

theorem sectionSixFirstLowCentralSmallI5P1D817_denominator_q4_product_bound
    {d r s : Real}
    (hd0 : sectionSixFirstLowCentralSmallI5P1D816Row0A ≤ d)
    (hd1 : d ≤ sectionSixFirstLowCentralSmallI5P1D816Row0B)
    (hr0 : 0 ≤ r) (hs0 : 0 ≤ s) :
    (1 / (sectionSixFirstLowCentralSmallI5P1D816Row0Beta - d)) *
        (1 / (d + r)) * (1 / (d + s)) ≤
      (1 / (sectionSixFirstLowCentralSmallI5P1D816Row0Beta -
        sectionSixFirstLowCentralSmallI5P1D816Row0B)) *
        sectionSixFirstLowCentralSmallI5P1D816Row0Q4
          sectionSixFirstLowCentralSmallI5P1D816Row0A r *
        sectionSixFirstLowCentralSmallI5P1D816Row0Q4
          sectionSixFirstLowCentralSmallI5P1D816Row0A s := by
  have ha_pos : 0 < d817A := by norm_num [d817A]
  have hb_pos : 0 < d817Beta - d817B := by
    norm_num [d817Beta, d817B]
  have hd_pos : 0 < d817Beta - d := by linarith
  have hdr_pos : 0 < d + r := by linarith [ha_pos, hd0, hr0]
  have hds_pos : 0 < d + s := by linarith [ha_pos, hd0, hs0]
  have har_pos : 0 < d817A + r := by linarith [ha_pos, hr0]
  have has_pos : 0 < d817A + s := by linarith [ha_pos, hs0]
  have hbd : d817Beta - d817B ≤ d817Beta - d := by linarith
  have hrd : d817A + r ≤ d + r := by linarith
  have hsd : d817A + s ≤ d + s := by linarith
  have hinvbeta : 1 / (d817Beta - d) ≤ 1 / (d817Beta - d817B) :=
    one_div_le_one_div_of_le hb_pos hbd
  have hinvr : 1 / (d + r) ≤ 1 / (d817A + r) :=
    one_div_le_one_div_of_le har_pos hrd
  have hinvs : 1 / (d + s) ≤ 1 / (d817A + s) :=
    one_div_le_one_div_of_le has_pos hsd
  have hq4r : 1 / (d817A + r) ≤ d817Q4 d817A r := by
    simpa [d817Q4] using
      (sectionSixFirstLowCentralSmallI5P1D816_q4_inv_le
        (a := d817A) (x := r) ha_pos hr0)
  have hq4s : 1 / (d817A + s) ≤ d817Q4 d817A s := by
    simpa [d817Q4] using
      (sectionSixFirstLowCentralSmallI5P1D816_q4_inv_le
        (a := d817A) (x := s) ha_pos hs0)
  have hq4r0 : 0 ≤ d817Q4 d817A r :=
    (show 0 ≤ 1 / (d817A + r) by positivity).trans hq4r
  have hq4s0 : 0 ≤ d817Q4 d817A s :=
    (show 0 ≤ 1 / (d817A + s) by positivity).trans hq4s
  calc
    (1 / (d817Beta - d)) * (1 / (d + r)) * (1 / (d + s)) ≤
        (1 / (d817Beta - d817B)) * (1 / (d + r)) *
          (1 / (d + s)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hinvbeta (by positivity)) (by positivity)
    _ ≤ (1 / (d817Beta - d817B)) * d817Q4 d817A r *
        (1 / (d + s)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hinvr.trans hq4r) (by positivity))
          (by positivity)
    _ ≤ (1 / (d817Beta - d817B)) * d817Q4 d817A r *
        d817Q4 d817A s := by
      exact mul_le_mul_of_nonneg_left (hinvs.trans hq4s)
        (mul_nonneg (by positivity) hq4r0)

theorem sectionSixFirstLowCentralSmallI5P1D817_row0_tail_q4_majorant
    {d r s : Real}
    (hd0 : sectionSixFirstLowCentralSmallI5P1D816Row0A ≤ d)
    (hd1 : d ≤ sectionSixFirstLowCentralSmallI5P1D816Row0B)
    (hr0 : 0 ≤ r)
    (hr1 : r ≤ sectionSixFirstLowCentralSmallI5P1D817Row0H d)
    (hs0 : 0 ≤ s) (hs1 : s ≤ r) :
    (∫ t in sectionSixFirstLowCentralSmallI5P1D816Row0Gap..
        (d - sectionSixFirstLowCentralSmallI5P1D816Row0Gap),
      sectionSixFirstLowCentralSmallI5P1D817Kernel (((d, r), s), t)) ≤
      sectionSixFirstLowCentralSmallI5P1D816Row0TailC *
        ((1 / (sectionSixFirstLowCentralSmallI5P1D816Row0Beta -
          sectionSixFirstLowCentralSmallI5P1D816Row0B)) *
          sectionSixFirstLowCentralSmallI5P1D816Row0Q4
            sectionSixFirstLowCentralSmallI5P1D816Row0A r *
          sectionSixFirstLowCentralSmallI5P1D816Row0Q4
            sectionSixFirstLowCentralSmallI5P1D816Row0A s) *
        (1 / sectionSixFirstLowCentralSmallI5P1D816Row0Gap -
          1 / (sectionSixFirstLowCentralSmallI5P1D816Row0B -
            sectionSixFirstLowCentralSmallI5P1D816Row0Gap)) := by
  have htail := sectionSixFirstLowCentralSmallI5P1D817_row0_tail_fiber_le
    hd0 hd1 hr0 hr1 hs0 hs1
  have hprod := sectionSixFirstLowCentralSmallI5P1D817_denominator_q4_product_bound
    hd0 hd1 hr0 hs0
  have ha_pos : 0 < d817A := by norm_num [d817A]
  have hq4r : 1 / (d817A + r) ≤ d817Q4 d817A r := by
    simpa [d817Q4] using
      (sectionSixFirstLowCentralSmallI5P1D816_q4_inv_le
        (a := d817A) (x := r) ha_pos hr0)
  have hq4s : 1 / (d817A + s) ≤ d817Q4 d817A s := by
    simpa [d817Q4] using
      (sectionSixFirstLowCentralSmallI5P1D816_q4_inv_le
        (a := d817A) (x := s) ha_pos hs0)
  have hq4r0 : 0 ≤ d817Q4 d817A r :=
    (show 0 ≤ 1 / (d817A + r) by positivity).trans hq4r
  have hq4s0 : 0 ≤ d817Q4 d817A s :=
    (show 0 ≤ 1 / (d817A + s) by positivity).trans hq4s
  have hgap : 0 < d817Gap := by norm_num [d817Gap]
  have hden : 0 < d817Beta - d := by
    have : 0 < d817Beta - d817B := by norm_num [d817Beta, d817B]
    linarith
  have hdg : 0 < d - d817Gap := by
    have h := (show d817Gap ≤ d - d817Gap by
      norm_num [d817A, d817Gap] at hd0 ⊢
      linarith)
    exact lt_of_lt_of_le hgap h
  have hbg : 0 < d817B - d817Gap := by norm_num [d817B, d817Gap]
  have hprim : 1 / d817Gap - 1 / (d - d817Gap) ≤
      1 / d817Gap - 1 / (d817B - d817Gap) := by
    have hcmp : d - d817Gap ≤ d817B - d817Gap := by linarith
    have hi := one_div_le_one_div_of_le hdg hcmp
    exact sub_le_sub_left hi _
  have hGh : d817Gap ≤ d - d817Gap := by
    norm_num [d817A, d817Gap] at hd0 ⊢
    linarith
  have hprim0 : 0 ≤ 1 / d817Gap - 1 / (d - d817Gap) := by
    have hi := one_div_le_one_div_of_le hgap hGh
    linarith
  have hleft :
      d817TailC / ((d817Beta - d) * (d + r) * (d + s)) *
          (1 / d817Gap - 1 / (d - d817Gap)) =
        d817TailC * ((1 / (d817Beta - d)) * (1 / (d + r)) *
          (1 / (d + s))) * (1 / d817Gap - 1 / (d - d817Gap)) := by
    field_simp [ne_of_gt hden, ne_of_gt (show 0 < d + r by linarith),
      ne_of_gt (show 0 < d + s by linarith)]
  calc
    (∫ t in d817Gap..(d - d817Gap),
        sectionSixFirstLowCentralSmallI5P1D817Kernel (((d, r), s), t)) ≤
      d817TailC / ((d817Beta - d) * (d + r) * (d + s)) *
        (1 / d817Gap - 1 / (d - d817Gap)) := htail
    _ = d817TailC * ((1 / (d817Beta - d)) * (1 / (d + r)) *
          (1 / (d + s))) * (1 / d817Gap - 1 / (d - d817Gap)) := hleft
    _ ≤ d817TailC * ((1 / (d817Beta - d817B)) * d817Q4 d817A r *
          d817Q4 d817A s) * (1 / d817Gap - 1 / (d - d817Gap)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hprod (by positivity)) hprim0
    _ ≤ d817TailC * ((1 / (d817Beta - d817B)) * d817Q4 d817A r *
          d817Q4 d817A s) * (1 / d817Gap - 1 / (d817B - d817Gap)) := by
      have hcoef : 0 ≤ d817TailC *
          ((1 / (d817Beta - d817B)) * d817Q4 d817A r * d817Q4 d817A s) := by
        have hqprod : 0 ≤ (1 / (d817Beta - d817B)) *
            d817Q4 d817A r * d817Q4 d817A s :=
          mul_nonneg (mul_nonneg (by positivity) hq4r0) hq4s0
        exact mul_nonneg (by positivity) hqprod
      exact mul_le_mul_of_nonneg_left hprim hcoef

theorem sectionSixFirstLowCentralSmallI5P1D817_row0_kernel_nonneg
    {z : SectionSixP1AffineT}
    (hz : z ∈ sectionSixFirstLowCentralSmallI5P1D815Row0) :
    0 ≤ sectionSixFirstLowCentralSmallI5P1D817Kernel z := by
  have hp : z ∈ sectionSixFirstLowCentralSmallI5P1D808Piece (0 : Fin 3) := by
    simpa [sectionSixFirstLowCentralSmallI5P1D808Piece] using
      (sectionSixFirstLowCentralSmallI5P1D815_row0_subset_piece0 hz)
  change 0 ≤ sectionSixFirstLowCentralSmallI5P1D809Kernel z
  exact sectionSixFirstLowCentralSmallI5P1D809_kernel_nonneg_piece
    (0 : Fin 3) hp

theorem sectionSixFirstLowCentralSmallI5P1D817_row0_kernel_integrable :
    IntegrableOn sectionSixFirstLowCentralSmallI5P1D817Kernel
      sectionSixFirstLowCentralSmallI5P1D815Row0
      (volume : Measure SectionSixP1AffineT) := by
  change IntegrableOn sectionSixFirstLowCentralSmallI5P1D816Row0Kernel
      sectionSixFirstLowCentralSmallI5P1D815Row0
      (volume : Measure SectionSixP1AffineT)
  exact sectionSixFirstLowCentralSmallI5P1D816_row0_kernel_integrable

theorem sectionSixFirstLowCentralSmallI5P1D817_row0_endpoint_order :
    sectionSixFirstLowCentralSmallI5P1D816Row0A ≤
      sectionSixFirstLowCentralSmallI5P1D816Row0B := by
  norm_num [sectionSixFirstLowCentralSmallI5P1D816Row0A,
    sectionSixFirstLowCentralSmallI5P1D816Row0B]

end

end PrimesRestrictedDigits
