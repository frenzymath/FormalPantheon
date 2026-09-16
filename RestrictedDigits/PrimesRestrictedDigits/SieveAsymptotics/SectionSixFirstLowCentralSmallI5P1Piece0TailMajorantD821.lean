import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece0ScalarD821
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixBuchstabFiberIntegrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
/-! # SectionSixFirstLowCentralSmallI5P1Piece0TailMajorantD821 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits
noncomputable section

/-!
# full transformed Piece0 t-fiber majorant

This is the local full-Piece0 tail/q4 estimate used by the set-integral module. It makes no
measure, Fubini, source, aggregate, or cap claim.
-/

theorem sectionSixFirstLowCentralSmallI5P1D821_piece0_tail_q4_majorant
    {d r s : Real}
    (hd0 : (16249 / 125000 : Real) ≤ d)
    (hds : d ≤ (29 / 200 : Real))
    (hr0 : 0 ≤ r)
    (hr1 : r ≤ ((16 / 25 : Real) - 212499 / 500000 - d) / 2)
    (hs0 : 0 ≤ s) (hs1 : s ≤ r) :
    (∫ t in (16249 / 250000 : Real)..(d - 16249 / 250000),
      sectionSixFirstLowCentralSmallI5P1D809Kernel (((d, r), s), t)) ≤
      sectionSixFirstLowCentralSmallI5P1D821Majorant d r s := by
  have hD0pos : 0 < (16249 / 125000 : Real) := by norm_num
  have hGapPos : 0 < (16249 / 250000 : Real) := by norm_num
  have hu : 0 < (212499 / 500000 : Real) - d := by linarith
  have hv : 0 < d + r := by linarith
  have hw : 0 < d + s := by linarith
  have hGh : (16249 / 250000 : Real) ≤ d - 16249 / 250000 := by
    norm_num at hd0 ⊢
    linarith
  have hrs : r + s ≤ (16 / 25 : Real) - 212499 / 500000 - d := by
    norm_num at hr1 ⊢
    linarith
  have htail : 4 * (d - 16249 / 250000 : Real) ≤
      1 - 212499 / 500000 - d - r - s := by
    have hleft : 4 * (d - 16249 / 250000 : Real) ≤
        4 * ((29 / 200 : Real) - 16249 / 250000) := by gcongr
    have hright : 1 - 212499 / 500000 - d - r - s ≥ 1 - (16 / 25 : Real) := by
      linarith
    norm_num at hleft hright ⊢
    linarith
  have htail' := integral_sectionSixBuchstabTailBranch_le
    (u := (212499 / 500000 : Real) - d) (v := d + r) (w := d + s)
    (B := 1 - 212499 / 500000 - d - r - s)
    (l := (16249 / 250000 : Real)) (h := d - 16249 / 250000)
    hu hv hw hGapPos hGh htail
  have hbase := sectionSixFirstLowCentralSmallI5P1D816_q4_inv_le
    (a := (16249 / 125000 : Real)) (x := r) hD0pos hr0
  have hbaseS := sectionSixFirstLowCentralSmallI5P1D816_q4_inv_le
    (a := (16249 / 125000 : Real)) (x := s) hD0pos hs0
  have hBetaInv : 1 / ((212499 / 500000 : Real) - d) ≤
      1 / ((212499 / 500000 : Real) - 29 / 200) := by
    apply one_div_le_one_div_of_le
    · linarith
    · linarith
  have hRInv : 1 / (d + r) ≤ 1 / ((16249 / 125000 : Real) + r) := by
    apply one_div_le_one_div_of_le
    · linarith
    · linarith
  have hSInv : 1 / (d + s) ≤ 1 / ((16249 / 125000 : Real) + s) := by
    apply one_div_le_one_div_of_le
    · linarith
    · linarith
  have hprod :
      (1 / ((212499 / 500000 : Real) - d)) * (1 / (d + r)) * (1 / (d + s)) ≤
        (1 / ((212499 / 500000 : Real) - 29 / 200)) *
          sectionSixFirstLowCentralSmallI5P1D816Row0Q4 (16249 / 125000 : Real) r *
            sectionSixFirstLowCentralSmallI5P1D816Row0Q4 (16249 / 125000 : Real) s := by
    have hQr : 0 ≤ sectionSixFirstLowCentralSmallI5P1D816Row0Q4
        (16249 / 125000 : Real) r :=
      (show 0 ≤ 1 / ((16249 / 125000 : Real) + r) by positivity).trans hbase
    have hQs : 0 ≤ sectionSixFirstLowCentralSmallI5P1D816Row0Q4
        (16249 / 125000 : Real) s :=
      (show 0 ≤ 1 / ((16249 / 125000 : Real) + s) by positivity).trans hbaseS
    calc
      (1 / ((212499 / 500000 : Real) - d)) * (1 / (d + r)) * (1 / (d + s)) ≤
          (1 / ((212499 / 500000 : Real) - 29 / 200)) * (1 / (d + r)) *
            (1 / (d + s)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hBetaInv (by positivity)) (by positivity)
      _ ≤ (1 / ((212499 / 500000 : Real) - 29 / 200)) *
          sectionSixFirstLowCentralSmallI5P1D816Row0Q4 (16249 / 125000 : Real) r *
            (1 / (d + s)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hRInv.trans hbase) (by positivity)) (by positivity)
      _ ≤ (1 / ((212499 / 500000 : Real) - 29 / 200)) *
          sectionSixFirstLowCentralSmallI5P1D816Row0Q4 (16249 / 125000 : Real) r *
            sectionSixFirstLowCentralSmallI5P1D816Row0Q4 (16249 / 125000 : Real) s := by
        exact mul_le_mul_of_nonneg_left (hSInv.trans hbaseS)
          (mul_nonneg (by positivity) hQr)
  have hprim : 1 / (16249 / 250000 : Real) - 1 / (d - 16249 / 250000) ≤
      1 / (16249 / 250000 : Real) - 1 / ((29 / 200 : Real) - 16249 / 250000) := by
    have hden0 : 0 < d - 16249 / 250000 := lt_of_lt_of_le hGapPos hGh
    have hle : d - 16249 / 250000 ≤ (29 / 200 : Real) - 16249 / 250000 := by linarith
    exact sub_le_sub_left (one_div_le_one_div_of_le hden0 hle) _
  have hprim0 : 0 ≤ 1 / (16249 / 250000 : Real) - 1 / (d - 16249 / 250000) := by
    exact sub_nonneg.mpr (one_div_le_one_div_of_le hGapPos hGh)
  have hQrGlobal : 0 ≤ sectionSixFirstLowCentralSmallI5P1D816Row0Q4
      (16249 / 125000 : Real) r :=
    (show 0 ≤ 1 / ((16249 / 125000 : Real) + r) by positivity).trans hbase
  have hQsGlobal : 0 ≤ sectionSixFirstLowCentralSmallI5P1D816Row0Q4
      (16249 / 125000 : Real) s :=
    (show 0 ≤ 1 / ((16249 / 125000 : Real) + s) by positivity).trans hbaseS
  calc
    (∫ t in (16249 / 250000 : Real)..(d - 16249 / 250000),
        sectionSixFirstLowCentralSmallI5P1D809Kernel (((d, r), s), t)) =
        ∫ t in (16249 / 250000 : Real)..(d - 16249 / 250000),
          buchstabFunction ((1 - 212499 / 500000 - d - r - s - t) / t) /
            (((212499 / 500000 : Real) - d) * (d + r) * (d + s) * t ^ (2 : Nat)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      simpa [sectionSixFirstLowCentralSmallI5P1D816Row0Kernel] using
        sectionSixFirstLowCentralSmallI5P1D816_kernel_formula d r s t
    _ ≤ (564383 / 1000000 : Real) /
          (((212499 / 500000 : Real) - d) * (d + r) * (d + s)) *
          (1 / (16249 / 250000 : Real) - 1 / (d - 16249 / 250000)) := by
      simpa [div_eq_mul_inv, mul_assoc] using htail'
    _ = (564383 / 1000000 : Real) *
        ((1 / ((212499 / 500000 : Real) - d)) * (1 / (d + r)) * (1 / (d + s))) *
          (1 / (16249 / 250000 : Real) - 1 / (d - 16249 / 250000)) := by
      field_simp [ne_of_gt hu, ne_of_gt hv, ne_of_gt hw]
    _ ≤ (564383 / 1000000 : Real) *
        ((1 / ((212499 / 500000 : Real) - 29 / 200)) *
          sectionSixFirstLowCentralSmallI5P1D816Row0Q4 (16249 / 125000 : Real) r *
          sectionSixFirstLowCentralSmallI5P1D816Row0Q4 (16249 / 125000 : Real) s) *
          (1 / (16249 / 250000 : Real) - 1 / (d - 16249 / 250000)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hprod (by positivity)) hprim0
    _ ≤ sectionSixFirstLowCentralSmallI5P1D821Majorant d r s := by
      unfold sectionSixFirstLowCentralSmallI5P1D821Majorant
      have hcoef : 0 ≤ (564383 / 1000000 : Real) *
          ((1 / ((212499 / 500000 : Real) - 29 / 200)) *
            sectionSixFirstLowCentralSmallI5P1D816Row0Q4 (16249 / 125000 : Real) r *
            sectionSixFirstLowCentralSmallI5P1D816Row0Q4 (16249 / 125000 : Real) s) := by
        exact mul_nonneg (by positivity)
          (mul_nonneg (mul_nonneg (by positivity) hQrGlobal) hQsGlobal)
      exact mul_le_mul_of_nonneg_left hprim hcoef


end
end PrimesRestrictedDigits
