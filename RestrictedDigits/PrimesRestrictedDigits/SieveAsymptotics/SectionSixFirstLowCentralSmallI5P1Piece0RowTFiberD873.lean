import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece0TailMajorantD821
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
/-! # SectionSixFirstLowCentralSmallI5P1Piece0RowTFiberD873 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits
noncomputable section

/-!
# generic transformed Piece0 row t-fiber majorant

This module proves a pointwise t-fiber bound on any closed d-interval inside the transformed
Piece0 range. It makes no row-integral, Fubini, finite-sum, source, or numerical-cap claim.
-/

private abbrev d873D0 : Real :=
  sectionSixFirstLowCentralSmallI5P1D807D0

private abbrev d873Ds : Real :=
  sectionSixFirstLowCentralSmallI5P1D807Ds

private abbrev d873Beta : Real :=
  sectionSixFirstLowCentralSmallI5P1D807Beta

private abbrev d873Gap : Real :=
  sectionSixFirstLowCentralSmallI5P1D807Gap

private abbrev d873H : Real -> Real :=
  sectionSixFirstLowCentralSmallI5P1D807H

private abbrev d873Q4 : Real -> Real -> Real :=
  sectionSixFirstLowCentralSmallI5P1D816Row0Q4

theorem sectionSixFirstLowCentralSmallI5P1D873_p0Row_tFiber_le
    {a b d r s : Real}
    (hD0a : sectionSixFirstLowCentralSmallI5P1D807D0 <= a)
    (hab : a <= b)
    (hbDs : b <= sectionSixFirstLowCentralSmallI5P1D807Ds)
    (hd : d ∈ Set.Icc a b)
    (hr : r ∈ Set.Icc 0
      (sectionSixFirstLowCentralSmallI5P1D807H d))
    (hs : s ∈ Set.Icc 0 r) :
    (∫ t in sectionSixFirstLowCentralSmallI5P1D807Gap..
        (d - sectionSixFirstLowCentralSmallI5P1D807Gap),
      sectionSixFirstLowCentralSmallI5P1D809Kernel (((d, r), s), t)) <=
      ((sectionSixFirstLowCentralSmallI5P1D816Row0TailC /
          (sectionSixFirstLowCentralSmallI5P1D807Beta - b) *
          (1 / sectionSixFirstLowCentralSmallI5P1D807Gap -
            1 / (b - sectionSixFirstLowCentralSmallI5P1D807Gap))) *
        sectionSixFirstLowCentralSmallI5P1D816Row0Q4 a r *
        sectionSixFirstLowCentralSmallI5P1D816Row0Q4 a s) := by
  rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
    ⟨hA, hBeta, hGap, hD0, hDs, hDr, hD1⟩
  have hD0pos : 0 < d873D0 := by
    change 0 < sectionSixFirstLowCentralSmallI5P1D807D0
    rw [hD0]
    norm_num
  have hGapPos : 0 < d873Gap := by
    change 0 < sectionSixFirstLowCentralSmallI5P1D807Gap
    rw [hGap]
    norm_num
  have hDsBeta : d873Ds < d873Beta := by
    change sectionSixFirstLowCentralSmallI5P1D807Ds <
      sectionSixFirstLowCentralSmallI5P1D807Beta
    rw [hDs, hBeta]
    norm_num
  have haPos : 0 < a := hD0pos.trans_le hD0a
  have hbBeta : 0 < d873Beta - b := sub_pos.mpr (hbDs.trans_lt hDsBeta)
  have hbetaD : 0 < d873Beta - d := by linarith [hd.2]
  have hdrPos : 0 < d + r := by linarith [hd.1, hr.1]
  have hdsPos : 0 < d + s := by linarith [hd.1, hs.1]
  have h2GapD0 : 2 * d873Gap = d873D0 := by
    change 2 * sectionSixFirstLowCentralSmallI5P1D807Gap =
      sectionSixFirstLowCentralSmallI5P1D807D0
    rw [hGap, hD0]
    norm_num
  have hGapLe : d873Gap <= d - d873Gap := by
    linarith [hD0a, hd.1, h2GapD0]
  have hDGPos : 0 < d - d873Gap := hGapPos.trans_le hGapLe
  have hrs : r + s <=
      sectionSixFirstLowCentralSmallI5P1D807Square - d873Beta - d := by
    unfold sectionSixFirstLowCentralSmallI5P1D807H at hr
    linarith [hr.2, hs.2]
  have htail : 4 * (d - d873Gap) <= 1 - d873Beta - d - r - s := by
    have hdDs : d <= d873Ds := hd.2.trans hbDs
    have hleft : 4 * (d - d873Gap) <= 4 * (d873Ds - d873Gap) := by
      linarith
    have hright : 1 - d873Beta - d - r - s >=
        1 - sectionSixFirstLowCentralSmallI5P1D807Square := by
      linarith [hrs]
    change 4 *
      (d - sectionSixFirstLowCentralSmallI5P1D807Gap) <=
        4 * (sectionSixFirstLowCentralSmallI5P1D807Ds -
          sectionSixFirstLowCentralSmallI5P1D807Gap) at hleft
    change 1 - sectionSixFirstLowCentralSmallI5P1D807Beta - d - r - s >=
      1 - sectionSixFirstLowCentralSmallI5P1D807Square at hright
    change 4 * (d - sectionSixFirstLowCentralSmallI5P1D807Gap) <=
      1 - sectionSixFirstLowCentralSmallI5P1D807Beta - d - r - s
    rw [hGap, hDs] at hleft
    rw [hBeta]
    norm_num [sectionSixFirstLowCentralSmallI5P1D807Square,
      sectionSixFirstLowCentralSmallI5P1D807Delta,
      sectionSixThetaOne, sectionSixThetaTwo] at hright
    linarith
  have htailRaw := integral_sectionSixBuchstabTailBranch_le
    (u := d873Beta - d) (v := d + r) (w := d + s)
    (B := 1 - d873Beta - d - r - s)
    (l := d873Gap) (h := d - d873Gap)
    hbetaD hdrPos hdsPos hGapPos hGapLe htail
  have hqR := sectionSixFirstLowCentralSmallI5P1D816_q4_inv_le
    (a := a) (x := r) haPos hr.1
  have hqS := sectionSixFirstLowCentralSmallI5P1D816_q4_inv_le
    (a := a) (x := s) haPos hs.1
  have hArPos : 0 < a + r := by linarith [hr.1]
  have hAsPos : 0 < a + s := by linarith [hs.1]
  have hInvBeta : 1 / (d873Beta - d) <= 1 / (d873Beta - b) := by
    exact one_div_le_one_div_of_le hbBeta (by linarith [hd.2])
  have hInvR : 1 / (d + r) <= 1 / (a + r) := by
    exact one_div_le_one_div_of_le hArPos (by linarith [hd.1])
  have hInvS : 1 / (d + s) <= 1 / (a + s) := by
    exact one_div_le_one_div_of_le hAsPos (by linarith [hd.1])
  have hQ4R0 : 0 <= d873Q4 a r :=
    (show 0 <= 1 / (a + r) by positivity).trans hqR
  have hQ4S0 : 0 <= d873Q4 a s :=
    (show 0 <= 1 / (a + s) by positivity).trans hqS
  have hprod :
      (1 / (d873Beta - d)) * (1 / (d + r)) * (1 / (d + s)) <=
        (1 / (d873Beta - b)) * d873Q4 a r * d873Q4 a s := by
    calc
      (1 / (d873Beta - d)) * (1 / (d + r)) * (1 / (d + s)) <=
          (1 / (d873Beta - b)) * (1 / (d + r)) * (1 / (d + s)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hInvBeta (by positivity)) (by positivity)
      _ <= (1 / (d873Beta - b)) * d873Q4 a r * (1 / (d + s)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hInvR.trans hqR) (by positivity))
          (by positivity)
      _ <= (1 / (d873Beta - b)) * d873Q4 a r * d873Q4 a s := by
        exact mul_le_mul_of_nonneg_left (hInvS.trans hqS)
          (mul_nonneg (by positivity) hQ4R0)
  have hUpperGap : d873Gap <= b - d873Gap := by
    linarith [hD0a, hab, h2GapD0]
  have hBGPos : 0 < b - d873Gap := hGapPos.trans_le hUpperGap
  have hTailMono : 1 / d873Gap - 1 / (d - d873Gap) <=
      1 / d873Gap - 1 / (b - d873Gap) := by
    exact sub_le_sub_left
      (one_div_le_one_div_of_le hDGPos (by linarith [hd.2])) _
  have hTail0 : 0 <= 1 / d873Gap - 1 / (d - d873Gap) := by
    exact sub_nonneg.mpr (one_div_le_one_div_of_le hGapPos hGapLe)
  have htarget0 : 0 <=
      (564383 / 1000000 : Real) *
        ((1 / (d873Beta - b)) * d873Q4 a r * d873Q4 a s) := by
    positivity
  calc
    (∫ t in d873Gap..(d - d873Gap),
        sectionSixFirstLowCentralSmallI5P1D809Kernel (((d, r), s), t)) =
        ∫ t in d873Gap..(d - d873Gap),
          buchstabFunction ((1 - d873Beta - d - r - s - t) / t) /
            ((d873Beta - d) * (d + r) * (d + s) * t ^ (2 : Nat)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have hk := sectionSixFirstLowCentralSmallI5P1D816_kernel_formula d r s t
      have hk' := show
          sectionSixFirstLowCentralSmallI5P1D809Kernel (((d, r), s), t) =
            buchstabFunction
                ((1 - sectionSixFirstLowCentralSmallI5P1D816Row0Beta -
                  d - r - s - t) / t) /
              ((sectionSixFirstLowCentralSmallI5P1D816Row0Beta - d) *
                (d + r) * (d + s) * t ^ (2 : Nat)) by
        simpa [sectionSixFirstLowCentralSmallI5P1D816Row0Kernel] using hk
      convert hk' using 1;
        norm_num [d873Beta, sectionSixFirstLowCentralSmallI5P1D816Row0Beta,
          sectionSixFirstLowCentralSmallI5P1D807Beta,
          sectionSixFirstLowCentralSmallI5P1D807Delta, sectionSixThetaTwo]
    _ <= (564383 / 1000000 : Real) /
          ((d873Beta - d) * (d + r) * (d + s)) *
          (1 / d873Gap - 1 / (d - d873Gap)) := by
      simpa [div_eq_mul_inv, mul_assoc] using htailRaw
    _ = (564383 / 1000000 : Real) *
          ((1 / (d873Beta - d)) * (1 / (d + r)) * (1 / (d + s))) *
          (1 / d873Gap - 1 / (d - d873Gap)) := by
      field_simp [ne_of_gt hbetaD, ne_of_gt hdrPos, ne_of_gt hdsPos]
    _ <= (564383 / 1000000 : Real) *
          ((1 / (d873Beta - b)) * d873Q4 a r * d873Q4 a s) *
          (1 / d873Gap - 1 / (d - d873Gap)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hprod (by positivity)) hTail0
    _ <= (564383 / 1000000 : Real) *
          ((1 / (d873Beta - b)) * d873Q4 a r * d873Q4 a s) *
          (1 / d873Gap - 1 / (b - d873Gap)) := by
      exact mul_le_mul_of_nonneg_left hTailMono htarget0
    _ = ((564383 / 1000000 : Real) / (d873Beta - b) *
          (1 / d873Gap - 1 / (b - d873Gap))) *
          d873Q4 a r * d873Q4 a s := by
      ring


end
end PrimesRestrictedDigits
