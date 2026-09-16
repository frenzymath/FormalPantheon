import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P2RefinedProfileD912
import Mathlib.Algebra.Order.Group.MinMax

/-!
# clamped interval algebra for the P2 profile

The generic identities flatten nested max-min clamps. The final three results put every
translated P2 endpoint and its width into the form needed by later local rational caps.
-/

set_option autoImplicit false
set_option warningAsError true

namespace PrimesRestrictedDigits

theorem sectionSixBuchstabClamp_raiseLower_D976
    {l h a x : Real} (hax : a <= x) :
    sectionSixBuchstabClamp (sectionSixBuchstabClamp l h a) h x =
      sectionSixBuchstabClamp l h x := by
  unfold sectionSixBuchstabClamp
  rw [max_assoc, max_eq_right (min_le_min_left h hax)]

theorem sectionSixBuchstabClamp_between_D976
    {l h a x b : Real} (hax : a <= x) (hxb : x <= b) :
    sectionSixBuchstabClamp
        (sectionSixBuchstabClamp l h a)
        (sectionSixBuchstabClamp l h b) x =
      sectionSixBuchstabClamp l h x := by
  simp only [sectionSixBuchstabClamp, max_def, min_def]
  split_ifs <;> linarith

theorem sectionSixFirstLowCentralSmallI5P2_shiftedUpper_eq_D976
    (x : ((Real × Real) × Real)) :
    let beta := sectionSixThetaTwo (1 / 1000000 : Real)
    let d := x.1.1
    let r := x.1.2
    let s := x.2
    let B := 1 - beta - d - r - s
    d + sectionSixFirstLowCentralSmallI5P2FullUpper x =
      min (d + s) (B / 2) := by
  dsimp only
  change
    x.1.1 +
        min x.2
          ((1 - sectionSixThetaTwo (1 / 1000000 : Real) -
            3 * x.1.1 - x.1.2 - x.2) / 2) =
      min (x.1.1 + x.2)
        ((1 - sectionSixThetaTwo (1 / 1000000 : Real) -
          x.1.1 - x.1.2 - x.2) / 2)
  let Q : Real :=
    (1 - sectionSixThetaTwo (1 / 1000000 : Real) -
      3 * x.1.1 - x.1.2 - x.2) / 2
  let R : Real :=
    (1 - sectionSixThetaTwo (1 / 1000000 : Real) -
      x.1.1 - x.1.2 - x.2) / 2
  change x.1.1 + min x.2 Q = min (x.1.1 + x.2) R
  have hQR : x.1.1 + Q = R := by
    dsimp only [Q, R]
    ring
  rw [<- hQR]
  by_cases hs : x.2 <= Q
  · rw [min_eq_left hs, min_eq_left (by linarith)]
  · have hQs : Q <= x.2 := le_of_not_ge hs
    rw [min_eq_right hQs, min_eq_right (by linarith)]

theorem sectionSixBuchstabClampedEndpoints_eq_D976
    {d W B rhoL rhoH : Real}
    (hrho : rhoL <= rhoH) (hhalf : rhoH <= B / 2) :
    let h := min W (B / 2)
    let L := sectionSixBuchstabClamp d h rhoL
    let H := sectionSixBuchstabClamp d h rhoH
    L = max d (min W rhoL) ∧
      H = max d (min W rhoH) ∧ L <= H := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · unfold sectionSixBuchstabClamp
    rw [min_assoc, min_eq_right (hrho.trans hhalf)]
  · unfold sectionSixBuchstabClamp
    rw [min_assoc, min_eq_right hhalf]
  · unfold sectionSixBuchstabClamp
    exact max_le_max_left d (min_le_min_left (min W (B / 2)) hrho)

theorem sectionSixBuchstabClampedEndpoints_of_posWidth_D976
    {d W rhoL rhoH : Real}
    (hpos : 0 < max d (min W rhoH) - max d (min W rhoL)) :
    max d (min W rhoL) = max d rhoL ∧
      max d (min W rhoH) = min W rhoH := by
  have hLH : max d (min W rhoL) < max d (min W rhoH) := sub_pos.mp hpos
  have hdH : d < max d (min W rhoH) :=
    lt_of_le_of_lt (le_max_left d (min W rhoL)) hLH
  have hdMin : d < min W rhoH := by
    by_contra h
    have hMinLe : min W rhoH <= d := le_of_not_gt h
    rw [max_eq_left hMinLe] at hdH
    exact (lt_irrefl d) hdH
  have hdW : d < W := hdMin.trans_le (min_le_left W rhoH)
  have hHleW : max d (min W rhoH) <= W := by
    rw [max_eq_right hdMin.le]
    exact min_le_left W rhoH
  have hLltW : max d (min W rhoL) < W := hLH.trans_le hHleW
  have hrhoLltW : rhoL < W := by
    by_contra h
    have hWrhoL : W <= rhoL := le_of_not_gt h
    rw [min_eq_left hWrhoL, max_eq_right hdW.le] at hLltW
    exact (lt_irrefl W) hLltW
  exact ⟨by rw [min_eq_right hrhoLltW.le], max_eq_right hdMin.le⟩

theorem sectionSixBuchstabClampedWidth_bounds_D976
    {d W rhoL rhoH : Real}
    (hdW : d <= W) (hrho : rhoL <= rhoH) :
    let L := max d (min W rhoL)
    let H := max d (min W rhoH)
    let Delta := H - L
    d <= L ∧ L <= H ∧ H <= W ∧
      Delta <= max 0 (W - d) ∧
      Delta <= max 0 (rhoH - d) ∧
      Delta <= max 0 (W - rhoL) ∧
      Delta <= max 0 (rhoH - rhoL) := by
  let L : Real := max d (min W rhoL)
  let H : Real := max d (min W rhoH)
  let Delta : Real := H - L
  change d <= L ∧ L <= H ∧ H <= W ∧
    Delta <= max 0 (W - d) ∧
    Delta <= max 0 (rhoH - d) ∧
    Delta <= max 0 (W - rhoL) ∧
    Delta <= max 0 (rhoH - rhoL)
  have hLlo : d <= L := by
    dsimp only [L]
    exact le_max_left d (min W rhoL)
  have hMinOrder : min W rhoL <= min W rhoH := min_le_min_left W hrho
  have hLH : L <= H := by
    dsimp only [L, H]
    exact max_le_max_left d hMinOrder
  have hHhi : H <= W := by
    dsimp only [H]
    exact max_le hdW (min_le_left W rhoH)
  have hTotal : Delta <= max 0 (W - d) := by
    have hraw : Delta <= W - d := by
      dsimp only [Delta]
      exact sub_le_sub hHhi hLlo
    exact hraw.trans (le_max_right 0 (W - d))
  have hFromLower : Delta <= max 0 (rhoH - d) := by
    by_cases hHigh : rhoH <= d
    · have hHeq : H = d := by
        dsimp only [H]
        exact max_eq_left ((min_le_right W rhoH).trans hHigh)
      have hLeq : L = d := by
        dsimp only [L]
        exact max_eq_left ((min_le_right W rhoL).trans (hrho.trans hHigh))
      dsimp only [Delta]
      rw [hHeq, hLeq, sub_self]
      exact le_max_left 0 (rhoH - d)
    · have hdHigh : d <= rhoH := (lt_of_not_ge hHigh).le
      have hHrho : H <= rhoH := by
        dsimp only [H]
        exact max_le hdHigh (min_le_right W rhoH)
      have hraw : Delta <= rhoH - d := by
        dsimp only [Delta]
        exact sub_le_sub hHrho hLlo
      exact hraw.trans (le_max_right 0 (rhoH - d))
  have hFromUpper : Delta <= max 0 (W - rhoL) := by
    by_cases hLow : W <= rhoL
    · have hLeq : L = W := by
        dsimp only [L]
        rw [min_eq_left hLow, max_eq_right hdW]
      have hHeq : H = W := by
        dsimp only [H]
        rw [min_eq_left (hLow.trans hrho), max_eq_right hdW]
      dsimp only [Delta]
      rw [hHeq, hLeq, sub_self]
      exact le_max_left 0 (W - rhoL)
    · have hLowW : rhoL <= W := (lt_of_not_ge hLow).le
      have hrhoL : rhoL <= L := by
        dsimp only [L]
        rw [min_eq_right hLowW]
        exact le_max_right d rhoL
      have hraw : Delta <= W - rhoL := by
        dsimp only [Delta]
        exact sub_le_sub hHhi hrhoL
      exact hraw.trans (le_max_right 0 (W - rhoL))
  have hRaw : Delta <= max 0 (rhoH - rhoL) := by
    have hMinDiff : min W rhoH - min W rhoL <= rhoH - rhoL := by
      by_cases hHigh : rhoH <= W
      · rw [min_eq_right hHigh, min_eq_right (hrho.trans hHigh)]
      · have hWHigh : W <= rhoH := (lt_of_not_ge hHigh).le
        rw [min_eq_left hWHigh]
        by_cases hLow : rhoL <= W
        · rw [min_eq_right hLow]
          linarith
        · have hWLow : W <= rhoL := (lt_of_not_ge hLow).le
          rw [min_eq_left hWLow]
          linarith
    have hClampDiff : Delta <= max 0 (min W rhoH - min W rhoL) := by
      dsimp only [Delta, H, L]
      simpa using
        (max_sub_max_le_max d (min W rhoH) d (min W rhoL))
    exact hClampDiff.trans (max_le_max_left 0 hMinDiff)
  exact ⟨hLlo, hLH, hHhi, hTotal, hFromLower, hFromUpper, hRaw⟩

end PrimesRestrictedDigits
