import PrimesRestrictedDigits.SieveAsymptotics.SectionSixBuchstabClampedRefinedFiberD900E
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P2FullOuterFubiniD781
import PrimesRestrictedDigits.BasicEstimates.ClosedIccFiberIntegral

/-!
# refined P2 q-fiber profile

This module instantiates the Buchstab split on the exact fixed-delta P2 full-outer carrier. It
is an analytic bridge only: no spatial finite cover or numerical outer cap is asserted here.
The later replay can use the exported profile as a pointwise rational majorant while retaining
the exact q-cap.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.12).
-/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private abbrev d912Delta : Real := 1 / 1000000
private abbrev d912Beta : Real := sectionSixThetaTwo d912Delta

/-- The profile at the translated q-fiber endpoints. -/
def sectionSixFirstLowCentralSmallI5P2RefinedProfileFiberBound
    (x : ((Real × Real) × Real)) : Real :=
  let d := x.1.1
  let r := x.1.2
  let s := x.2
  let upper := sectionSixFirstLowCentralSmallI5P2FullUpper x
  let B := 1 - d912Beta - d - r - s
  let h := d + upper
  sectionSixBuchstabRefinedFiberBound
    (d912Beta - d) (d + r) (d + s) B d h

theorem sectionSixFirstLowCentralSmallI5P2FullOuter_qfiber_le_refinedProfile
    {x : ((Real × Real) × Real)}
    (hx : x ∈ sectionSixFirstLowCentralSmallI5P2FullOuter) :
    (∫ q in sectionSixFirstLowCentralSmallI5P2FullLower x..
      sectionSixFirstLowCentralSmallI5P2FullUpper x,
      sectionSixFirstLowCentralSmallI5P2TransformedKernel (x, q)) <=
      sectionSixFirstLowCentralSmallI5P2RefinedProfileFiberBound x := by
  let d : Real := x.1.1
  let r : Real := x.1.2
  let s : Real := x.2
  let upper : Real := sectionSixFirstLowCentralSmallI5P2FullUpper x
  let B : Real := 1 - d912Beta - d - r - s
  let h : Real := d + upper
  change sectionSixThetaGap d912Delta ≤ d ∧
      d < sectionSixThetaOne d912Delta / 2 ∧
      0 < r ∧ 0 < s ∧ s <= r ∧
      2 * d + r + s < sectionSixThetaOne d912Delta ∧
      2 * r + d < 16 / 25 - d912Beta ∧
      0 <= (1 - d912Beta - 3 * d - r - s) / 2 at hx
  have hgap : 0 < sectionSixThetaGap d912Delta := by
    norm_num [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo,
      d912Delta]
  rcases hx with ⟨hdGap, hdHalf, hr', hs', hsr, htheta, hwall, hcap⟩
  have hd : 0 < d := hgap.trans_le hdGap
  have hdhalf : d < sectionSixThetaOne d912Delta / 2 := hdHalf
  have hbeta : 0 < d912Beta - d := by
    norm_num [d912Beta, d912Delta, sectionSixThetaTwo,
      sectionSixThetaOne] at hdhalf ⊢
    linarith
  have hr : 0 < d + r := by linarith [hr']
  have hs : 0 < d + s := by linarith [hs']
  have hupper0 : 0 ≤ upper := by
    dsimp [upper, sectionSixFirstLowCentralSmallI5P2FullUpper]
    exact le_min hs'.le hcap
  have hdh : d ≤ h := by
    dsimp [h]
    linarith
  have hB : 2 * h ≤ B := by
    have hu : upper ≤ (1 - d912Beta - 3 * d - r - s) / 2 := by
      dsimp [upper, sectionSixFirstLowCentralSmallI5P2FullUpper]
      exact min_le_right _ _
    dsimp [h, B]
    linarith
  let f : Real → Real := fun t =>
    buchstabFunction ((B - t) / t) /
      ((d912Beta - d) * (d + r) * (d + s) * t ^ 2)
  have hprofile := sectionSixBuchstabClampedRefinedFiber_le
    hbeta hr hs hd hdh hB
  have hshift := intervalIntegral.integral_comp_add_right
    (f := f) (a := (0 : Real)) (b := upper) (d := d)
  have hshifted :
      (∫ q in sectionSixFirstLowCentralSmallI5P2FullLower x..
        sectionSixFirstLowCentralSmallI5P2FullUpper x,
        sectionSixFirstLowCentralSmallI5P2TransformedKernel (x, q)) =
        ∫ t in d..h, f t := by
    change
      (∫ q in (0 : Real)..upper,
        buchstabFunction
            ((1 - d912Beta - 2 * d - r - s - q) / (d + q)) /
          ((d912Beta - d) * (d + r) * (d + s) * (d + q) ^ 2)) =
        ∫ t in d..h, f t
    have hfun :
        (fun q : Real =>
          buchstabFunction
              ((1 - d912Beta - 2 * d - r - s - q) / (d + q)) /
            ((d912Beta - d) * (d + r) * (d + s) * (d + q) ^ 2)) =
          fun q : Real => f (q + d) := by
      funext q
      dsimp [f, B]
      congr 2 <;> ring
    rw [hfun, hshift]
    simp [h, add_comm]
  rw [hshifted]
  change
    (∫ t in d..h, f t) <=
      sectionSixFirstLowCentralSmallI5P2RefinedProfileFiberBound x
  dsimp [sectionSixFirstLowCentralSmallI5P2RefinedProfileFiberBound,
    d, r, s, upper, B, h, f] at hprofile ⊢
  exact hprofile

/- The exact constants used by the profile are exposed as checked identities
   for downstream arithmetic shards. -/
theorem sectionSixFirstLowCentralSmallI5P2RefinedProfile_beta_eq :
    d912Beta = (212499 / 500000 : Real) := by
  norm_num [d912Beta, d912Delta, sectionSixThetaTwo]

theorem sectionSixFirstLowCentralSmallI5P2RefinedProfile_gap_eq :
    sectionSixThetaGap d912Delta = (16249 / 250000 : Real) := by
  norm_num [d912Delta, sectionSixThetaGap, sectionSixThetaOne,
    sectionSixThetaTwo]

end
end PrimesRestrictedDigits
