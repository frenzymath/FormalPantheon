import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6FiberBranchWalls
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixBuchstabFiberIntegrals

/-!
# I6 branch-interval payload transport

This module transports a uniform weak Buchstab range on a closed fiber interval to the
corresponding inverse, middle, or tail payload theorem. The payload constants and logarithmic
identity come from the Buchstab fiber bounds.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.13), region `R_4`.
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

theorem sectionSixFirstLowBelowI6_branchIntervalPayload
    {u v w B l h : Real}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hl : 0 < l) (hlh : l <= h) :
    ((∀ t ∈ Icc l h,
        1 <= (B - t) / t ∧ (B - t) / t <= 2) →
      (∫ t in l..h,
        buchstabFunction ((B - t) / t) /
          (u * v * w * t ^ (2 : Nat))) =
        1 / (u * v * w * B) *
          Real.log (h * (B - l) / (l * (B - h)))) ∧
    ((∀ t ∈ Icc l h,
        2 <= (B - t) / t ∧ (B - t) / t <= 3) →
      (∫ t in l..h,
        buchstabFunction ((B - t) / t) /
          (u * v * w * t ^ (2 : Nat))) <=
        (70893 / 125000 : Real) / (u * v * w) *
          (1 / l - 1 / h)) ∧
    ((∀ t ∈ Icc l h,
        3 <= (B - t) / t) →
      (∫ t in l..h,
        buchstabFunction ((B - t) / t) /
          (u * v * w * t ^ (2 : Nat))) <=
        (564383 / 1000000 : Real) / (u * v * w) *
          (1 / l - 1 / h)) := by
  have hwalls := sectionSixFirstLowBelowI6_fiber_branch_walls
    (B := B) (l := l) (h := h) hl hlh
  constructor
  · intro hwall
    rcases hwalls.2.2.mp hwall with ⟨hAOne, hATwo⟩
    exact integral_sectionSixBuchstabInverseBranch_eq
      hu hv hw hl hlh hAOne hATwo
  constructor
  · intro hwall
    rcases hwalls.2.1.mp hwall with ⟨hATwo, hAThree⟩
    exact integral_sectionSixBuchstabMiddleBranch_le
      hu hv hw hl hlh hATwo hAThree
  · intro hwall
    exact integral_sectionSixBuchstabTailBranch_le hu hv hw hl hlh
      (hwalls.1.mp hwall)

end

end PrimesRestrictedDigits
