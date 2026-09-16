import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P0FiberCover
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixBuchstabFiberIntegrals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# P0 tail-cell payload for the low-central-small I5 carrier

The fixed tail cell uses the existing weak Buchstab tail envelope. Its endpoints remain the
public max/min expressions from the P0 fiber module, so this theorem is a symbolic interval
estimate rather than a claim that the closed cell is contained in the strict carrier.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.12).
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

theorem sectionSixFirstLowCentralSmallI5P0TailCell_integral_le
    {u v w : Real}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hLU :
      sectionSixFirstLowCentralSmallI5P0CellLower u v w 2 <=
        sectionSixFirstLowCentralSmallI5P0CellUpper u v w 2) :
    (∫ t in
        sectionSixFirstLowCentralSmallI5P0CellLower u v w 2..
        sectionSixFirstLowCentralSmallI5P0CellUpper u v w 2,
      buchstabFunction ((1 - u - v - w - t) / t) /
        (u * v * w * t ^ 2)) <=
      (564383 / 1000000 : Real) / (u * v * w) *
        (1 / sectionSixFirstLowCentralSmallI5P0CellLower u v w 2 -
         1 / sectionSixFirstLowCentralSmallI5P0CellUpper u v w 2) := by
  have hgap : 0 < sectionSixThetaGap (1 / 1000000 : Real) := by
    norm_num [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo]
  have hl : 0 <
      sectionSixFirstLowCentralSmallI5P0CellLower u v w 2 := by
    unfold sectionSixFirstLowCentralSmallI5P0CellLower
    exact lt_of_lt_of_le hgap (le_max_left _ _)
  have hh : 0 <
      sectionSixFirstLowCentralSmallI5P0CellUpper u v w 2 :=
    lt_of_lt_of_le hl hLU
  have hAThree : 4 *
      sectionSixFirstLowCentralSmallI5P0CellUpper u v w 2 <=
        1 - u - v - w := by
    have hraw :
        sectionSixFirstLowCentralSmallI5P0CellUpper u v w 2 <=
          sectionSixFirstLowCentralSmallI5P0RawUpper u v w 2 := by
      unfold sectionSixFirstLowCentralSmallI5P0CellUpper
      exact min_le_right _ _
    have hraw' :
        sectionSixFirstLowCentralSmallI5P0RawUpper u v w 2 <=
          (1 - u - v - w) / 4 := by
      change (1 - u - v - w) / 4 <=
        (1 - u - v - w) / 4
      exact le_rfl
    have hupper := hraw.trans hraw'
    linarith [hupper]
  exact integral_sectionSixBuchstabTailBranch_le
    hu hv hw hl hLU hAThree

end

end PrimesRestrictedDigits
