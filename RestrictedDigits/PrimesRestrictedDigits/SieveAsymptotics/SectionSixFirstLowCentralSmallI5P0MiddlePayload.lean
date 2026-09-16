import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P0FiberCover
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixBuchstabFiberIntegrals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# P0 middle-cell payload for the low-central-small I5 carrier

The fixed middle cell uses the existing weak Buchstab middle envelope. The public max/min
endpoints are retained literally, so this is a symbolic closed-cell estimate and not a
strict-fiber membership claim.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.12).
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

theorem sectionSixFirstLowCentralSmallI5P0MiddleCell_integral_le
    {u v w : Real}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hLU :
      sectionSixFirstLowCentralSmallI5P0CellLower u v w (1 : Fin 3) <=
        sectionSixFirstLowCentralSmallI5P0CellUpper u v w (1 : Fin 3)) :
    (∫ t in
        sectionSixFirstLowCentralSmallI5P0CellLower u v w (1 : Fin 3)..
        sectionSixFirstLowCentralSmallI5P0CellUpper u v w (1 : Fin 3),
      buchstabFunction ((1 - u - v - w - t) / t) /
        (u * v * w * t ^ (2 : Nat))) <=
      (70893 / 125000 : Real) / (u * v * w) *
        (1 /
            sectionSixFirstLowCentralSmallI5P0CellLower u v w (1 : Fin 3) -
          1 /
            sectionSixFirstLowCentralSmallI5P0CellUpper u v w (1 : Fin 3)) := by
  have hgap : 0 < sectionSixThetaGap (1 / 1000000 : Real) := by
    norm_num [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo]
  have hl : 0 <
      sectionSixFirstLowCentralSmallI5P0CellLower u v w (1 : Fin 3) := by
    unfold sectionSixFirstLowCentralSmallI5P0CellLower
    exact lt_of_lt_of_le hgap (le_max_left _ _)
  have hh : 0 <
      sectionSixFirstLowCentralSmallI5P0CellUpper u v w (1 : Fin 3) :=
    lt_of_lt_of_le hl hLU
  have hATwo : 3 *
      sectionSixFirstLowCentralSmallI5P0CellUpper u v w (1 : Fin 3) <=
        1 - u - v - w := by
    have hraw :
        sectionSixFirstLowCentralSmallI5P0CellUpper u v w (1 : Fin 3) <=
          sectionSixFirstLowCentralSmallI5P0RawUpper u v w (1 : Fin 3) := by
      unfold sectionSixFirstLowCentralSmallI5P0CellUpper
      exact min_le_right _ _
    have hraw' :
        sectionSixFirstLowCentralSmallI5P0RawUpper u v w (1 : Fin 3) <=
          (1 - u - v - w) / 3 := by
      change (1 - u - v - w) / 3 <=
        (1 - u - v - w) / 3
      exact le_rfl
    have hupper := hraw.trans hraw'
    linarith [hupper]
  have hAThree : 1 - u - v - w <= 4 *
      sectionSixFirstLowCentralSmallI5P0CellLower u v w (1 : Fin 3) := by
    have hraw :
        sectionSixFirstLowCentralSmallI5P0RawLower u v w (1 : Fin 3) <=
          sectionSixFirstLowCentralSmallI5P0CellLower u v w (1 : Fin 3) := by
      unfold sectionSixFirstLowCentralSmallI5P0CellLower
      exact le_max_right _ _
    have hraw' :
        (1 - u - v - w) / 4 <=
          sectionSixFirstLowCentralSmallI5P0RawLower u v w (1 : Fin 3) := by
      change (1 - u - v - w) / 4 <=
        (1 - u - v - w) / 4
      exact le_rfl
    have hlower := hraw'.trans hraw
    linarith [hlower]
  exact integral_sectionSixBuchstabMiddleBranch_le
    hu hv hw hl hLU hATwo hAThree

end

end PrimesRestrictedDigits
