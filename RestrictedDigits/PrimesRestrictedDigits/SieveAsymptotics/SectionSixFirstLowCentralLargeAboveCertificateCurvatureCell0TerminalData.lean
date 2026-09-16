import Mathlib.Tactic.NormNum
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell0TerminalSupport

/-! Common exact scale for the four static Cell0 terminal tables. -/
open scoped BigOperators Polynomial

namespace PrimesRestrictedDigits

noncomputable section

namespace SectionSixFirstLowCentralLargeAboveCell0Certificate

def cell0TerminalScale : Rat :=
  1789086433087645879074167 /
    4870981538202613592147827148437500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

theorem cell0TerminalScale_eq_base :
    cell0TerminalScale = cell0PScale * cell0QScale * cell0QScale := by
  norm_num [cell0TerminalScale, cell0PScale, cell0QScale]

theorem cell0TerminalScale_eq_half_power :
    cell0TerminalScale = cell0PowerScale / 2 := by
  norm_num [cell0TerminalScale, cell0PowerScale]

end SectionSixFirstLowCentralLargeAboveCell0Certificate

end

end PrimesRestrictedDigits
