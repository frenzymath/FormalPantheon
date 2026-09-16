import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P0FiberCover
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Measurability

/-!
# Measurable endpoint functions for the P0 cells

The native left-associated base is `((Real × Real) × Real)`. These are the pointwise endpoint
facts only; no projected carrier or endpoint ordering is asserted.
-/

namespace PrimesRestrictedDigits

noncomputable section

theorem sectionSixFirstLowCentralSmallI5P0CellLower_measurable
    (b : Fin 3) :
    Measurable (fun z : ((Real × Real) × Real) =>
      sectionSixFirstLowCentralSmallI5P0CellLower z.1.1 z.1.2 z.2 b) := by
  fin_cases b <;>
    simp only [sectionSixFirstLowCentralSmallI5P0CellLower,
      sectionSixFirstLowCentralSmallI5P0RawLower]
  all_goals measurability

theorem sectionSixFirstLowCentralSmallI5P0CellUpper_measurable
    (b : Fin 3) :
    Measurable (fun z : ((Real × Real) × Real) =>
      sectionSixFirstLowCentralSmallI5P0CellUpper z.1.1 z.1.2 z.2 b) := by
  fin_cases b <;>
    simp only [sectionSixFirstLowCentralSmallI5P0CellUpper,
      sectionSixFirstLowCentralSmallI5P0RawUpper]
  all_goals measurability

end

end PrimesRestrictedDigits
