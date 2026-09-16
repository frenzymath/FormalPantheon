import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6TailCellPayload
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowBelowI6FiberCover
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Transport the fixed I6 tail payload to its labelled fiber cell

This is a one-way geometric bridge from the rectangle to the all-high tail cell. It makes no
global cover, replay, or numerical-cap claim.
-/

open Set

namespace PrimesRestrictedDigits

noncomputable section

theorem sectionSixFirstLowBelowI6TailCell_subset_delta6AllHighTailCell :
    sectionSixFirstLowBelowI6TailCell ⊆
      {x | sectionSixFirstLowBelowI6BaseFamily
          x.1.1.1 x.1.1.2 x.1.2 true ∧
        x.2 ∈ sectionSixFirstLowBelowI6FiberCell
          x.1.1.1 x.1.1.2 x.1.2 (2 : Fin 3)
          (fun _ : Fin 5 => true)} := by
  intro x hx
  have hwall := sectionSixFirstLowBelowI6TailCell_tail_wall hx
  rcases hx with ⟨⟨⟨⟨hu, huUpper⟩, ⟨hv, hvUpper⟩⟩,
    ⟨hw, hwUpper⟩⟩, ⟨ht, htUpper⟩⟩
  have hgap : 0 < sectionSixThetaGap (1 / 1000000 : Real) := by
    norm_num [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo]
  have hgaplt : sectionSixThetaGap (1 / 1000000 : Real) < x.2 := by
    norm_num [sectionSixThetaGap, sectionSixThetaOne, sectionSixThetaTwo] at ht ⊢
    linarith
  have htw : x.2 <= x.1.2 := by linarith
  have hwv : x.1.2 <= x.1.1.2 := by linarith
  have hvu : x.1.1.2 <= x.1.1.1 := by linarith
  have huv : x.1.1.1 + x.1.1.2 <
      sectionSixThetaOne (1 / 1000000 : Real) := by
    norm_num [sectionSixThetaOne] at huUpper hvUpper ⊢
    linarith
  have h0 : sectionSixThetaTwo (1 / 1000000 : Real) -
      x.1.1.1 - x.1.1.2 <= x.2 := by
    norm_num [sectionSixThetaTwo] at hu hv ht ⊢
    linarith
  have h1 : sectionSixThetaTwo (1 / 1000000 : Real) -
      x.1.1.1 - x.1.2 <= x.2 := by
    norm_num [sectionSixThetaTwo] at hu hw ht ⊢
    linarith
  have h2 : sectionSixThetaTwo (1 / 1000000 : Real) -
      x.1.1.2 - x.1.2 <= x.2 := by
    norm_num [sectionSixThetaTwo] at hv hw ht ⊢
    linarith
  have h3 : sectionSixThetaTwo (1 / 1000000 : Real) -
      x.1.1.1 - x.1.1.2 - x.1.2 <= x.2 := by
    norm_num [sectionSixThetaTwo] at hu hv hw ht ⊢
    linarith
  have h4 : 1 - sectionSixThetaOne (1 / 1000000 : Real) -
      x.1.1.1 - x.1.1.2 - x.1.2 <= x.2 := by
    norm_num [sectionSixThetaOne] at hu hv hw ht ⊢
    linarith
  have htail : x.2 <=
      (1 - x.1.1.1 - x.1.1.2 - x.1.2) / 4 := by
    rw [le_div_iff₀ (by norm_num : (0 : Real) < 4)]
    nlinarith [hwall]
  have hcell := sectionSixFirstLowBelowI6FiberCell_mem_tail_allHigh_of_bounds
    hgap hgaplt htw h0 h1 h2 h3 h4 htail hwv hvu huv
  change sectionSixFirstLowBelowI6BaseFamily
      x.1.1.1 x.1.1.2 x.1.2 true ∧
    x.2 ∈ sectionSixFirstLowBelowI6FiberCell
      x.1.1.1 x.1.1.2 x.1.2 (2 : Fin 3) (fun _ : Fin 5 => true)
  refine ⟨?_, hcell⟩
  right
  change true = true ∧
    sectionSixThetaTwo (1 / 1000000 : Real) <
      x.1.1.1 + x.1.1.2 + x.1.2
  refine ⟨rfl, ?_⟩
  norm_num [sectionSixThetaTwo] at hu hv hw ⊢
  linarith

end

end PrimesRestrictedDigits
