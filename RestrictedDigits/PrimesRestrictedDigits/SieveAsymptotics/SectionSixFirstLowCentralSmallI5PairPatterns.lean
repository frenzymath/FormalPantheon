import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstUniformIntegralRegions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Four pair-side patterns for the low-central-small I5 carrier

The five pair exclusions on the fixed mixed outer carrier have four possible low/high
patterns. This is the finite affine reduction used before any I5 fiber or integral estimate.
Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.12).
-/

open Set

namespace PrimesRestrictedDigits

noncomputable section

private abbrev sectionSixFirstLowCentralSmallI5Delta : Real := 1 / 1000000

@[simp] private def sectionSixFirstLowCentralSmallI5Low (s : Real) : Prop :=
  s < sectionSixThetaOne sectionSixFirstLowCentralSmallI5Delta

@[simp] private def sectionSixFirstLowCentralSmallI5High (s : Real) : Prop :=
  sectionSixThetaTwo sectionSixFirstLowCentralSmallI5Delta < s

private theorem sectionSixFirstLowCentralSmallI5_side
    {s : Real} (hs : s ∉ Set.Icc
      (sectionSixThetaOne sectionSixFirstLowCentralSmallI5Delta)
      (sectionSixThetaTwo sectionSixFirstLowCentralSmallI5Delta)) :
    sectionSixFirstLowCentralSmallI5Low s ∨
      sectionSixFirstLowCentralSmallI5High s := by
  have htheta : sectionSixThetaOne sectionSixFirstLowCentralSmallI5Delta ≤
      sectionSixThetaTwo sectionSixFirstLowCentralSmallI5Delta := by
    norm_num [sectionSixFirstLowCentralSmallI5Delta, sectionSixThetaOne,
      sectionSixThetaTwo]
  by_cases hlow : sectionSixFirstLowCentralSmallI5Low s
  · exact Or.inl hlow
  · right
    have hleft : sectionSixThetaOne sectionSixFirstLowCentralSmallI5Delta ≤ s :=
      le_of_not_gt hlow
    have hnotle : ¬ s ≤
        sectionSixThetaTwo sectionSixFirstLowCentralSmallI5Delta := by
      intro hright
      exact hs ⟨hleft, hright⟩
    exact lt_of_not_ge hnotle

/-- The four admissible side patterns, in `(u+w,u+t,v+w,v+t,w+t)` order. -/
def sectionSixFirstLowCentralSmallI5PairPattern
    (cell : Fin 4) : Set (((Real × Real) × Real) × Real) :=
  match cell with
  | 0 => {x |
      sectionSixFirstLowCentralSmallI5Low (x.1.1.1 + x.1.2) ∧
      sectionSixFirstLowCentralSmallI5Low (x.1.1.1 + x.2) ∧
      sectionSixFirstLowCentralSmallI5Low (x.1.1.2 + x.1.2) ∧
      sectionSixFirstLowCentralSmallI5Low (x.1.1.2 + x.2) ∧
      sectionSixFirstLowCentralSmallI5Low (x.1.2 + x.2)}
  | 1 => {x |
      sectionSixFirstLowCentralSmallI5High (x.1.1.1 + x.1.2) ∧
      sectionSixFirstLowCentralSmallI5Low (x.1.1.1 + x.2) ∧
      sectionSixFirstLowCentralSmallI5Low (x.1.1.2 + x.1.2) ∧
      sectionSixFirstLowCentralSmallI5Low (x.1.1.2 + x.2) ∧
      sectionSixFirstLowCentralSmallI5Low (x.1.2 + x.2)}
  | 2 => {x |
      sectionSixFirstLowCentralSmallI5High (x.1.1.1 + x.1.2) ∧
      sectionSixFirstLowCentralSmallI5High (x.1.1.1 + x.2) ∧
      sectionSixFirstLowCentralSmallI5Low (x.1.1.2 + x.1.2) ∧
      sectionSixFirstLowCentralSmallI5Low (x.1.1.2 + x.2) ∧
      sectionSixFirstLowCentralSmallI5Low (x.1.2 + x.2)}
  | 3 => {x |
      sectionSixFirstLowCentralSmallI5High (x.1.1.1 + x.1.2) ∧
      sectionSixFirstLowCentralSmallI5Low (x.1.1.1 + x.2) ∧
      sectionSixFirstLowCentralSmallI5High (x.1.1.2 + x.1.2) ∧
      sectionSixFirstLowCentralSmallI5Low (x.1.1.2 + x.2) ∧
      sectionSixFirstLowCentralSmallI5Low (x.1.2 + x.2)}

theorem sectionSixFirstLowCentralSmallI5_pairPattern_cover :
    sectionSixFirstLowCentralSmallUniformOuterRegion
        (1 / 1000000 : Real) ⊆
      ⋃ cell : Fin 4,
        sectionSixFirstLowCentralSmallI5PairPattern cell := by
  intro x hx
  rcases x with ⟨⟨⟨u, v⟩, w⟩, t⟩
  rcases hx with ⟨hgap, htw, hwv, hvu, hu, hmix, hsq, hcap,
    hA, hB, hC, hD, hE⟩
  have htheta : sectionSixThetaOne sectionSixFirstLowCentralSmallI5Delta ≤
      sectionSixThetaTwo sectionSixFirstLowCentralSmallI5Delta := by
    norm_num [sectionSixFirstLowCentralSmallI5Delta, sectionSixThetaOne,
      sectionSixThetaTwo]
  have hAs := sectionSixFirstLowCentralSmallI5_side hA
  have hBs := sectionSixFirstLowCentralSmallI5_side hB
  have hCs := sectionSixFirstLowCentralSmallI5_side hC
  have hDs := sectionSixFirstLowCentralSmallI5_side hD
  have hEs := sectionSixFirstLowCentralSmallI5_side hE
  have hDlow : sectionSixFirstLowCentralSmallI5Low (v + t) := by
    rcases hDs with hDl | hDh
    · exact hDl
    · exfalso
      norm_num [sectionSixFirstLowCentralSmallI5Low,
        sectionSixFirstLowCentralSmallI5High,
        sectionSixFirstLowCentralSmallI5Delta, sectionSixThetaOne,
        sectionSixThetaTwo] at hmix hsq hcap hDh
      linarith
  have hElow : sectionSixFirstLowCentralSmallI5Low (w + t) := by
    rcases hEs with hEl | hEh
    · exact hEl
    · exfalso
      norm_num [sectionSixFirstLowCentralSmallI5Low,
        sectionSixFirstLowCentralSmallI5High,
        sectionSixFirstLowCentralSmallI5Delta, sectionSixThetaOne,
        sectionSixThetaTwo] at hsq hcap hEh
      linarith
  have hBCnot : ¬ (sectionSixFirstLowCentralSmallI5High (u + t) ∧
      sectionSixFirstLowCentralSmallI5High (v + w)) := by
    intro hBC
    norm_num [sectionSixFirstLowCentralSmallI5High,
      sectionSixFirstLowCentralSmallI5Delta, sectionSixThetaTwo] at hBC hsq hcap
    linarith
  rcases hAs with hAl | hAh
  · have hBlow : sectionSixFirstLowCentralSmallI5Low (u + t) := by
      rcases hBs with hBl | hBh
      · exact hBl
      · exfalso
        norm_num [sectionSixFirstLowCentralSmallI5Low,
          sectionSixFirstLowCentralSmallI5High,
          sectionSixFirstLowCentralSmallI5Delta, sectionSixThetaOne,
          sectionSixThetaTwo] at hAl hBh
        linarith
    have hClow : sectionSixFirstLowCentralSmallI5Low (v + w) := by
      rcases hCs with hCl | hCh
      · exact hCl
      · exfalso
        norm_num [sectionSixFirstLowCentralSmallI5Low,
          sectionSixFirstLowCentralSmallI5High,
          sectionSixFirstLowCentralSmallI5Delta, sectionSixThetaOne,
          sectionSixThetaTwo] at hAl hCh
        linarith
    refine Set.mem_iUnion.mpr ⟨(0 : Fin 4), ?_⟩
    exact ⟨hAl, hBlow, hClow, hDlow, hElow⟩
  · rcases hBs with hBl | hBh
    · rcases hCs with hCl | hCh
      · refine Set.mem_iUnion.mpr ⟨(1 : Fin 4), ?_⟩
        exact ⟨hAh, hBl, hCl, hDlow, hElow⟩
      · refine Set.mem_iUnion.mpr ⟨(3 : Fin 4), ?_⟩
        exact ⟨hAh, hBl, hCh, hDlow, hElow⟩
    · rcases hCs with hCl | hCh
      · refine Set.mem_iUnion.mpr ⟨(2 : Fin 4), ?_⟩
        exact ⟨hAh, hBh, hCl, hDlow, hElow⟩
      · exact False.elim (hBCnot ⟨hBh, hCh⟩)

theorem sectionSixFirstLowCentralSmallI5_onlyLargestHigh_argument_gt_two
    {x : (((Real × Real) × Real) × Real)}
    (hx : x ∈ sectionSixFirstLowCentralSmallUniformOuterRegion
      (1 / 1000000 : Real))
    (hpattern : x ∈ sectionSixFirstLowCentralSmallI5PairPattern 1) :
    2 < (1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2 := by
  have hgap : 0 < sectionSixThetaGap
      sectionSixFirstLowCentralSmallI5Delta := by
    norm_num [sectionSixFirstLowCentralSmallI5Delta, sectionSixThetaGap,
      sectionSixThetaOne, sectionSixThetaTwo]
  have htPos : 0 < x.2 := hgap.trans hx.1
  rcases x with ⟨⟨⟨u, v⟩, w⟩, t⟩
  rcases hx with ⟨hwall, htw, hwv, hvu, hu, hmix, hsq, hcap,
    hA, hB, hC, hD, hE⟩
  change sectionSixFirstLowCentralSmallI5High (u + w) ∧
      sectionSixFirstLowCentralSmallI5Low (u + t) ∧
      sectionSixFirstLowCentralSmallI5Low (v + w) ∧
      sectionSixFirstLowCentralSmallI5Low (v + t) ∧
      sectionSixFirstLowCentralSmallI5Low (w + t) at hpattern
  rcases hpattern with ⟨hAh, hBl, hCl, hDl, hEl⟩
  apply (lt_div_iff₀ htPos).2
  norm_num [sectionSixFirstLowCentralSmallI5Low,
    sectionSixFirstLowCentralSmallI5High,
    sectionSixFirstLowCentralSmallI5Delta, sectionSixThetaGap,
    sectionSixThetaOne, sectionSixThetaTwo] at hmix hAh hBl hCl ⊢
  linarith

end
end PrimesRestrictedDigits
