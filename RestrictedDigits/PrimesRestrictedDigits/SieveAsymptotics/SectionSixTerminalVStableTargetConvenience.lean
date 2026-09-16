import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStableTargetRegion

/-!
# Convenience margin for terminal-V stable targets

The low terminal band uses all displayed positions, while the high band uses their complement.
Both choices retain the exact two-epsilon margin required before the local grid loss is
charged.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private noncomputable def terminalVDisplayedPositions
    {ell M : Nat} (pattern : SectionSixTerminalVStablePattern ell M) :
    Finset (Fin ((pattern.1.1 + ell) + pattern.2.1.1)) :=
  Finset.univ.map pattern.2.2

private theorem sum_terminalVDisplayedPositions
    {ell M : Nat} (pattern : SectionSixTerminalVStablePattern ell M)
    (x : Fin ((pattern.1.1 + ell) + pattern.2.1.1) -> Real) :
    (∑ j ∈ terminalVDisplayedPositions pattern, x j) =
      sectionSixTerminalVDisplayedSum pattern x := by
  rw [terminalVDisplayedPositions, Finset.sum_map]
  rw [Fin.sum_univ_add]
  change (∑ i : Fin pattern.1.1, x (pattern.innerPositionEmbedding i)) +
      (∑ i : Fin ell, x (pattern.sourcePositionEmbedding i)) = _
  rw [sectionSixTerminalVDisplayedSum, sectionSixTerminalVSourceSum,
    sectionSixTerminalVInnerSum]
  ring

/-- Every terminal-V target retains its exact two-epsilon convenience
margin. Invalid zero-arity targets satisfy the statement vacuously. -/
theorem sectionSixTerminalVStableTargetRegion_convenient_two_mul
    {epsilon delta : Real} {ell M : Nat}
    (region : Set (Fin ell -> Real)) (band : SectionSixStateBand)
    (pattern : SectionSixTerminalVStablePattern ell M) :
    IsTypeIIRegionConvenient (2 * epsilon)
      (sectionSixTerminalVStableTargetRegion
        epsilon delta region band pattern) := by
  let displayedPositions := terminalVDisplayedPositions pattern
  cases band with
  | low =>
      refine ⟨displayedPositions, ?_⟩
      intro x hx
      obtain ⟨hinner, _hresidual, _hsimplex, _hsource, hinnerUpper,
        _hsourceLower, hcutoff, hband⟩ :=
        mem_sectionSixTerminalVStableTargetRegion.mp hx
      rw [sum_terminalVDisplayedPositions pattern x]
      have hfirstUpper := hinnerUpper (⟨0, hinner⟩ : Fin pattern.1.1)
      change x (pattern.firstInnerPosition hinner) <=
        sectionSixThetaGap epsilon at hfirstUpper
      simp only [sectionSixTerminalVCutoffExponent] at hcutoff
      change sectionSixThetaOne epsilon <=
          sectionSixTerminalVDisplayedSum pattern x ∧
        sectionSixTerminalVDisplayedSum pattern x <=
          sectionSixThetaTwo epsilon
      simp only [sectionSixThetaOne, sectionSixThetaTwo, sectionSixThetaGap]
        at hcutoff hfirstUpper hband ⊢
      exact ⟨by linarith [hband.2.2.1], by linarith⟩
  | high =>
      let complementPositions :
          Finset (Fin ((pattern.1.1 + ell) + pattern.2.1.1)) :=
        Finset.univ \ displayedPositions
      refine ⟨complementPositions, ?_⟩
      intro x hx
      obtain ⟨hinner, _hresidual, hsimplex, _hsource, hinnerUpper,
        _hsourceLower, hcutoff, hband⟩ :=
        mem_sectionSixTerminalVStableTargetRegion.mp hx
      have hsumComplement : (∑ j ∈ complementPositions, x j) =
          1 - sectionSixTerminalVDisplayedSum pattern x := by
        rw [show complementPositions = Finset.univ \ displayedPositions by rfl,
          Finset.sum_sdiff_eq_sub (Finset.subset_univ displayedPositions)]
        rw [hsimplex.2.2, sum_terminalVDisplayedPositions pattern x]
      rw [hsumComplement]
      have hfirstUpper := hinnerUpper (⟨0, hinner⟩ : Fin pattern.1.1)
      change x (pattern.firstInnerPosition hinner) <=
        sectionSixThetaGap epsilon at hfirstUpper
      simp only [sectionSixTerminalVCutoffExponent] at hcutoff
      change sectionSixThetaOne epsilon <=
          1 - sectionSixTerminalVDisplayedSum pattern x ∧
        1 - sectionSixTerminalVDisplayedSum pattern x <=
          sectionSixThetaTwo epsilon
      simp only [sectionSixThetaOne, sectionSixThetaTwo, sectionSixThetaGap]
        at hcutoff hfirstUpper hband ⊢
      exact ⟨by linarith [hcutoff], by linarith [hband.2.2.2.1]⟩

end

end PrimesRestrictedDigits
