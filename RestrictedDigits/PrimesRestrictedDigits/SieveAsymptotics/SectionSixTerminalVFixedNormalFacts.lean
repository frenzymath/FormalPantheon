import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStableTargetRegion
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Normal geometry of the fixed terminal-V presentation

This file exposes the literal normal families used by the terminal-V fixed presentation.
Positive residual arity supplies a comparison coordinate outside every displayed embedding,
and every nonzero literal differs from its coefficient at that coordinate.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The coefficient-one normal supported on the range of an embedding. -/
noncomputable def sectionSixTerminalVEmbeddingSumNormal {s d : Nat}
    (embedding : Fin s ↪ Fin d) : Fin d -> Real :=
  typeIIAffineLiftNormal embedding (fun _ => 1)

/-- The coefficient-one normal on the source-labelled coordinates. -/
noncomputable def sectionSixTerminalVSourceSumNormal {ell M : Nat}
    (pattern : SectionSixTerminalVStablePattern ell M) :
    Fin ((pattern.1.1 + ell) + pattern.2.1.1) -> Real :=
  sectionSixTerminalVEmbeddingSumNormal pattern.sourcePositionEmbedding

/-- The coefficient-one normal on the accumulated-inner coordinates. -/
noncomputable def sectionSixTerminalVInnerSumNormal {ell M : Nat}
    (pattern : SectionSixTerminalVStablePattern ell M) :
    Fin ((pattern.1.1 + ell) + pattern.2.1.1) -> Real :=
  sectionSixTerminalVEmbeddingSumNormal pattern.innerPositionEmbedding

/-- The coefficient-one normal on every displayed source or inner coordinate. -/
noncomputable def sectionSixTerminalVDisplayedSumNormal {ell M : Nat}
    (pattern : SectionSixTerminalVStablePattern ell M) :
    Fin ((pattern.1.1 + ell) + pattern.2.1.1) -> Real :=
  sectionSixTerminalVSourceSumNormal pattern +
    sectionSixTerminalVInnerSumNormal pattern

/-- Evaluating an embedded coefficient-one normal sums the embedded
coordinates. -/
theorem sectionSixTerminalVAffineValue_embeddingSumNormal
    {s d : Nat} (embedding : Fin s ↪ Fin d) (x : Fin d -> Real) :
    typeIIAffineValue (sectionSixTerminalVEmbeddingSumNormal embedding) x =
      ∑ i, x (embedding i) := by
  rw [sectionSixTerminalVEmbeddingSumNormal, typeIIAffineValue_liftNormal]
  simp [typeIIAffineValue]

/-- The source sum is represented by its literal affine normal. -/
theorem sectionSixTerminalVAffineValue_sourceSumNormal
    {ell M : Nat} (pattern : SectionSixTerminalVStablePattern ell M)
    (x : Fin ((pattern.1.1 + ell) + pattern.2.1.1) -> Real) :
    typeIIAffineValue (sectionSixTerminalVSourceSumNormal pattern) x =
      sectionSixTerminalVSourceSum pattern x := by
  exact sectionSixTerminalVAffineValue_embeddingSumNormal
    pattern.sourcePositionEmbedding x

/-- The inner sum is represented by its literal affine normal. -/
theorem sectionSixTerminalVAffineValue_innerSumNormal
    {ell M : Nat} (pattern : SectionSixTerminalVStablePattern ell M)
    (x : Fin ((pattern.1.1 + ell) + pattern.2.1.1) -> Real) :
    typeIIAffineValue (sectionSixTerminalVInnerSumNormal pattern) x =
      sectionSixTerminalVInnerSum pattern x := by
  exact sectionSixTerminalVAffineValue_embeddingSumNormal
    pattern.innerPositionEmbedding x

/-- The displayed sum is represented by its literal affine normal. -/
theorem sectionSixTerminalVAffineValue_displayedSumNormal
    {ell M : Nat} (pattern : SectionSixTerminalVStablePattern ell M)
    (x : Fin ((pattern.1.1 + ell) + pattern.2.1.1) -> Real) :
    typeIIAffineValue (sectionSixTerminalVDisplayedSumNormal pattern) x =
      sectionSixTerminalVDisplayedSum pattern x := by
  rw [sectionSixTerminalVDisplayedSumNormal]
  rw [show typeIIAffineValue
      (sectionSixTerminalVSourceSumNormal pattern +
        sectionSixTerminalVInnerSumNormal pattern) x =
      typeIIAffineValue (sectionSixTerminalVSourceSumNormal pattern) x +
        typeIIAffineValue (sectionSixTerminalVInnerSumNormal pattern) x by
      simp [typeIIAffineValue, add_mul, Finset.sum_add_distrib]]
  rw [
    sectionSixTerminalVAffineValue_sourceSumNormal,
    sectionSixTerminalVAffineValue_innerSumNormal]
  rfl

/-- Literal normal family for the weak fixed coordinate and cutoff walls. -/
noncomputable def sectionSixTerminalVWeakFixedNormalFamily
    {ell M : Nat} (pattern : SectionSixTerminalVStablePattern ell M)
    (hinner : 0 < pattern.1.1) :
    Fin (pattern.1.1 + (ell + 1)) ->
      Fin ((pattern.1.1 + ell) + pattern.2.1.1) -> Real :=
  Fin.append
    (fun i => Pi.single (pattern.innerPositionEmbedding i) 1)
    (Fin.append
      (fun i => Pi.single (pattern.sourcePositionEmbedding i) (-1))
      (fun _ => sectionSixTerminalVDisplayedSumNormal pattern -
        Pi.single (pattern.firstInnerPosition hinner) 1))

/-- Literal normal family for the four strict low-band walls. -/
noncomputable def sectionSixTerminalVLowStrictNormalFamily
    {ell M : Nat} (pattern : SectionSixTerminalVStablePattern ell M)
    (hinner : 0 < pattern.1.1) (hresidual : 0 < pattern.2.1.1) :
    Fin 4 -> Fin ((pattern.1.1 + ell) + pattern.2.1.1) -> Real :=
  ![sectionSixTerminalVSourceSumNormal pattern,
    Pi.single (pattern.firstInnerPosition hinner) (-1),
    -sectionSixTerminalVDisplayedSumNormal pattern,
    Pi.single (pattern.firstInnerPosition hinner) 1 -
      Pi.single (pattern.firstResidualPosition hresidual) 1]

/-- Literal normal family for the five strict high-band walls. -/
noncomputable def sectionSixTerminalVHighStrictNormalFamily
    {ell M : Nat} (pattern : SectionSixTerminalVStablePattern ell M)
    (hinner : 0 < pattern.1.1) (hresidual : 0 < pattern.2.1.1) :
    Fin 5 -> Fin ((pattern.1.1 + ell) + pattern.2.1.1) -> Real :=
  ![-sectionSixTerminalVSourceSumNormal pattern,
    sectionSixTerminalVSourceSumNormal pattern,
    Pi.single (pattern.firstInnerPosition hinner) (-1),
    -sectionSixTerminalVDisplayedSumNormal pattern,
    Pi.single (pattern.firstInnerPosition hinner) 1 -
      Pi.single (pattern.firstResidualPosition hresidual) 1]

/-- The first residual coordinate is outside the complete displayed range. -/
theorem sectionSixTerminalVFirstResidual_not_mem_displayedRange
    {ell M : Nat} (pattern : SectionSixTerminalVStablePattern ell M)
    (hresidual : 0 < pattern.2.1.1) :
    pattern.firstResidualPosition hresidual ∉ Set.range pattern.2.2 := by
  rw [← mem_range_typeIIComplementPositionEmbedding_iff pattern.2.2]
  exact ⟨⟨0, hresidual⟩, rfl⟩

/-- The first residual coordinate is outside the inner-labelled range. -/
theorem sectionSixTerminalVFirstResidual_not_mem_innerRange
    {ell M : Nat} (pattern : SectionSixTerminalVStablePattern ell M)
    (hresidual : 0 < pattern.2.1.1) :
    pattern.firstResidualPosition hresidual ∉
      Set.range pattern.innerPositionEmbedding := by
  rintro ⟨i, hi⟩
  exact sectionSixTerminalVFirstResidual_not_mem_displayedRange pattern hresidual
    ⟨Fin.castAdd ell i, hi⟩

/-- The first residual coordinate is outside the source-labelled range. -/
theorem sectionSixTerminalVFirstResidual_not_mem_sourceRange
    {ell M : Nat} (pattern : SectionSixTerminalVStablePattern ell M)
    (hresidual : 0 < pattern.2.1.1) :
    pattern.firstResidualPosition hresidual ∉
      Set.range pattern.sourcePositionEmbedding := by
  rintro ⟨i, hi⟩
  exact sectionSixTerminalVFirstResidual_not_mem_displayedRange pattern hresidual
    ⟨Fin.natAdd pattern.1.1 i, hi⟩

/-- The first inner and first residual coordinates are distinct. -/
theorem sectionSixTerminalVFirstInner_ne_firstResidual
    {ell M : Nat} (pattern : SectionSixTerminalVStablePattern ell M)
    (hinner : 0 < pattern.1.1) (hresidual : 0 < pattern.2.1.1) :
    pattern.firstInnerPosition hinner ≠
      pattern.firstResidualPosition hresidual := by
  intro heq
  exact sectionSixTerminalVFirstResidual_not_mem_displayedRange pattern hresidual
    ⟨Fin.castAdd ell (⟨0, hinner⟩ : Fin pattern.1.1), heq⟩

private theorem terminalVSingle_apply_eq_zero_of_not_mem_range
    {s d : Nat} (embedding : Fin s ↪ Fin d) (a : Real) (i : Fin s)
    {z : Fin d} (hz : z ∉ Set.range embedding) :
    (Pi.single (embedding i) a : Fin d -> Real) z = 0 := by
  classical
  rw [Pi.single_apply]
  split
  · next heq => exact (hz ⟨i, heq.symm⟩).elim
  · rfl

private theorem terminalVNonconstant_at_of_apply_eq_zero
    {d : Nat} {normal : Fin d -> Real} {z : Fin d}
    (hnormal : normal ≠ 0) (hz : normal z = 0) :
    ∃ i, normal i ≠ normal z := by
  by_contra hnone
  apply hnormal
  funext i
  have hi : normal i = normal z := not_exists.mp hnone i |> not_ne_iff.mp
  exact hi.trans hz

private theorem terminalVEmbeddingSumNormal_apply_firstResidual_eq_zero
    {s d : Nat} (embedding : Fin s ↪ Fin d) {z : Fin d}
    (hz : z ∉ Set.range embedding) :
    sectionSixTerminalVEmbeddingSumNormal embedding z = 0 :=
  typeIIAffineLiftNormal_apply_of_not_mem_range embedding (fun _ => 1) hz

/-- Every weak fixed normal vanishes at the first residual coordinate. -/
theorem sectionSixTerminalVWeakFixedNormalFamily_apply_firstResidual_eq_zero
    {ell M : Nat} (pattern : SectionSixTerminalVStablePattern ell M)
    (hinner : 0 < pattern.1.1) (hresidual : 0 < pattern.2.1.1)
    (j : Fin (pattern.1.1 + (ell + 1))) :
    sectionSixTerminalVWeakFixedNormalFamily pattern hinner j
        (pattern.firstResidualPosition hresidual) = 0 := by
  unfold sectionSixTerminalVWeakFixedNormalFamily
  cases j using Fin.addCases with
  | left i =>
      simpa only [Fin.append_left] using
        terminalVSingle_apply_eq_zero_of_not_mem_range
          pattern.innerPositionEmbedding 1 i
          (sectionSixTerminalVFirstResidual_not_mem_innerRange pattern hresidual)
  | right j =>
      cases j using Fin.addCases with
      | left i =>
          simpa only [Fin.append_right, Fin.append_left] using
            terminalVSingle_apply_eq_zero_of_not_mem_range
              pattern.sourcePositionEmbedding (-1) i
              (sectionSixTerminalVFirstResidual_not_mem_sourceRange
                pattern hresidual)
      | right i =>
          fin_cases i
          rw [Fin.append_right, Fin.append_right, Pi.sub_apply,
            sectionSixTerminalVDisplayedSumNormal, Pi.add_apply,
            sectionSixTerminalVSourceSumNormal,
            sectionSixTerminalVInnerSumNormal,
            terminalVEmbeddingSumNormal_apply_firstResidual_eq_zero,
            terminalVEmbeddingSumNormal_apply_firstResidual_eq_zero]
          · have hsingle :
                (Pi.single (pattern.firstInnerPosition hinner) 1 :
                  Fin ((pattern.1.1 + ell) + pattern.2.1.1) -> Real)
                    (pattern.firstResidualPosition hresidual) = 0 :=
                terminalVSingle_apply_eq_zero_of_not_mem_range
                  pattern.innerPositionEmbedding 1
                  (⟨0, hinner⟩ : Fin pattern.1.1)
                  (sectionSixTerminalVFirstResidual_not_mem_innerRange
                    pattern hresidual)
            rw [hsingle]
            norm_num
          · exact sectionSixTerminalVFirstResidual_not_mem_innerRange
              pattern hresidual
          · exact sectionSixTerminalVFirstResidual_not_mem_sourceRange
              pattern hresidual

/-- Every nonzero weak fixed normal is nonconstant, witnessed against the
first residual coefficient. -/
theorem sectionSixTerminalVWeakFixedNormalFamily_normal_nonconstant
    {ell M : Nat} (pattern : SectionSixTerminalVStablePattern ell M)
    (hinner : 0 < pattern.1.1) (hresidual : 0 < pattern.2.1.1)
    (j : Fin (pattern.1.1 + (ell + 1)))
    (hnormal : sectionSixTerminalVWeakFixedNormalFamily pattern hinner j ≠ 0) :
    ∃ i, sectionSixTerminalVWeakFixedNormalFamily pattern hinner j i ≠
      sectionSixTerminalVWeakFixedNormalFamily pattern hinner j
        (pattern.firstResidualPosition hresidual) :=
  terminalVNonconstant_at_of_apply_eq_zero hnormal
    (sectionSixTerminalVWeakFixedNormalFamily_apply_firstResidual_eq_zero
      pattern hinner hresidual j)

/-- Every nonzero low strict normal is nonconstant, witnessed against the
first residual coefficient. -/
theorem sectionSixTerminalVLowStrictNormalFamily_normal_nonconstant
    {ell M : Nat} (pattern : SectionSixTerminalVStablePattern ell M)
    (hinner : 0 < pattern.1.1) (hresidual : 0 < pattern.2.1.1)
    (j : Fin 4)
    (hnormal : sectionSixTerminalVLowStrictNormalFamily pattern hinner
      hresidual j ≠ 0) :
    ∃ i, sectionSixTerminalVLowStrictNormalFamily pattern hinner hresidual j i ≠
      sectionSixTerminalVLowStrictNormalFamily pattern hinner hresidual j
        (pattern.firstResidualPosition hresidual) := by
  unfold sectionSixTerminalVLowStrictNormalFamily at hnormal ⊢
  fin_cases j
  · apply terminalVNonconstant_at_of_apply_eq_zero hnormal
    change sectionSixTerminalVSourceSumNormal pattern
      (pattern.firstResidualPosition hresidual) = 0
    exact terminalVEmbeddingSumNormal_apply_firstResidual_eq_zero _
      (sectionSixTerminalVFirstResidual_not_mem_sourceRange pattern hresidual)
  · apply terminalVNonconstant_at_of_apply_eq_zero hnormal
    exact terminalVSingle_apply_eq_zero_of_not_mem_range
      pattern.innerPositionEmbedding (-1) (⟨0, hinner⟩ : Fin pattern.1.1)
      (sectionSixTerminalVFirstResidual_not_mem_innerRange pattern hresidual)
  · apply terminalVNonconstant_at_of_apply_eq_zero hnormal
    change (-sectionSixTerminalVDisplayedSumNormal pattern)
      (pattern.firstResidualPosition hresidual) = 0
    rw [Pi.neg_apply, sectionSixTerminalVDisplayedSumNormal, Pi.add_apply,
      sectionSixTerminalVSourceSumNormal, sectionSixTerminalVInnerSumNormal,
      terminalVEmbeddingSumNormal_apply_firstResidual_eq_zero,
      terminalVEmbeddingSumNormal_apply_firstResidual_eq_zero]
    · norm_num
    · exact sectionSixTerminalVFirstResidual_not_mem_innerRange pattern hresidual
    · exact sectionSixTerminalVFirstResidual_not_mem_sourceRange pattern hresidual
  · refine ⟨pattern.firstInnerPosition hinner, ?_⟩
    classical
    change ((Pi.single (pattern.firstInnerPosition hinner) 1 -
        Pi.single (pattern.firstResidualPosition hresidual) 1) :
          Fin ((pattern.1.1 + ell) + pattern.2.1.1) -> Real)
          (pattern.firstInnerPosition hinner) ≠
      ((Pi.single (pattern.firstInnerPosition hinner) 1 -
        Pi.single (pattern.firstResidualPosition hresidual) 1) :
          Fin ((pattern.1.1 + ell) + pattern.2.1.1) -> Real)
          (pattern.firstResidualPosition hresidual)
    simp [sectionSixTerminalVFirstInner_ne_firstResidual pattern hinner hresidual]
    norm_num

/-- Every nonzero high strict normal is nonconstant, witnessed against the
first residual coefficient. -/
theorem sectionSixTerminalVHighStrictNormalFamily_normal_nonconstant
    {ell M : Nat} (pattern : SectionSixTerminalVStablePattern ell M)
    (hinner : 0 < pattern.1.1) (hresidual : 0 < pattern.2.1.1)
    (j : Fin 5)
    (hnormal : sectionSixTerminalVHighStrictNormalFamily pattern hinner
      hresidual j ≠ 0) :
    ∃ i, sectionSixTerminalVHighStrictNormalFamily pattern hinner hresidual j i ≠
      sectionSixTerminalVHighStrictNormalFamily pattern hinner hresidual j
        (pattern.firstResidualPosition hresidual) := by
  unfold sectionSixTerminalVHighStrictNormalFamily at hnormal ⊢
  fin_cases j
  · apply terminalVNonconstant_at_of_apply_eq_zero hnormal
    change (-sectionSixTerminalVSourceSumNormal pattern)
      (pattern.firstResidualPosition hresidual) = 0
    rw [Pi.neg_apply, sectionSixTerminalVSourceSumNormal,
      terminalVEmbeddingSumNormal_apply_firstResidual_eq_zero]
    · norm_num
    · exact sectionSixTerminalVFirstResidual_not_mem_sourceRange pattern hresidual
  · apply terminalVNonconstant_at_of_apply_eq_zero hnormal
    change sectionSixTerminalVSourceSumNormal pattern
      (pattern.firstResidualPosition hresidual) = 0
    exact terminalVEmbeddingSumNormal_apply_firstResidual_eq_zero _
      (sectionSixTerminalVFirstResidual_not_mem_sourceRange pattern hresidual)
  · apply terminalVNonconstant_at_of_apply_eq_zero hnormal
    exact terminalVSingle_apply_eq_zero_of_not_mem_range
      pattern.innerPositionEmbedding (-1) (⟨0, hinner⟩ : Fin pattern.1.1)
      (sectionSixTerminalVFirstResidual_not_mem_innerRange pattern hresidual)
  · apply terminalVNonconstant_at_of_apply_eq_zero hnormal
    change (-sectionSixTerminalVDisplayedSumNormal pattern)
      (pattern.firstResidualPosition hresidual) = 0
    rw [Pi.neg_apply, sectionSixTerminalVDisplayedSumNormal, Pi.add_apply,
      sectionSixTerminalVSourceSumNormal, sectionSixTerminalVInnerSumNormal,
      terminalVEmbeddingSumNormal_apply_firstResidual_eq_zero,
      terminalVEmbeddingSumNormal_apply_firstResidual_eq_zero]
    · norm_num
    · exact sectionSixTerminalVFirstResidual_not_mem_innerRange pattern hresidual
    · exact sectionSixTerminalVFirstResidual_not_mem_sourceRange pattern hresidual
  · refine ⟨pattern.firstInnerPosition hinner, ?_⟩
    classical
    change ((Pi.single (pattern.firstInnerPosition hinner) 1 -
        Pi.single (pattern.firstResidualPosition hresidual) 1) :
          Fin ((pattern.1.1 + ell) + pattern.2.1.1) -> Real)
          (pattern.firstInnerPosition hinner) ≠
      ((Pi.single (pattern.firstInnerPosition hinner) 1 -
        Pi.single (pattern.firstResidualPosition hresidual) 1) :
          Fin ((pattern.1.1 + ell) + pattern.2.1.1) -> Real)
          (pattern.firstResidualPosition hresidual)
    simp [sectionSixTerminalVFirstInner_ne_firstResidual pattern hinner hresidual]
    norm_num

end

end PrimesRestrictedDigits
