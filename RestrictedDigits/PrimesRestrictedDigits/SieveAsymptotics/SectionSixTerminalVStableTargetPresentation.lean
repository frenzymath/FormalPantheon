import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStableTargetRegion
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVFixedNormalFacts
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIAffineMixedOperations
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Mixed affine presentation of terminal-V stable targets

This module presents the exact positive-arity target. The low band has four strict fixed walls
and the high band has five; all simplex, source, range, and upper-cutoff walls remain weak.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private theorem terminalVAffineValue_single
    {d : Nat} (i : Fin d) (a : Real) (x : Fin d -> Real) :
    typeIIAffineValue (Pi.single i a) x = a * x i := by
  classical
  simp [typeIIAffineValue, Pi.single_apply]

private theorem terminalVAffineValue_add
    {d : Nat} (a b x : Fin d -> Real) :
    typeIIAffineValue (a + b) x =
      typeIIAffineValue a x + typeIIAffineValue b x := by
  simp [typeIIAffineValue, add_mul, Finset.sum_add_distrib]

private theorem terminalVAffineValue_sub
    {d : Nat} (a b x : Fin d -> Real) :
    typeIIAffineValue (a - b) x =
      typeIIAffineValue a x - typeIIAffineValue b x := by
  simp [typeIIAffineValue, sub_mul, Finset.sum_sub_distrib]

private theorem terminalVAffineValue_neg
    {d : Nat} (a x : Fin d -> Real) :
    typeIIAffineValue (-a) x = -typeIIAffineValue a x := by
  simp [typeIIAffineValue, Finset.sum_neg_distrib]

private def terminalVWeakFixedRegion
    {ell M : Nat} (epsilon : Real) (band : SectionSixStateBand)
    (pattern : SectionSixTerminalVStablePattern ell M)
    (hinner : 0 < pattern.1.1) :
    Set (Fin ((pattern.1.1 + ell) + pattern.2.1.1) -> Real) :=
  {x | (forall i, x (pattern.innerPositionEmbedding i) <=
        sectionSixThetaGap epsilon) ∧
      (forall i, sectionSixThetaGap epsilon <=
        x (pattern.sourcePositionEmbedding i)) ∧
      sectionSixTerminalVDisplayedSum pattern x <=
        sectionSixTerminalVCutoffExponent epsilon band +
          x (pattern.firstInnerPosition hinner)}

private noncomputable def terminalVWeakFixedPresentation
    {ell M : Nat} (epsilon : Real) (band : SectionSixStateBand)
    (pattern : SectionSixTerminalVStablePattern ell M)
    (hinner : 0 < pattern.1.1) :
    TypeIIAffineHalfspacePresentation
      (terminalVWeakFixedRegion epsilon band pattern hinner) where
  constraintCount := pattern.1.1 + (ell + 1)
  normal := sectionSixTerminalVWeakFixedNormalFamily pattern hinner
  bound := Fin.append (fun _ => sectionSixThetaGap epsilon)
    (Fin.append (fun _ => -sectionSixThetaGap epsilon)
      (fun _ => sectionSixTerminalVCutoffExponent epsilon band))
  mem_iff := by
    intro x
    rw [Fin.forall_fin_add, Fin.forall_fin_add]
    constructor
    · rintro ⟨hinnerUpper, hsourceLower, hcutoff⟩
      refine ⟨?_, ?_⟩
      · intro i
        simpa only [sectionSixTerminalVWeakFixedNormalFamily,
          Fin.append_left, terminalVAffineValue_single,
          one_mul] using hinnerUpper i
      · refine ⟨?_, ?_⟩
        · intro i
          simp only [sectionSixTerminalVWeakFixedNormalFamily,
            Fin.append_right, Fin.append_left,
            terminalVAffineValue_single, neg_one_mul]
          linarith [hsourceLower i]
        · intro j
          fin_cases j
          simp only [sectionSixTerminalVWeakFixedNormalFamily,
            Fin.append_right, terminalVAffineValue_sub,
            sectionSixTerminalVAffineValue_displayedSumNormal,
            terminalVAffineValue_single, one_mul]
          linarith
    · rintro ⟨hinnerUpper, hsourceLower, hcutoff⟩
      refine ⟨?_, ?_⟩
      · intro i
        simpa only [sectionSixTerminalVWeakFixedNormalFamily,
          Fin.append_left, terminalVAffineValue_single,
          one_mul] using hinnerUpper i
      · refine ⟨?_, ?_⟩
        · intro i
          have hi := hsourceLower i
          simp only [sectionSixTerminalVWeakFixedNormalFamily,
            Fin.append_right, Fin.append_left,
            terminalVAffineValue_single, neg_one_mul] at hi
          linarith
        · have h := hcutoff (0 : Fin 1)
          simp only [sectionSixTerminalVWeakFixedNormalFamily,
            Fin.append_right, terminalVAffineValue_sub,
            sectionSixTerminalVAffineValue_displayedSumNormal,
            terminalVAffineValue_single, one_mul] at h
          linarith

private def terminalVLowStrictRegion
    {ell M : Nat} (epsilon delta : Real)
    (pattern : SectionSixTerminalVStablePattern ell M)
    (hinner : 0 < pattern.1.1) (hresidual : 0 < pattern.2.1.1) :
    Set (Fin ((pattern.1.1 + ell) + pattern.2.1.1) -> Real) :=
  {x | sectionSixTerminalVSourceSum pattern x <
          sectionSixThetaOne epsilon ∧
        delta < x (pattern.firstInnerPosition hinner) ∧
        sectionSixThetaOne epsilon <
          sectionSixTerminalVDisplayedSum pattern x ∧
        x (pattern.firstInnerPosition hinner) <
          x (pattern.firstResidualPosition hresidual)}

private noncomputable def terminalVLowStrictPresentation
    {ell M : Nat} (epsilon delta : Real)
    (pattern : SectionSixTerminalVStablePattern ell M)
    (hinner : 0 < pattern.1.1) (hresidual : 0 < pattern.2.1.1) :
    TypeIIAffineMixedPresentation
      (terminalVLowStrictRegion epsilon delta pattern hinner hresidual) where
  constraintCount := 4
  normal := sectionSixTerminalVLowStrictNormalFamily pattern hinner hresidual
  bound := ![sectionSixThetaOne epsilon, -delta,
    -sectionSixThetaOne epsilon, 0]
  isStrict := fun _ => true
  mem_iff := by
    intro x
    constructor
    · rintro ⟨hsource, hq, hdisplayed, hcross⟩ c
      simp only [if_pos]
      fin_cases c
      · simpa [sectionSixTerminalVLowStrictNormalFamily,
          sectionSixTerminalVAffineValue_sourceSumNormal] using hsource
      · simpa [sectionSixTerminalVLowStrictNormalFamily,
          terminalVAffineValue_single] using (neg_lt_neg hq)
      · simpa [sectionSixTerminalVLowStrictNormalFamily,
          terminalVAffineValue_neg,
          sectionSixTerminalVAffineValue_displayedSumNormal] using
            (neg_lt_neg hdisplayed)
      · simpa [sectionSixTerminalVLowStrictNormalFamily,
          terminalVAffineValue_sub, terminalVAffineValue_single] using
          sub_lt_zero.mpr hcross
    · intro h
      have hsource : sectionSixTerminalVSourceSum pattern x <
          sectionSixThetaOne epsilon := by
        simpa [sectionSixTerminalVLowStrictNormalFamily,
          sectionSixTerminalVAffineValue_sourceSumNormal] using h (0 : Fin 4)
      have hq : -x (pattern.firstInnerPosition hinner) < -delta := by
        simpa [sectionSixTerminalVLowStrictNormalFamily,
          terminalVAffineValue_single] using h (1 : Fin 4)
      have hdisplayed : -sectionSixTerminalVDisplayedSum pattern x <
          -sectionSixThetaOne epsilon := by
        simpa [sectionSixTerminalVLowStrictNormalFamily,
          terminalVAffineValue_neg,
          sectionSixTerminalVAffineValue_displayedSumNormal] using h (2 : Fin 4)
      have hcross : x (pattern.firstInnerPosition hinner) -
          x (pattern.firstResidualPosition hresidual) < 0 := by
        simpa [sectionSixTerminalVLowStrictNormalFamily,
          terminalVAffineValue_sub,
          terminalVAffineValue_single] using h (3 : Fin 4)
      exact ⟨hsource, by linarith, by linarith, by linarith⟩

private def terminalVHighStrictRegion
    {ell M : Nat} (epsilon delta : Real)
    (pattern : SectionSixTerminalVStablePattern ell M)
    (hinner : 0 < pattern.1.1) (hresidual : 0 < pattern.2.1.1) :
    Set (Fin ((pattern.1.1 + ell) + pattern.2.1.1) -> Real) :=
  {x | sectionSixThetaTwo epsilon <
          sectionSixTerminalVSourceSum pattern x ∧
        sectionSixTerminalVSourceSum pattern x <
          1 - sectionSixThetaTwo epsilon ∧
        delta < x (pattern.firstInnerPosition hinner) ∧
        1 - sectionSixThetaTwo epsilon <
          sectionSixTerminalVDisplayedSum pattern x ∧
        x (pattern.firstInnerPosition hinner) <
          x (pattern.firstResidualPosition hresidual)}

private noncomputable def terminalVHighStrictPresentation
    {ell M : Nat} (epsilon delta : Real)
    (pattern : SectionSixTerminalVStablePattern ell M)
    (hinner : 0 < pattern.1.1) (hresidual : 0 < pattern.2.1.1) :
    TypeIIAffineMixedPresentation
      (terminalVHighStrictRegion epsilon delta pattern hinner hresidual) where
  constraintCount := 5
  normal := sectionSixTerminalVHighStrictNormalFamily pattern hinner hresidual
  bound := ![-sectionSixThetaTwo epsilon,
    1 - sectionSixThetaTwo epsilon, -delta,
    -(1 - sectionSixThetaTwo epsilon), 0]
  isStrict := fun _ => true
  mem_iff := by
    intro x
    constructor
    · rintro ⟨hsourceLower, hsourceUpper, hq, hdisplayed, hcross⟩ c
      simp only [if_pos]
      fin_cases c
      · simpa [sectionSixTerminalVHighStrictNormalFamily,
          terminalVAffineValue_neg,
          sectionSixTerminalVAffineValue_sourceSumNormal] using
            (neg_lt_neg hsourceLower)
      · simpa [sectionSixTerminalVHighStrictNormalFamily,
          sectionSixTerminalVAffineValue_sourceSumNormal] using hsourceUpper
      · simpa [sectionSixTerminalVHighStrictNormalFamily,
          terminalVAffineValue_single] using (neg_lt_neg hq)
      · simpa [sectionSixTerminalVHighStrictNormalFamily,
          terminalVAffineValue_neg,
          sectionSixTerminalVAffineValue_displayedSumNormal] using
            (neg_lt_neg hdisplayed)
      · simpa [sectionSixTerminalVHighStrictNormalFamily,
          terminalVAffineValue_sub, terminalVAffineValue_single] using
          sub_lt_zero.mpr hcross
    · intro h
      have hsourceLower : -sectionSixTerminalVSourceSum pattern x <
          -sectionSixThetaTwo epsilon := by
        simpa [sectionSixTerminalVHighStrictNormalFamily,
          terminalVAffineValue_neg,
          sectionSixTerminalVAffineValue_sourceSumNormal] using h (0 : Fin 5)
      have hsourceUpper : sectionSixTerminalVSourceSum pattern x <
          1 - sectionSixThetaTwo epsilon := by
        simpa [sectionSixTerminalVHighStrictNormalFamily,
          sectionSixTerminalVAffineValue_sourceSumNormal] using h (1 : Fin 5)
      have hq : -x (pattern.firstInnerPosition hinner) < -delta := by
        simpa [sectionSixTerminalVHighStrictNormalFamily,
          terminalVAffineValue_single] using h (2 : Fin 5)
      have hdisplayed : -sectionSixTerminalVDisplayedSum pattern x <
          -(1 - sectionSixThetaTwo epsilon) := by
        simpa [sectionSixTerminalVHighStrictNormalFamily,
          terminalVAffineValue_neg,
          sectionSixTerminalVAffineValue_displayedSumNormal] using h (3 : Fin 5)
      have hcross : x (pattern.firstInnerPosition hinner) -
          x (pattern.firstResidualPosition hresidual) < 0 := by
        simpa [sectionSixTerminalVHighStrictNormalFamily,
          terminalVAffineValue_sub,
          terminalVAffineValue_single] using h (4 : Fin 5)
      exact ⟨by linarith, hsourceUpper, by linarith, by linarith, by linarith⟩

private theorem terminalVFixedRegion_eq_weak_inter_strict
    {ell M : Nat} (epsilon delta : Real) (band : SectionSixStateBand)
    (pattern : SectionSixTerminalVStablePattern ell M)
    (hinner : 0 < pattern.1.1) (hresidual : 0 < pattern.2.1.1) :
    sectionSixTerminalVFixedRegion epsilon delta band pattern
        hinner hresidual =
      terminalVWeakFixedRegion epsilon band pattern hinner ∩
        match band with
        | .low => terminalVLowStrictRegion epsilon delta pattern
            hinner hresidual
        | .high => terminalVHighStrictRegion epsilon delta pattern
            hinner hresidual := by
  ext x
  cases band
  · simp only [sectionSixTerminalVFixedRegion, terminalVWeakFixedRegion,
      terminalVLowStrictRegion, sectionSixTerminalVCutoffExponent,
      Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨ha, hb, hc, hd, he, hf, hg⟩
      exact ⟨⟨ha, hb, hc⟩, ⟨hd, he, hf, hg⟩⟩
    · rintro ⟨⟨ha, hb, hc⟩, ⟨hd, he, hf, hg⟩⟩
      exact ⟨ha, hb, hc, hd, he, hf, hg⟩
  · simp only [sectionSixTerminalVFixedRegion, terminalVWeakFixedRegion,
      terminalVHighStrictRegion, sectionSixTerminalVCutoffExponent,
      Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨ha, hb, hc, hd, he, hf, hg, hh⟩
      exact ⟨⟨ha, hb, hc⟩, ⟨hd, he, hf, hg, hh⟩⟩
    · rintro ⟨⟨ha, hb, hc⟩, ⟨hd, he, hf, hg, hh⟩⟩
      exact ⟨ha, hb, hc, hd, he, hf, hg, hh⟩

/-- Exact mixed presentation of the terminal-V fixed walls. -/
noncomputable def sectionSixTerminalVFixedPresentation
    {ell M : Nat} (epsilon delta : Real) (band : SectionSixStateBand)
    (pattern : SectionSixTerminalVStablePattern ell M)
    (hinner : 0 < pattern.1.1) (hresidual : 0 < pattern.2.1.1) :
    TypeIIAffineMixedPresentation
      (sectionSixTerminalVFixedRegion epsilon delta band pattern
        hinner hresidual) := by
  cases band with
  | low =>
      let presentation :=
        (terminalVWeakFixedPresentation epsilon .low pattern hinner).toMixed.inter
          (terminalVLowStrictPresentation epsilon delta pattern
            hinner hresidual)
      exact
        { constraintCount := presentation.constraintCount
          normal := presentation.normal
          bound := presentation.bound
          isStrict := presentation.isStrict
          mem_iff := by
            intro x
            rw [terminalVFixedRegion_eq_weak_inter_strict]
            exact presentation.mem_iff x }
  | high =>
      let presentation :=
        (terminalVWeakFixedPresentation epsilon .high pattern hinner).toMixed.inter
          (terminalVHighStrictPresentation epsilon delta pattern
            hinner hresidual)
      exact
        { constraintCount := presentation.constraintCount
          normal := presentation.normal
          bound := presentation.bound
          isStrict := presentation.isStrict
          mem_iff := by
            intro x
            rw [terminalVFixedRegion_eq_weak_inter_strict]
            exact presentation.mem_iff x }

/-- Total constraint count of the fixed presentation, including its weak
coordinate and cutoff walls. -/
theorem sectionSixTerminalVFixedPresentation_constraintCount
    {ell M : Nat} (epsilon delta : Real) (band : SectionSixStateBand)
    (pattern : SectionSixTerminalVStablePattern ell M)
    (hinner : 0 < pattern.1.1) (hresidual : 0 < pattern.2.1.1) :
    (sectionSixTerminalVFixedPresentation epsilon delta band pattern
      hinner hresidual).constraintCount =
        pattern.1.1 + (ell + 1) +
          match band with
          | .low => 4
          | .high => 5 := by
  cases band <;> rfl

/-- The three closed fixed-wall inequalities used by the terminal convenience
argument are retained by the forward half of the mixed presentation. -/
theorem sectionSixTerminalVFixedPresentation_forward_convenienceBounds
    {ell M : Nat} (epsilon delta : Real) (band : SectionSixStateBand)
    (pattern : SectionSixTerminalVStablePattern ell M)
    (hinner : 0 < pattern.1.1) (hresidual : 0 < pattern.2.1.1)
    (x : Fin ((pattern.1.1 + ell) + pattern.2.1.1) -> Real)
    (hforward : forall c,
      typeIIAffineValue
          ((sectionSixTerminalVFixedPresentation epsilon delta band pattern
            hinner hresidual).normal c) x <=
        (sectionSixTerminalVFixedPresentation epsilon delta band pattern
          hinner hresidual).bound c) :
    x (pattern.firstInnerPosition hinner) <= sectionSixThetaGap epsilon ∧
      sectionSixTerminalVDisplayedSum pattern x <=
        sectionSixTerminalVCutoffExponent epsilon band +
          x (pattern.firstInnerPosition hinner) ∧
      (match band with
        | .low => sectionSixThetaOne epsilon
        | .high => 1 - sectionSixThetaTwo epsilon) <=
          sectionSixTerminalVDisplayedSum pattern x := by
  cases band with
  | low =>
      have hinnerUpper := hforward
        (Fin.castAdd 4 (Fin.castAdd (ell + 1)
          (⟨0, hinner⟩ : Fin pattern.1.1)))
      have hcutoff := hforward (Fin.castAdd 4
        (Fin.natAdd pattern.1.1 (Fin.natAdd ell (0 : Fin 1))))
      have hdisplayedLower := hforward
        (Fin.natAdd (pattern.1.1 + (ell + 1)) (2 : Fin 4))
      simp only [sectionSixTerminalVFixedPresentation,
        TypeIIAffineMixedPresentation.inter,
        terminalVWeakFixedPresentation, terminalVLowStrictPresentation,
        TypeIIAffineHalfspacePresentation.toMixed,
        sectionSixTerminalVWeakFixedNormalFamily,
        sectionSixTerminalVLowStrictNormalFamily,
        Fin.append_left, Fin.append_right,
        terminalVAffineValue_single, terminalVAffineValue_sub,
        sectionSixTerminalVAffineValue_displayedSumNormal,
        one_mul] at hinnerUpper hcutoff hdisplayedLower
      simp [terminalVAffineValue_neg,
        sectionSixTerminalVAffineValue_displayedSumNormal] at hdisplayedLower
      simp only [sectionSixTerminalVCutoffExponent] at hcutoff ⊢
      exact ⟨hinnerUpper, by linarith, by linarith⟩
  | high =>
      have hinnerUpper := hforward
        (Fin.castAdd 5 (Fin.castAdd (ell + 1)
          (⟨0, hinner⟩ : Fin pattern.1.1)))
      have hcutoff := hforward (Fin.castAdd 5
        (Fin.natAdd pattern.1.1 (Fin.natAdd ell (0 : Fin 1))))
      have hdisplayedLower := hforward
        (Fin.natAdd (pattern.1.1 + (ell + 1)) (3 : Fin 5))
      simp only [sectionSixTerminalVFixedPresentation,
        TypeIIAffineMixedPresentation.inter,
        terminalVWeakFixedPresentation, terminalVHighStrictPresentation,
        TypeIIAffineHalfspacePresentation.toMixed,
        sectionSixTerminalVWeakFixedNormalFamily,
        sectionSixTerminalVHighStrictNormalFamily,
        Fin.append_left, Fin.append_right,
        terminalVAffineValue_single, terminalVAffineValue_sub,
        sectionSixTerminalVAffineValue_displayedSumNormal,
        one_mul] at hinnerUpper hcutoff hdisplayedLower
      simp [terminalVAffineValue_neg,
        sectionSixTerminalVAffineValue_displayedSumNormal] at hdisplayedLower
      simp only [sectionSixTerminalVCutoffExponent] at hcutoff ⊢
      exact ⟨hinnerUpper, by linarith, by linarith⟩
private theorem terminalVCardFinAppendFalseTrue (n k : Nat) :
    ((Finset.univ : Finset (Fin (n + k))).filter fun c =>
      Fin.append (fun _ : Fin n => false) (fun _ : Fin k => true) c).card = k := by
  rw [Finset.card_filter, Fin.sum_univ_add]
  simp

/-- The fixed presentation has exactly four strict walls in the low band and
five in the high band. -/
theorem sectionSixTerminalVFixedPresentation_strictIndices_card
    {ell M : Nat} (epsilon delta : Real) (band : SectionSixStateBand)
    (pattern : SectionSixTerminalVStablePattern ell M)
    (hinner : 0 < pattern.1.1) (hresidual : 0 < pattern.2.1.1) :
    (sectionSixTerminalVFixedPresentation epsilon delta band pattern
      hinner hresidual).strictIndices.card =
        match band with
        | .low => 4
        | .high => 5 := by
  cases band <;>
    simp [sectionSixTerminalVFixedPresentation,
      TypeIIAffineMixedPresentation.strictIndices,
      TypeIIAffineMixedPresentation.inter,
      TypeIIAffineHalfspacePresentation.toMixed,
      terminalVLowStrictPresentation, terminalVHighStrictPresentation]
    <;> apply terminalVCardFinAppendFalseTrue

/-- Every nonzero fixed terminal-V wall is nonconstant, witnessed against
the first residual coefficient. -/
theorem sectionSixTerminalVFixedPresentation_normal_nonconstant
    {ell M : Nat} (epsilon delta : Real) (band : SectionSixStateBand)
    (pattern : SectionSixTerminalVStablePattern ell M)
    (hinner : 0 < pattern.1.1) (hresidual : 0 < pattern.2.1.1)
    (j : Fin (sectionSixTerminalVFixedPresentation epsilon delta band pattern
      hinner hresidual).constraintCount)
    (hnormal : (sectionSixTerminalVFixedPresentation epsilon delta band pattern
      hinner hresidual).normal j ≠ 0) :
    ∃ i, (sectionSixTerminalVFixedPresentation epsilon delta band pattern
        hinner hresidual).normal j i ≠
      (sectionSixTerminalVFixedPresentation epsilon delta band pattern
        hinner hresidual).normal j
        (pattern.firstResidualPosition hresidual) := by
  cases band with
  | low =>
      unfold sectionSixTerminalVFixedPresentation at hnormal ⊢
      dsimp only at hnormal ⊢
      unfold TypeIIAffineMixedPresentation.inter at hnormal ⊢
      dsimp only at hnormal ⊢
      cases j using Fin.addCases with
      | left j =>
          rw [Fin.append_left] at hnormal ⊢
          exact sectionSixTerminalVWeakFixedNormalFamily_normal_nonconstant
            pattern hinner hresidual j hnormal
      | right j =>
          rw [Fin.append_right] at hnormal ⊢
          exact sectionSixTerminalVLowStrictNormalFamily_normal_nonconstant
            pattern hinner hresidual j hnormal
  | high =>
      unfold sectionSixTerminalVFixedPresentation at hnormal ⊢
      dsimp only at hnormal ⊢
      unfold TypeIIAffineMixedPresentation.inter at hnormal ⊢
      dsimp only at hnormal ⊢
      cases j using Fin.addCases with
      | left j =>
          rw [Fin.append_left] at hnormal ⊢
          exact sectionSixTerminalVWeakFixedNormalFamily_normal_nonconstant
            pattern hinner hresidual j hnormal
      | right j =>
          rw [Fin.append_right] at hnormal ⊢
          exact sectionSixTerminalVHighStrictNormalFamily_normal_nonconstant
            pattern hinner hresidual j hnormal

/-- Exact mixed presentation of the positive-arity terminal-V target core. -/
noncomputable def sectionSixTerminalVStableTargetPositivePresentation
    {ell M : Nat} {sourceRegion : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation sourceRegion)
    (epsilon delta : Real) (band : SectionSixStateBand)
    (pattern : SectionSixTerminalVStablePattern ell M)
    (hinner : 0 < pattern.1.1) (hresidual : 0 < pattern.2.1.1) :
    TypeIIAffineMixedPresentation
      (typeIIExponentSimplex delta ∩
        (typeIIAffineEmbeddingPreimageRegion
            pattern.sourcePositionEmbedding sourceRegion ∩
          sectionSixTerminalVFixedRegion epsilon delta band pattern
            hinner hresidual)) :=
  (typeIIExponentSimplexPresentationRaw delta (by omega)).toMixed.inter
    ((sourcePresentation.toMixed.liftAlongEmbedding
      pattern.sourcePositionEmbedding).inter
        (sectionSixTerminalVFixedPresentation epsilon delta band pattern
          hinner hresidual))

/-- Exact mixed presentation of the public total target under the positive
arity witnesses required by its terminal walls. -/
noncomputable def sectionSixTerminalVStableTargetPresentation
    {ell M : Nat} {sourceRegion : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation sourceRegion)
    (epsilon delta : Real) (band : SectionSixStateBand)
    (pattern : SectionSixTerminalVStablePattern ell M)
    (hinner : 0 < pattern.1.1) (hresidual : 0 < pattern.2.1.1) :
    TypeIIAffineMixedPresentation
      (sectionSixTerminalVStableTargetRegion
        epsilon delta sourceRegion band pattern) := by
  rw [sectionSixTerminalVStableTargetRegion_eq_positiveCore hinner hresidual]
  exact sectionSixTerminalVStableTargetPositivePresentation sourcePresentation
    epsilon delta band pattern hinner hresidual

end

end PrimesRestrictedDigits
