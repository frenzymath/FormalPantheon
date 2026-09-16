import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStablePatterns
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIEmbeddedAffineNormal
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIExponentSimplexPresentation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Direct stable-pattern target regions

One fixed stable-position pattern turns the displayed direct constraints into a closed region
on the complete normalized factor tuple. The complete region is defined directly in the `Fin
(k + 1)` coordinates consumed by Proposition 7.2. Source: proof of Lemma 7.3 in
`MAYNARD-PRD-PUBLISHED`, pp. 149--152.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private noncomputable def directTargetPresentationInter
    {d : Nat} {left right : Set (Fin d -> Real)}
    (leftPresentation : TypeIIAffineHalfspacePresentation left)
    (rightPresentation : TypeIIAffineHalfspacePresentation right) :
    TypeIIAffineHalfspacePresentation (left ∩ right) where
  constraintCount := leftPresentation.constraintCount +
    rightPresentation.constraintCount
  normal := Fin.append leftPresentation.normal rightPresentation.normal
  bound := Fin.append leftPresentation.bound rightPresentation.bound
  mem_iff := by
    intro x
    rw [Set.mem_inter_iff, leftPresentation.mem_iff,
      rightPresentation.mem_iff, Fin.forall_fin_add]
    constructor
    · rintro ⟨hleft, hright⟩
      exact ⟨fun i => by simpa only [Fin.append_left] using hleft i,
        fun i => by simpa only [Fin.append_right] using hright i⟩
    · rintro ⟨hleft, hright⟩
      exact ⟨fun i => by simpa only [Fin.append_left] using hleft i,
        fun i => by simpa only [Fin.append_right] using hright i⟩

private theorem directTargetAffineValue_single
    {d : Nat} (i : Fin d) (a : Real) (x : Fin d -> Real) :
    typeIIAffineValue (Pi.single i a) x = a * x i := by
  classical
  simp [typeIIAffineValue, Pi.single_apply]

private theorem directTargetAffineValue_sub_single
    {d : Nat} (i j : Fin d) (x : Fin d -> Real) :
    typeIIAffineValue (Pi.single i 1 - Pi.single j 1) x = x i - x j := by
  rw [typeIIAffineValue]
  simp_rw [Pi.sub_apply, sub_mul]
  rw [Finset.sum_sub_distrib]
  simp [Pi.single_apply]

/--
Reassociate a stored displayed-position embedding to `k+1` coordinate convention without
changing any numeric position.
-/
def SectionSixDirectStablePattern.canonicalDisplayedEmbedding
    {ell M : Nat} (pattern : SectionSixDirectStablePattern ell M) :
    Fin (ell + 1) ↪ Fin ((ell + pattern.1.1) + 1) :=
  pattern.2.trans
    (Fin.castOrderIso
      (Nat.add_right_comm ell 1 pattern.1.1)).toEquiv.toEmbedding

private def sectionSixDirectDisplayedSourceEmbedding (ell : Nat) :
    Fin ell ↪ Fin (ell + 1) where
  toFun := Fin.succ
  inj' := Fin.succ_injective ell

private def sectionSixDirectBandLower
    (epsilon : Real) (band : SectionSixDirectBand) : Real :=
  match band with
  | .first => sectionSixThetaOne epsilon
  | .second => 1 - sectionSixThetaTwo epsilon

private def sectionSixDirectBandUpper
    (epsilon : Real) (band : SectionSixDirectBand) : Real :=
  match band with
  | .first => sectionSixThetaTwo epsilon
  | .second => 1 - sectionSixThetaOne epsilon

private def sectionSixDirectDisplayedSourceSumNormal
    {ell : Nat} (a : Real) : Fin (ell + 1) -> Real :=
  Fin.cases 0 (fun _ => a)

private theorem directTargetAffineValue_displayedSourceSumNormal
    {ell : Nat} (a : Real) (x : Fin (ell + 1) -> Real) :
    typeIIAffineValue (sectionSixDirectDisplayedSourceSumNormal a) x =
      a * ∑ i : Fin ell, x i.succ := by
  rw [typeIIAffineValue, Fin.sum_univ_succ]
  simp only [sectionSixDirectDisplayedSourceSumNormal, Fin.cases_zero,
    zero_mul, zero_add, Fin.cases_succ, ← Finset.mul_sum]

private def sectionSixDirectDisplayedThresholdNormals
    {ell : Nat} : Fin 2 -> Fin (ell + 1) -> Real :=
  ![Pi.single 0 (-1 : Real), Pi.single 0 1]

private def sectionSixDirectDisplayedThresholdBounds
    (epsilon delta : Real) : Fin 2 -> Real :=
  ![-delta, sectionSixThetaGap epsilon]

private def sectionSixDirectDisplayedBandNormals
    {ell : Nat} : Fin 2 -> Fin (ell + 1) -> Real :=
  ![sectionSixDirectDisplayedSourceSumNormal (-1),
    sectionSixDirectDisplayedSourceSumNormal 1]

private def sectionSixDirectDisplayedBandBounds
    (epsilon : Real) (band : SectionSixDirectBand) : Fin 2 -> Real :=
  ![-sectionSixDirectBandLower epsilon band,
    sectionSixDirectBandUpper epsilon band]

private def sectionSixDirectDisplayedFixedRegion
    (epsilon delta : Real) (ell : Nat) (band : SectionSixDirectBand) :
    Set (Fin (ell + 1) -> Real) :=
  {y | delta <= y 0 ∧
    y 0 <= sectionSixThetaGap epsilon ∧
    (forall i : Fin ell, sectionSixThetaGap epsilon <= y i.succ) ∧
    sectionSixDirectBandLower epsilon band <= ∑ i : Fin ell, y i.succ ∧
    (∑ i : Fin ell, y i.succ) <= sectionSixDirectBandUpper epsilon band}

private noncomputable def sectionSixDirectDisplayedFixedPresentation
    (epsilon delta : Real) (ell : Nat) (band : SectionSixDirectBand) :
    TypeIIAffineHalfspacePresentation
      (sectionSixDirectDisplayedFixedRegion epsilon delta ell band) where
  constraintCount := 2 + (ell + 2)
  normal := Fin.append sectionSixDirectDisplayedThresholdNormals
    (Fin.append (fun i => Pi.single i.succ (-1 : Real))
      sectionSixDirectDisplayedBandNormals)
  bound := Fin.append
    (sectionSixDirectDisplayedThresholdBounds epsilon delta)
    (Fin.append (fun _ => -sectionSixThetaGap epsilon)
      (sectionSixDirectDisplayedBandBounds epsilon band))
  mem_iff := by
    intro y
    rw [Fin.forall_fin_add, Fin.forall_fin_add]
    constructor
    · rintro ⟨hqLower, hqUpper, hpLower, hbandLower, hbandUpper⟩
      refine ⟨?_, ?_, ?_⟩
      · intro c
        fin_cases c
        · simp [sectionSixDirectDisplayedThresholdNormals,
            sectionSixDirectDisplayedThresholdBounds,
            directTargetAffineValue_single, hqLower]
        · simp [sectionSixDirectDisplayedThresholdNormals,
            sectionSixDirectDisplayedThresholdBounds,
            directTargetAffineValue_single, hqUpper]
      · intro i
        simp only [Fin.append_right, Fin.append_left,
          directTargetAffineValue_single, neg_one_mul]
        linarith [hpLower i]
      · intro c
        fin_cases c
        · simp [sectionSixDirectDisplayedBandNormals,
            sectionSixDirectDisplayedBandBounds,
            directTargetAffineValue_displayedSourceSumNormal, hbandLower]
        · simp [sectionSixDirectDisplayedBandNormals,
            sectionSixDirectDisplayedBandBounds,
            directTargetAffineValue_displayedSourceSumNormal, hbandUpper]
    · rintro ⟨hqBounds, hpBounds, hbandBounds⟩
      have hqLower := hqBounds (0 : Fin 2)
      have hqUpper := hqBounds (1 : Fin 2)
      simp [sectionSixDirectDisplayedThresholdNormals,
        sectionSixDirectDisplayedThresholdBounds,
        directTargetAffineValue_single] at hqLower hqUpper
      refine ⟨hqLower, hqUpper, ?_, ?_, ?_⟩
      · intro i
        have hi := hpBounds i
        simp only [Fin.append_right, Fin.append_left,
          directTargetAffineValue_single, neg_one_mul] at hi
        linarith
      · have hlower := hbandBounds (0 : Fin 2)
        simpa [sectionSixDirectDisplayedBandNormals,
          sectionSixDirectDisplayedBandBounds,
          directTargetAffineValue_displayedSourceSumNormal] using hlower
      · have hupper := hbandBounds (1 : Fin 2)
        simpa [sectionSixDirectDisplayedBandNormals,
          sectionSixDirectDisplayedBandBounds,
          directTargetAffineValue_displayedSourceSumNormal] using hupper

/-- The closed weak displayed constraints for one direct Section 6 band. -/
def sectionSixDirectDisplayedBandRegion
    (epsilon delta : Real) {ell : Nat}
    (sourceRegion : Set (Fin ell -> Real))
    (band : SectionSixDirectBand) : Set (Fin (ell + 1) -> Real) :=
  typeIIAffineEmbeddingPreimageRegion
      (sectionSixDirectDisplayedSourceEmbedding ell) sourceRegion ∩
    sectionSixDirectDisplayedFixedRegion epsilon delta ell band

@[simp] theorem mem_sectionSixDirectDisplayedBandRegion
    {epsilon delta : Real} {ell : Nat}
    {sourceRegion : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {y : Fin (ell + 1) -> Real} :
    y ∈ sectionSixDirectDisplayedBandRegion
        epsilon delta sourceRegion band ↔
      (fun i => y i.succ) ∈ sourceRegion ∧
      delta <= y 0 ∧
      y 0 <= sectionSixThetaGap epsilon ∧
      (forall i : Fin ell,
        sectionSixThetaGap epsilon <= y i.succ) ∧
      match band with
      | .first =>
          sectionSixThetaOne epsilon <=
              ∑ i : Fin ell, y i.succ ∧
            (∑ i : Fin ell, y i.succ) <=
              sectionSixThetaTwo epsilon
      | .second =>
          1 - sectionSixThetaTwo epsilon <=
              ∑ i : Fin ell, y i.succ ∧
            (∑ i : Fin ell, y i.succ) <=
              1 - sectionSixThetaOne epsilon := by
  cases band <;> rfl

/-- The exact weak halfspace presentation of the displayed direct band. -/
noncomputable def sectionSixDirectDisplayedBandPresentation
    {ell : Nat} {sourceRegion : Set (Fin ell -> Real)}
    (presentation : TypeIIAffineHalfspacePresentation sourceRegion)
    (epsilon delta : Real) (band : SectionSixDirectBand) :
    TypeIIAffineHalfspacePresentation
      (sectionSixDirectDisplayedBandRegion
        epsilon delta sourceRegion band) :=
  directTargetPresentationInter
    (presentation.liftAlongEmbedding
      (sectionSixDirectDisplayedSourceEmbedding ell))
    (sectionSixDirectDisplayedFixedPresentation epsilon delta ell band)

/-- The weak displayed presentation contains the literal closed lower-q
constraint, without exposing its numeric position in the concatenation. -/
theorem exists_sectionSixDirectDisplayedBandLowerQConstraint
    {ell : Nat} {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (epsilon delta : Real) (band : SectionSixDirectBand) :
    ∃ j : Fin (sectionSixDirectDisplayedBandPresentation
        sourcePresentation epsilon delta band).constraintCount,
      (sectionSixDirectDisplayedBandPresentation
        sourcePresentation epsilon delta band).normal j =
          Pi.single (0 : Fin (ell + 1)) (-1 : Real) ∧
      (sectionSixDirectDisplayedBandPresentation
        sourcePresentation epsilon delta band).bound j = -delta := by
  classical
  refine ⟨Fin.natAdd
    (sourcePresentation.liftAlongEmbedding
      (sectionSixDirectDisplayedSourceEmbedding ell)).constraintCount
    (Fin.castAdd (ell + 2) (0 : Fin 2)), ?_, ?_⟩
  · simp only [sectionSixDirectDisplayedBandPresentation,
      directTargetPresentationInter,
      sectionSixDirectDisplayedFixedPresentation]
    rw [Fin.append_right, Fin.append_left]
    simp [sectionSixDirectDisplayedThresholdNormals]
  · simp only [sectionSixDirectDisplayedBandPresentation,
      directTargetPresentationInter,
      sectionSixDirectDisplayedFixedPresentation]
    rw [Fin.append_right, Fin.append_left]
    simp [sectionSixDirectDisplayedThresholdBounds]

/-- The fixed full target region `k+1` coordinate convention. -/
def sectionSixDirectStableTargetRegion
    {ell M : Nat} (epsilon delta : Real)
    (sourceRegion : Set (Fin ell -> Real))
    (band : SectionSixDirectBand)
    (pattern : SectionSixDirectStablePattern ell M) :
    Set (Fin ((ell + pattern.1.1) + 1) -> Real) :=
  typeIIExponentSimplex delta ∩
    typeIIAffineEmbeddingPreimageRegion pattern.canonicalDisplayedEmbedding
      (sectionSixDirectDisplayedBandRegion
        epsilon delta sourceRegion band)

@[simp] theorem mem_sectionSixDirectStableTargetRegion
    {epsilon delta : Real} {ell M : Nat}
    {sourceRegion : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {pattern : SectionSixDirectStablePattern ell M}
    {x : Fin ((ell + pattern.1.1) + 1) -> Real} :
    x ∈ sectionSixDirectStableTargetRegion
        epsilon delta sourceRegion band pattern ↔
      x ∈ typeIIExponentSimplex delta ∧
      (fun i => x (pattern.canonicalDisplayedEmbedding i)) ∈
        sectionSixDirectDisplayedBandRegion
          epsilon delta sourceRegion band := by
  rfl

/-- The exact weak halfspace presentation of one fixed full target region. -/
noncomputable def sectionSixDirectStableTargetPresentation
    {ell M : Nat} {sourceRegion : Set (Fin ell -> Real)}
    (presentation : TypeIIAffineHalfspacePresentation sourceRegion)
    (epsilon delta : Real) (band : SectionSixDirectBand)
    (pattern : SectionSixDirectStablePattern ell M) :
    TypeIIAffineHalfspacePresentation
      (sectionSixDirectStableTargetRegion
        epsilon delta sourceRegion band pattern) :=
  directTargetPresentationInter
    (typeIIExponentSimplexPresentation
      (k := ell + pattern.1.1) delta)
    ((sectionSixDirectDisplayedBandPresentation
      presentation epsilon delta band).liftAlongEmbedding
        pattern.canonicalDisplayedEmbedding)

/-- The full target is contained in the ordered delta-simplex. -/
theorem sectionSixDirectStableTargetRegion_isTypeIISourceRegion
    (epsilon delta : Real) {ell M : Nat}
    (sourceRegion : Set (Fin ell -> Real))
    (band : SectionSixDirectBand)
    (pattern : SectionSixDirectStablePattern ell M) :
    IsTypeIISourceRegion delta
      (sectionSixDirectStableTargetRegion
        epsilon delta sourceRegion band pattern) := by
  intro x hx
  exact hx.1

private def sectionSixDirectStableSourceEmbedding
    {ell M : Nat} (pattern : SectionSixDirectStablePattern ell M) :
    Fin ell ↪ Fin ((ell + pattern.1.1) + 1) :=
  (sectionSixDirectDisplayedSourceEmbedding ell).trans
    pattern.canonicalDisplayedEmbedding

private noncomputable def sectionSixDirectStableSourcePositions
    {ell M : Nat} (pattern : SectionSixDirectStablePattern ell M) :
    Finset (Fin ((ell + pattern.1.1) + 1)) :=
  Finset.univ.map (sectionSixDirectStableSourceEmbedding pattern)

private theorem sum_sectionSixDirectStableSourcePositions
    {ell M : Nat} (pattern : SectionSixDirectStablePattern ell M)
    (x : Fin ((ell + pattern.1.1) + 1) -> Real) :
    (∑ j ∈ sectionSixDirectStableSourcePositions pattern, x j) =
      ∑ i : Fin ell, x (pattern.canonicalDisplayedEmbedding i.succ) := by
  simp [sectionSixDirectStableSourcePositions,
    sectionSixDirectStableSourceEmbedding,
    sectionSixDirectDisplayedSourceEmbedding]

/-- Both direct bands retain their exact two-epsilon convenience margin. The
second uses the complement of the displayed source-prime positions in the
full sum-one tuple. -/
theorem sectionSixDirectStableTargetRegion_convenient_two_mul
    {epsilon delta : Real}
    {ell M : Nat} (sourceRegion : Set (Fin ell -> Real))
    (band : SectionSixDirectBand)
    (pattern : SectionSixDirectStablePattern ell M) :
    IsTypeIIRegionConvenient (2 * epsilon)
      (sectionSixDirectStableTargetRegion
        epsilon delta sourceRegion band pattern) := by
  let sourcePositions := sectionSixDirectStableSourcePositions pattern
  cases band with
  | first =>
      refine ⟨sourcePositions, ?_⟩
      intro x hx
      have hdisplay := mem_sectionSixDirectDisplayedBandRegion.mp
        (mem_sectionSixDirectStableTargetRegion.mp hx).2
      rw [sum_sectionSixDirectStableSourcePositions pattern x]
      have hband := hdisplay.2.2.2.2
      simp only [sectionSixThetaOne, sectionSixThetaTwo] at hband
      exact ⟨by linarith, by linarith⟩

  | second =>
      let complementPositions : Finset (Fin ((ell + pattern.1.1) + 1)) :=
        Finset.univ \ sourcePositions
      refine ⟨complementPositions, ?_⟩
      intro x hx
      have htarget := mem_sectionSixDirectStableTargetRegion.mp hx
      have hdisplay := mem_sectionSixDirectDisplayedBandRegion.mp htarget.2
      have hsumAll : (∑ j, x j) = 1 := htarget.1.2.2
      have hsumComplement : (∑ j ∈ complementPositions, x j) =
          1 - ∑ i : Fin ell,
            x (pattern.canonicalDisplayedEmbedding i.succ) := by
        rw [show complementPositions = Finset.univ \ sourcePositions by rfl,
          Finset.sum_sdiff_eq_sub (Finset.subset_univ sourcePositions)]
        change (∑ j, x j) - (∑ j ∈ sourcePositions, x j) = _
        rw [hsumAll, sum_sectionSixDirectStableSourcePositions pattern x]
      rw [hsumComplement]
      have hband := hdisplay.2.2.2.2
      simp only [sectionSixThetaOne, sectionSixThetaTwo] at hband
      exact ⟨by linarith, by linarith⟩

/--
Both direct bands satisfy convenience after discarding one epsilon of their exact displayed
margin.
-/
theorem sectionSixDirectStableTargetRegion_convenient
    {epsilon delta : Real} (hepsilon : 0 <= epsilon)
    {ell M : Nat} (sourceRegion : Set (Fin ell -> Real))
    (band : SectionSixDirectBand)
    (pattern : SectionSixDirectStablePattern ell M) :
    IsTypeIIRegionConvenient epsilon
      (sectionSixDirectStableTargetRegion
        epsilon delta sourceRegion band pattern) := by
  obtain ⟨I, hI⟩ := sectionSixDirectStableTargetRegion_convenient_two_mul
    (epsilon := epsilon) (delta := delta) sourceRegion band pattern
  refine ⟨I, ?_⟩
  intro x hx
  have hbounds := hI x hx
  exact ⟨by linarith [hbounds.1], by linarith [hbounds.2]⟩

end

end PrimesRestrictedDigits
