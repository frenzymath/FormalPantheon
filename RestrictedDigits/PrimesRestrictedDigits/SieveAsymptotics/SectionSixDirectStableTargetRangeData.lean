import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStableTargetRegion

/-!
# Reverse direct-range data from base-X displayed factors

This reconstructs the accepted direct `(p,q)` index in the reverse direction of the
ordered-factor reduction in Lemma 7.3 of `MAYNARD-PRD-PUBLISHED`, pp. 150--152.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- Base-X displayed membership and a separately retained strict lower-q
endpoint reconstruct the exact accepted direct index. -/
theorem sectionSixDirectStableTargetFactors_index_mem_of_baseXDisplayed
    {epsilon delta : Real} {ell length M : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {pattern : SectionSixDirectStablePattern ell M}
    (factors : Fin ((ell + pattern.1.1) + 1) -> Nat)
    (hepsilon : 0 < epsilon)
    (hlength : 1 <= length)
    (hprime : ∀ i, (factors i).Prime)
    (hmonotone : Monotone factors)
    (hembedding : StrictMono pattern.canonicalDisplayedEmbedding)
    (hdisplayX :
      (fun i => normalizedPrimeLog (10 ^ length)
        (factors (pattern.canonicalDisplayedEmbedding i))) ∈
          sectionSixDirectDisplayedBandRegion epsilon delta region band)
    (hqLowerStrict :
      (((10 ^ length : Nat) : Real) ^ delta) <
        (factors (pattern.canonicalDisplayedEmbedding 0) : Real)) :
    ((fun i => factors (pattern.canonicalDisplayedEmbedding i.succ)),
        factors (pattern.canonicalDisplayedEmbedding 0)) ∈
      sectionSixDirectRepeatedIndices epsilon delta ell region length band := by
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let embedding := pattern.canonicalDisplayedEmbedding
  let p : Fin ell -> Nat := fun i => factors (embedding i.succ)
  let q : Nat := factors (embedding 0)
  have hXNat : 1 < XNat := by
    dsimp only [XNat]
    exact Nat.one_lt_pow (by omega : length ≠ 0) (by norm_num)
  have hX : (1 : Real) < X := by
    dsimp only [X, XNat]
    exact_mod_cast hXNat
  have hdisplay := mem_sectionSixDirectDisplayedBandRegion.mp hdisplayX
  have hpPrime : ∀ i, (p i).Prime := fun i => hprime _
  have hqPrime : q.Prime := hprime _
  have hpMonotone : Monotone p := by
    intro i j hij
    exact hmonotone (hembedding.monotone (Fin.succ_le_succ_iff.mpr hij))
  have hpLower : ∀ i,
      X ^ sectionSixThetaGap epsilon <= (p i : Real) := by
    intro i
    have hi := hdisplay.2.2.2.1 i
    change sectionSixThetaGap epsilon <=
      Real.logb X (p i : Real) at hi
    exact (Real.le_logb_iff_rpow_le hX (by
      exact_mod_cast (hpPrime i).pos)).mp hi
  have hqUpper : (q : Real) <= X ^ sectionSixThetaGap epsilon := by
    have hq := hdisplay.2.2.1
    change Real.logb X (q : Real) <= sectionSixThetaGap epsilon at hq
    exact (Real.logb_le_iff_le_rpow hX (by
      exact_mod_cast hqPrime.pos)).mp hq
  have hpProductPos : (0 : Real) < (primeTupleProduct p : Real) := by
    exact_mod_cast primeTupleProduct_pos fun i => (hpPrime i).ne_zero
  have hsum : (∑ i, normalizedPrimeLog XNat (p i)) =
      normalizedPrimeLog XNat (primeTupleProduct p) :=
    sum_normalizedPrimeLog_eq_normalizedPrimeLog_product
      (fun i => (hpPrime i).ne_zero)
  have hpRange : sectionSixDirectRangeMembership band X
      (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon)
      (primeTupleProduct p : Real) := by
    cases band with
    | first =>
        have hband := hdisplay.2.2.2.2
        change sectionSixThetaOne epsilon <=
            ∑ i, normalizedPrimeLog XNat (p i) ∧
          (∑ i, normalizedPrimeLog XNat (p i)) <=
            sectionSixThetaTwo epsilon at hband
        rw [hsum] at hband
        change sectionSixThetaOne epsilon <=
            Real.logb X (primeTupleProduct p : Real) ∧
          Real.logb X (primeTupleProduct p : Real) <=
            sectionSixThetaTwo epsilon at hband
        exact ⟨
          (Real.le_logb_iff_rpow_le hX hpProductPos).mp hband.1,
          (Real.logb_le_iff_le_rpow hX hpProductPos).mp hband.2⟩
    | second =>
        have hband := hdisplay.2.2.2.2
        change 1 - sectionSixThetaTwo epsilon <=
            ∑ i, normalizedPrimeLog XNat (p i) ∧
          (∑ i, normalizedPrimeLog XNat (p i)) <=
            1 - sectionSixThetaOne epsilon at hband
        rw [hsum] at hband
        change 1 - sectionSixThetaTwo epsilon <=
            Real.logb X (primeTupleProduct p : Real) ∧
          Real.logb X (primeTupleProduct p : Real) <=
            1 - sectionSixThetaOne epsilon at hband
        exact ⟨
          (Real.le_logb_iff_rpow_le hX hpProductPos).mp hband.1,
          (Real.logb_le_iff_le_rpow hX hpProductPos).mp hband.2⟩
  have hpCap : (primeTupleProduct p : Real) <=
      X ^ (1 - sectionSixThetaOne epsilon) := by
    cases band with
    | first =>
        exact hpRange.2.trans
          (Real.rpow_le_rpow_of_exponent_le hX.le (by
            simp only [sectionSixThetaOne, sectionSixThetaTwo]
            linarith))
    | second => exact hpRange.2
  have hpSource : IsPropositionSixOnePrimeTuple epsilon length region p := by
    dsimp only [IsPropositionSixOnePrimeTuple]
    refine ⟨hpPrime, hpMonotone, ?_, hpCap, ?_⟩
    · simpa only [X, XNat] using hpLower
    · simpa only [p, embedding, XNat] using hdisplay.1
  have hpMem : p ∈ propositionSixOnePrimeTuples epsilon ell region length :=
    (mem_propositionSixOnePrimeTuples_iff_source hepsilon hlength).mpr hpSource
  apply mem_sectionSixDirectRepeatedIndices.mpr
  constructor
  · apply mem_sectionSixDirectRangePrimeTuples.mpr
    exact ⟨hpMem, by simpa only [X, XNat] using hpRange⟩
  · apply mem_sievePrimeInterval.mpr
    exact ⟨hqPrime, by simpa only [q, embedding] using hqLowerStrict,
      by simpa only [q, X, XNat] using hqUpper⟩

end

end PrimesRestrictedDigits
