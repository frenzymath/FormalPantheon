import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStablePatternWallFactorCoefficient

/-!
# Canonical finite sums of direct stable-pattern wall coefficients

This chooses the unique predecessor dimension pattern by pattern and forms the finite
coefficient needed before eventual Type II absorption. See `MAYNARD-PRD-PUBLISHED`, Lemma 7.3,
pp. 150--152.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The canonical N coefficient for a positive-dimensional stable pattern,
and zero when no predecessor dimension exists. -/
noncomputable def sectionSixDirectStablePatternCanonicalWallCoefficient
    {ell M : Nat} {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (epsilon delta : Real) (band : SectionSixDirectBand)
    (pattern : SectionSixDirectStablePattern ell M) : Real :=
  if hzero : ell + pattern.1.1 = 0 then
    0
  else
    sectionSixDirectStablePatternWallCoefficient
      sourcePresentation epsilon delta band pattern
      (ell + pattern.1.1).pred
      (by simpa only [Nat.succ_eq_add_one] using
        (Nat.succ_pred hzero).symm)

/-- Any predecessor supplied by M gives exactly the canonical coefficient. -/
theorem sectionSixDirectStablePatternCanonicalWallCoefficient_eq_raw
    {ell M : Nat} {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (epsilon delta : Real) (band : SectionSixDirectBand)
    (pattern : SectionSixDirectStablePattern ell M) (n : Nat)
    (hdimension : ell + pattern.1.1 = n + 1) :
    sectionSixDirectStablePatternCanonicalWallCoefficient
        sourcePresentation epsilon delta band pattern =
      sectionSixDirectStablePatternWallCoefficient
        sourcePresentation epsilon delta band pattern n hdimension := by
  unfold sectionSixDirectStablePatternCanonicalWallCoefficient
  split
  next hzero => omega
  next hnonzero =>
    have hcanonical : ell + pattern.1.1 =
        (ell + pattern.1.1).pred + 1 := by
      simpa only [Nat.succ_eq_add_one] using
        (Nat.succ_pred hnonzero).symm
    have hn : n = (ell + pattern.1.1).pred :=
      Nat.add_right_cancel (hdimension.symm.trans hcanonical)
    subst n
    rfl

/-- A genuinely zero-dimensional pattern has canonical coefficient zero. -/
theorem sectionSixDirectStablePatternCanonicalWallCoefficient_eq_zero
    {ell M : Nat} {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (epsilon delta : Real) (band : SectionSixDirectBand)
    (pattern : SectionSixDirectStablePattern ell M)
    (hdimension : ell + pattern.1.1 = 0) :
    sectionSixDirectStablePatternCanonicalWallCoefficient
      sourcePresentation epsilon delta band pattern = 0 := by
  simp [sectionSixDirectStablePatternCanonicalWallCoefficient, hdimension]

/-- The fixed coefficient sum over the full finite stable-pattern type. -/
noncomputable def sectionSixDirectStablePatternCanonicalWallCoefficientSum
    {ell : Nat} {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (epsilon delta : Real) (band : SectionSixDirectBand) (M : Nat) : Real :=
  ∑ pattern : SectionSixDirectStablePattern ell M,
    sectionSixDirectStablePatternCanonicalWallCoefficient
      sourcePresentation epsilon delta band pattern

/-- The complete finite stable-pattern coefficient sum is nonnegative. -/
theorem sectionSixDirectStablePatternCanonicalWallCoefficientSum_nonneg
    {ell : Nat} {region : Set (Fin ell -> Real)}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    (epsilon delta : Real) (band : SectionSixDirectBand) (M : Nat) :
    0 <= sectionSixDirectStablePatternCanonicalWallCoefficientSum
      sourcePresentation epsilon delta band M := by
  unfold sectionSixDirectStablePatternCanonicalWallCoefficientSum
  apply Finset.sum_nonneg
  intro pattern _
  unfold sectionSixDirectStablePatternCanonicalWallCoefficient
  split
  · exact le_rfl
  · exact sectionSixDirectStablePatternWallCoefficient_nonneg
      sourcePresentation epsilon delta band pattern
        (ell + pattern.1.1).pred
        (by
          simpa only [Nat.succ_eq_add_one] using (Nat.succ_pred ‹_›).symm)

end

end PrimesRestrictedDigits
