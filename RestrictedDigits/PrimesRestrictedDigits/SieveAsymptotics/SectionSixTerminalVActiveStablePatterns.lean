import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStablePatternCoverage
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStablePatternValueImages

/-!
# Active terminal-V stable patterns

The exact signed terminal-V decomposition already retains stable patterns as outer summation
labels. This module restricts that sum to patterns realized by the ambient carrier and derives
the canonical active-pattern arity budget.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/--
Stable patterns whose exact terminal-V near fiber over the ambient carrier is nonempty.
-/
noncomputable def sectionSixTerminalVActiveStablePatterns
    {epsilon delta rho : Real} {ell length : Nat}
    (region : Set (Fin ell -> Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (B : Finset Nat) (M : Nat) :
    Finset (SectionSixTerminalVStablePattern ell M) :=
  Finset.univ.filter fun pattern =>
    (sectionSixSourceBandTerminalVNearCandidatesOfStablePattern region
      hepsilon hepsilonSmall hlength hdeltaGapStrict.le band B
        (((10 ^ length : Nat) : Real) ^ delta)
        (typeIINearXCarrier (10 ^ length) rho) M pattern).Nonempty

@[simp] theorem mem_sectionSixTerminalVActiveStablePatterns
    {epsilon delta rho : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)}
    {hepsilon : 0 < epsilon} {hepsilonSmall : epsilon <= 1 / 64}
    {hlength : 1 <= length}
    {hdeltaGapStrict : delta < sectionSixThetaGap epsilon}
    {band : SectionSixStateBand} {B : Finset Nat} {M : Nat}
    {pattern : SectionSixTerminalVStablePattern ell M} :
    pattern ∈ sectionSixTerminalVActiveStablePatterns (rho := rho) region
        hepsilon hepsilonSmall hlength hdeltaGapStrict band B M <->
      (sectionSixSourceBandTerminalVNearCandidatesOfStablePattern region
        hepsilon hepsilonSmall hlength hdeltaGapStrict.le band B
          (((10 ^ length : Nat) : Real) ^ delta)
          (typeIINearXCarrier (10 ^ length) rho) M pattern).Nonempty := by
  simp [sectionSixTerminalVActiveStablePatterns]

/-- A pattern inactive over an ambient carrier has empty fixed-pattern fiber
over every smaller requested carrier. -/
theorem
    sectionSixSourceBandTerminalVNearCandidatesOfStablePattern_eq_empty_of_not_mem_active
    {C B : Finset Nat} (hCB : C ⊆ B)
    {epsilon delta rho : Real} {ell length : Nat}
    (region : Set (Fin ell -> Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (M : Nat)
    (pattern : SectionSixTerminalVStablePattern ell M)
    (hinactive : pattern ∉ sectionSixTerminalVActiveStablePatterns
      (rho := rho) region hepsilon hepsilonSmall hlength hdeltaGapStrict band
        B M) :
    sectionSixSourceBandTerminalVNearCandidatesOfStablePattern region
      hepsilon hepsilonSmall hlength hdeltaGapStrict.le band C
        (((10 ^ length : Nat) : Real) ^ delta)
        (typeIINearXCarrier (10 ^ length) rho) M pattern = ∅ := by
  classical
  rw [
    sectionSixSourceBandTerminalVNearCandidatesOfStablePattern_eq_filter_of_subset
      hCB]
  have hBempty :
      sectionSixSourceBandTerminalVNearCandidatesOfStablePattern region
        hepsilon hepsilonSmall hlength hdeltaGapStrict.le band B
          (((10 ^ length : Nat) : Real) ^ delta)
          (typeIINearXCarrier (10 ^ length) rho) M pattern = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hnonempty
    exact hinactive
      (mem_sectionSixTerminalVActiveStablePatterns.mpr hnonempty)
  rw [hBempty]
  exact Finset.filter_empty _

/-- The represented-value image of an inactive fixed-pattern fiber is empty
over every smaller requested carrier. -/
theorem
    sectionSixTerminalVNearValueImageOfStablePattern_eq_empty_of_not_mem_active
    {C B : Finset Nat} (hCB : C ⊆ B)
    {epsilon delta rho : Real} {ell length : Nat}
    (region : Set (Fin ell -> Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (M : Nat)
    (pattern : SectionSixTerminalVStablePattern ell M)
    (hinactive : pattern ∉ sectionSixTerminalVActiveStablePatterns
      (rho := rho) region hepsilon hepsilonSmall hlength hdeltaGapStrict band
        B M) :
    sectionSixTerminalVNearValueImageOfStablePattern region hepsilon
      hepsilonSmall hlength hdeltaGapStrict.le band C
        (((10 ^ length : Nat) : Real) ^ delta)
        (typeIINearXCarrier (10 ^ length) rho) M pattern = ∅ := by
  unfold sectionSixTerminalVNearValueImageOfStablePattern
  rw [
    sectionSixSourceBandTerminalVNearCandidatesOfStablePattern_eq_empty_of_not_mem_active
      hCB region hepsilon hepsilonSmall hlength hdeltaGapStrict band M pattern
        hinactive,
    Finset.image_empty]

/-- The all-pattern signed image discrepancy is exactly its restriction to
patterns realized over the ambient carrier. Pattern labels, signs, and
cross-pattern multiplicities are retained. -/
theorem sum_sectionSixTerminalVStablePattern_imageDiscrepancy_eq_sum_active
    {A B : Finset Nat} (hAB : A ⊆ B) (lambda : Real)
    {epsilon delta rho : Real} {ell length : Nat}
    (region : Set (Fin ell -> Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (M : Nat) :
    let image := fun C : Finset Nat =>
      fun pattern : SectionSixTerminalVStablePattern ell M =>
        sectionSixTerminalVNearValueImageOfStablePattern region hepsilon
          hepsilonSmall hlength hdeltaGapStrict.le band C
            (((10 ^ length : Nat) : Real) ^ delta)
            (typeIINearXCarrier (10 ^ length) rho) M pattern
    let term := fun pattern : SectionSixTerminalVStablePattern ell M =>
      (-1 : Real) ^ pattern.1.1 *
        (((image A pattern).card : Real) -
          lambda * ((image B pattern).card : Real))
    (∑ pattern : SectionSixTerminalVStablePattern ell M, term pattern) =
      ∑ pattern ∈ sectionSixTerminalVActiveStablePatterns (rho := rho) region
        hepsilon hepsilonSmall hlength hdeltaGapStrict band B M,
          term pattern := by
  classical
  dsimp only
  let active := sectionSixTerminalVActiveStablePatterns (rho := rho) region
    hepsilon hepsilonSmall hlength hdeltaGapStrict band B M
  let image := fun C : Finset Nat =>
    fun pattern : SectionSixTerminalVStablePattern ell M =>
      sectionSixTerminalVNearValueImageOfStablePattern region hepsilon
        hepsilonSmall hlength hdeltaGapStrict.le band C
          (((10 ^ length : Nat) : Real) ^ delta)
          (typeIINearXCarrier (10 ^ length) rho) M pattern
  let term := fun pattern : SectionSixTerminalVStablePattern ell M =>
    (-1 : Real) ^ pattern.1.1 *
      (((image A pattern).card : Real) -
        lambda * ((image B pattern).card : Real))
  symm
  apply Finset.sum_subset (Finset.subset_univ active)
  intro pattern _ hinactive
  have hAempty : image A pattern = ∅ := by
    exact
      sectionSixTerminalVNearValueImageOfStablePattern_eq_empty_of_not_mem_active
        hAB region hepsilon hepsilonSmall hlength hdeltaGapStrict band M
          pattern (by simpa only [active] using hinactive)
  have hBempty : image B pattern = ∅ := by
    exact
      sectionSixTerminalVNearValueImageOfStablePattern_eq_empty_of_not_mem_active
        Finset.Subset.rfl region hepsilon hepsilonSmall hlength
          hdeltaGapStrict band M pattern
            (by simpa only [active] using hinactive)
  dsimp only [image] at hAempty hBempty
  rw [hAempty, hBempty]
  simp

/-- A stable pattern active at the canonical ceiling has total raw arity at
most that same ceiling. This uses realization, not merely the two stored
component bounds. -/
theorem sectionSixTerminalVActiveStablePattern_totalArity_le_ceil_two_div
    {epsilon delta rho : Real} {ell length : Nat}
    (region : Set (Fin ell -> Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (B : Finset Nat)
    (hrhoDelta : rho ^ 2 < delta)
    {pattern : SectionSixTerminalVStablePattern ell (Nat.ceil (2 / delta))}
    (hactive : pattern ∈ sectionSixTerminalVActiveStablePatterns
      (rho := rho) region hepsilon hepsilonSmall hlength hdeltaGapStrict band
        B (Nat.ceil (2 / delta))) :
    (pattern.1.1 + ell) + pattern.2.1.1 <= Nat.ceil (2 / delta) := by
  obtain ⟨candidate, hcandidate⟩ :=
    mem_sectionSixTerminalVActiveStablePatterns.mp hactive
  have hslice :=
    mem_sectionSixSourceBandTerminalVNearCandidatesOfStablePattern.mp
      hcandidate
  have htotal := sectionSixTerminalVNearCandidate_totalArity_le_ceil_two_div
    hepsilon hepsilonSmall hlength hdeltaGapStrict hrhoDelta hslice.1
  obtain ⟨hinner, hresidual, _hinnerPositions, _hsourcePositions⟩ :=
    SectionSixTerminalVCandidate.stablePatternTag_eq_some_data hslice.2
  omega

/-- The global canonical width budget implies the exact BN width for every
active pattern. -/
theorem sectionSixTerminalVActiveStablePattern_convenienceWidth
    {epsilon delta rho : Real} {ell length : Nat}
    (region : Set (Fin ell -> Real))
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (band : SectionSixStateBand) (B : Finset Nat)
    (hrhoDelta : rho ^ 2 < delta) (hrho : 0 <= rho)
    (hwidth :
      rho ^ 2 + ((Nat.ceil (2 / delta) : Real) * rho) <= epsilon)
    {pattern : SectionSixTerminalVStablePattern ell (Nat.ceil (2 / delta))}
    (hactive : pattern ∈ sectionSixTerminalVActiveStablePatterns
      (rho := rho) region hepsilon hepsilonSmall hlength hdeltaGapStrict band
        B (Nat.ceil (2 / delta))) :
    rho ^ 2 +
        (((((pattern.1.1 + ell) + pattern.2.1.1) - 1 : Nat) : Real) * rho) <=
      epsilon := by
  have htotal :=
    sectionSixTerminalVActiveStablePattern_totalArity_le_ceil_two_div region
      hepsilon hepsilonSmall hlength hdeltaGapStrict band B hrhoDelta hactive
  have hcoefficientNat :
      ((pattern.1.1 + ell) + pattern.2.1.1) - 1 <=
        Nat.ceil (2 / delta) :=
    (Nat.sub_le _ _).trans htotal
  have hcoefficientReal :
      (((((pattern.1.1 + ell) + pattern.2.1.1) - 1 : Nat) : Real)) <=
        (Nat.ceil (2 / delta) : Real) := by
    exact_mod_cast hcoefficientNat
  calc
    rho ^ 2 +
        (((((pattern.1.1 + ell) + pattern.2.1.1) - 1 : Nat) : Real) * rho) <=
      rho ^ 2 + ((Nat.ceil (2 / delta) : Real) * rho) :=
        add_le_add (le_refl _) <|
          mul_le_mul_of_nonneg_right hcoefficientReal hrho
    _ <= epsilon := hwidth

end

end PrimesRestrictedDigits
