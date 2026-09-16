import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoStablePatternCoverage
import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoStablePatternValueImages

/-!
# Active stable patterns for Proposition 6.2

Only stable patterns realized by the ambient near carrier contribute to the later
coefficient-one Sigma ledger. Active realization also supplies the canonical total-arity and
sharp local convenience-width bounds.

Source: `MAYNARD-PRD-PUBLISHED`, proof of Lemma 7.3, pp. 149--152.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- Stable patterns whose Proposition 6.2 near fiber over the ambient carrier
is nonempty. -/
noncomputable def propositionSixTwoActiveStablePatterns
    (epsilon rho : Real) (ell : Nat) (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (B : Finset Nat) (M : Nat) :
    Finset (PropositionSixTwoStablePattern ell M) :=
  Finset.univ.filter fun pattern =>
    (propositionSixTwoNearCandidatesOfStablePattern epsilon rho ell I j region
      length band B M pattern).Nonempty

@[simp] theorem mem_propositionSixTwoActiveStablePatterns
    {epsilon rho : Real} {ell length M : Nat} {I : Finset (Fin ell)}
    {j : Fin ell} {region : Set (Fin ell -> Real)}
    {band : SectionSixDirectBand} {B : Finset Nat}
    {pattern : PropositionSixTwoStablePattern ell M} :
    pattern ∈ propositionSixTwoActiveStablePatterns epsilon rho ell I j region
        length band B M <->
      (propositionSixTwoNearCandidatesOfStablePattern epsilon rho ell I j
        region length band B M pattern).Nonempty := by
  simp [propositionSixTwoActiveStablePatterns]

/-- Restricting the represented carrier cannot activate a pattern whose
ambient near fiber is empty. -/
theorem
    propositionSixTwoNearCandidatesOfStablePattern_eq_empty_of_not_mem_active
    {C B : Finset Nat} (hCB : C ⊆ B)
    (epsilon rho : Real) (ell : Nat) (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (M : Nat)
    (pattern : PropositionSixTwoStablePattern ell M)
    (hinactive : pattern ∉ propositionSixTwoActiveStablePatterns epsilon rho
      ell I j region length band B M) :
    propositionSixTwoNearCandidatesOfStablePattern epsilon rho ell I j region
      length band C M pattern = ∅ := by
  classical
  rw [propositionSixTwoNearCandidatesOfStablePattern_eq_filter_of_subset hCB]
  have hBempty :
      propositionSixTwoNearCandidatesOfStablePattern epsilon rho ell I j region
        length band B M pattern = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hnonempty
    exact hinactive (mem_propositionSixTwoActiveStablePatterns.mpr hnonempty)
  rw [hBempty]
  exact Finset.filter_empty _

/-- The represented-value image of an ambiently inactive pattern is empty over
every smaller requested carrier. -/
theorem
    propositionSixTwoNearValueImageOfStablePattern_eq_empty_of_not_mem_active
    {C B : Finset Nat} (hCB : C ⊆ B)
    (epsilon rho : Real) (ell : Nat) (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (M : Nat)
    (pattern : PropositionSixTwoStablePattern ell M)
    (hinactive : pattern ∉ propositionSixTwoActiveStablePatterns epsilon rho
      ell I j region length band B M) :
    propositionSixTwoNearValueImageOfStablePattern epsilon rho ell I j region
      length band C M pattern = ∅ := by
  unfold propositionSixTwoNearValueImageOfStablePattern
  rw [
    propositionSixTwoNearCandidatesOfStablePattern_eq_empty_of_not_mem_active
      hCB epsilon rho ell I j region length band M pattern hinactive,
    Finset.image_empty]

/-- An active stable pattern at the canonical ceiling has total arity at most
that ceiling. This uses a realizing ambient candidate, not merely the residual
arity stored in the pattern type. -/
theorem propositionSixTwoActiveStablePattern_totalArity_le_ceil_two_div
    {epsilon rho : Real} {ell length : Nat} {I : Finset (Fin ell)}
    {j : Fin ell} {region : Set (Fin ell -> Real)}
    {band : SectionSixDirectBand} {B : Finset Nat}
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    {pattern : PropositionSixTwoStablePattern ell
      (Nat.ceil (2 / sectionSixThetaGap epsilon))}
    (hactive : pattern ∈ propositionSixTwoActiveStablePatterns epsilon rho ell
      I j region length band B
        (Nat.ceil (2 / sectionSixThetaGap epsilon))) :
    ell + pattern.1.1 <= Nat.ceil (2 / sectionSixThetaGap epsilon) := by
  obtain ⟨candidate, hcandidate⟩ :=
    mem_propositionSixTwoActiveStablePatterns.mp hactive
  have hslice :=
    mem_propositionSixTwoNearCandidatesOfStablePattern.mp hcandidate
  have htotal := propositionSixTwoNearCandidate_totalArity_le_two_div
    hepsilon hepsilonSmall hlength hslice.1
  have htag :=
    PropositionSixTwoCandidate.stablePatternTag_eq_some_data hslice.2
  have hceil :
      ell + candidate.2.primeFactorsList.length <=
        Nat.ceil (2 / sectionSixThetaGap epsilon) := by
    exact_mod_cast htotal.trans
      (Nat.le_ceil (2 / sectionSixThetaGap epsilon))
  simpa only [htag.1] using hceil

/-- The sharp global canonical width budget implies the exact local width used
by the fixed-pattern finite ledger. -/
theorem propositionSixTwoActiveStablePattern_convenienceWidth
    {epsilon rho : Real} {ell length : Nat} {I : Finset (Fin ell)}
    {j : Fin ell} {region : Set (Fin ell -> Real)}
    {band : SectionSixDirectBand} {B : Finset Nat}
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length) (hrho : 0 <= rho)
    (hwidth :
      rho ^ 2 +
          (((Nat.ceil (2 / sectionSixThetaGap epsilon) - 1 : Nat) : Real) *
            rho) <=
        epsilon)
    {pattern : PropositionSixTwoStablePattern ell
      (Nat.ceil (2 / sectionSixThetaGap epsilon))}
    (hactive : pattern ∈ propositionSixTwoActiveStablePatterns epsilon rho ell
      I j region length band B
        (Nat.ceil (2 / sectionSixThetaGap epsilon))) :
    rho ^ 2 + (((ell + pattern.1.1 - 1 : Nat) : Real) * rho) <= epsilon := by
  have htotal := propositionSixTwoActiveStablePattern_totalArity_le_ceil_two_div
    hepsilon hepsilonSmall hlength hactive
  have hcoefficientNat :
      ell + pattern.1.1 - 1 <=
        Nat.ceil (2 / sectionSixThetaGap epsilon) - 1 := by
    omega
  have hcoefficientReal :
      ((ell + pattern.1.1 - 1 : Nat) : Real) <=
        ((Nat.ceil (2 / sectionSixThetaGap epsilon) - 1 : Nat) : Real) := by
    exact_mod_cast hcoefficientNat
  calc
    rho ^ 2 + (((ell + pattern.1.1 - 1 : Nat) : Real) * rho) <=
        rho ^ 2 +
          (((Nat.ceil (2 / sectionSixThetaGap epsilon) - 1 : Nat) : Real) *
            rho) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hcoefficientReal hrho)
    _ <= epsilon := hwidth

end

end PrimesRestrictedDigits
