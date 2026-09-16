import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoStablePatterns
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIStrictRoughFactorArity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Stable-pattern coverage for Proposition 6.2

Near candidates have bounded complete prime-factor arity and therefore a concrete stable
pattern. The printed weak source cap separately excludes a unit residual, and strict roughness
orders the distinguished displayed label before every off-range label.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The weak source cap excludes a unit residual at the weak width endpoint.
Candidate membership itself forces the decimal scale to exceed one. -/
theorem propositionSixTwoNearCandidate_cofactor_ne_one
    {epsilon rho : Real} {ell length : Nat} {I : Finset (Fin ell)}
    {j : Fin ell} {region : Set (Fin ell -> Real)}
    {band : SectionSixDirectBand} {C : Finset Nat}
    {candidate : PropositionSixTwoCandidate ell}
    (hrhoSq : rho ^ 2 <= sectionSixThetaGap epsilon)
    (hcandidate : candidate ∈ propositionSixTwoNearCandidates
      epsilon ell I j region length band rho C) :
    candidate.2 ≠ 1 := by
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  have hnearData := mem_propositionSixTwoNearCandidates.mp hcandidate
  have hcandidateData := mem_propositionSixTwoCandidates.mp hnearData.1
  have hpFinsetData := mem_propositionSixTwoPrimeTuples.mp hcandidateData.1
  have hpJData := Nat.mem_primesLE.mp (hpFinsetData.1 j)
  have hXNat : 1 < XNat := (hpJData.2.one_lt).trans_le hpJData.1
  have hX : 1 < X := by
    dsimp only [X]
    exact_mod_cast hXNat
  have hXPos : 0 < X := zero_lt_one.trans hX
  have hpData :=
    mem_propositionSixTwoPrimeTuples_iff_source.mp hcandidateData.1
  dsimp [IsPropositionSixTwoPrimeTuple] at hpData
  have hlower : X ^ sectionSixThetaGap epsilon <=
      (candidate.1 j : Real) := by
    simpa only [X, XNat] using hpData.2.2.1 j
  have hcapNat :
      primeTupleProduct candidate.1 * candidate.1 j <= XNat := by
    simpa only [XNat] using hpData.2.2.2.2.1
  have hcap : (primeTupleProduct candidate.1 : Real) *
      (candidate.1 j : Real) <= X := by
    norm_num only [← Nat.cast_mul]
    dsimp only [X]
    exact_mod_cast hcapNat
  have hnearLower :
      X ^ (1 - rho ^ 2) < (candidate.value : Real) := by
    simpa only [X, XNat] using
      (mem_typeIINearXCarrier.mp hnearData.2).2
  intro hm
  have hvalue :=
    PropositionSixTwoCandidate.value_eq_mul_primeTupleProduct_of_mem
      hnearData.1
  rw [hvalue, hm, one_mul] at hnearLower
  have hgapPowerPos : 0 < X ^ sectionSixThetaGap epsilon :=
    Real.rpow_pos_of_pos hXPos _
  have hscaledLower :
      X ^ (1 - rho ^ 2) * X ^ sectionSixThetaGap epsilon <
        (primeTupleProduct candidate.1 : Real) *
          X ^ sectionSixThetaGap epsilon :=
    mul_lt_mul_of_pos_right hnearLower hgapPowerPos
  have hscaledUpper :
      (primeTupleProduct candidate.1 : Real) *
          X ^ sectionSixThetaGap epsilon <=
        (primeTupleProduct candidate.1 : Real) * (candidate.1 j : Real) :=
    mul_le_mul_of_nonneg_left hlower (by positivity)
  have htooSmall :
      X ^ ((1 - rho ^ 2) + sectionSixThetaGap epsilon) < X := by
    rw [Real.rpow_add hXPos]
    exact hscaledLower.trans_le (hscaledUpper.trans hcap)
  have hexponent :
      1 <= (1 - rho ^ 2) + sectionSixThetaGap epsilon := by
    linarith
  have htooLarge :
      X <= X ^ ((1 - rho ^ 2) + sectionSixThetaGap epsilon) := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hX.le hexponent)
  exact (not_lt_of_ge htooLarge) htooSmall

/-- The weak-width endpoint already makes every near residual factor list
nonempty. -/
theorem propositionSixTwoNearCandidate_residualLength_pos
    {epsilon rho : Real} {ell length : Nat} {I : Finset (Fin ell)}
    {j : Fin ell} {region : Set (Fin ell -> Real)}
    {band : SectionSixDirectBand} {C : Finset Nat}
    {candidate : PropositionSixTwoCandidate ell}
    (hrhoSq : rho ^ 2 <= sectionSixThetaGap epsilon)
    (hcandidate : candidate ∈ propositionSixTwoNearCandidates
      epsilon ell I j region length band rho C) :
    0 < candidate.2.primeFactorsList.length := by
  have hnearData := mem_propositionSixTwoNearCandidates.mp hcandidate
  have hcandidateData := mem_propositionSixTwoCandidates.mp hnearData.1
  have hmZero : candidate.2 ≠ 0 := by
    intro hm
    apply zero_not_mem_propositionSixTwoCofactorCarrier_of_outer_mem
      hcandidateData.1
    simpa only [← hm] using hcandidateData.2
  have hmOne := propositionSixTwoNearCandidate_cofactor_ne_one
    hrhoSq hcandidate
  have hmGt : 1 < candidate.2 := by omega
  rw [List.length_pos_iff, Nat.primeFactorsList_ne_nil]
  exact hmGt

/--
A near candidate's complete prime-factor arity satisfies the real bound. No comparison between
the near width and theta gap is used.
-/
theorem propositionSixTwoNearCandidate_totalArity_le_two_div
    {epsilon rho : Real} {ell length : Nat} {I : Finset (Fin ell)}
    {j : Fin ell} {region : Set (Fin ell -> Real)}
    {band : SectionSixDirectBand} {C : Finset Nat}
    {candidate : PropositionSixTwoCandidate ell}
    (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hcandidate : candidate ∈ propositionSixTwoNearCandidates
      epsilon ell I j region length band rho C) :
    (((ell + candidate.2.primeFactorsList.length : Nat) : Real) <=
      2 / sectionSixThetaGap epsilon) := by
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  have hXNat : 1 < XNat := by
    dsimp [XNat]
    exact Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < (10 : Nat))
  have hnearData := mem_propositionSixTwoNearCandidates.mp hcandidate
  have hcandidateData := mem_propositionSixTwoCandidates.mp hnearData.1
  have hpData :=
    mem_propositionSixTwoPrimeTuples_iff_source.mp hcandidateData.1
  dsimp [IsPropositionSixTwoPrimeTuple] at hpData
  have hmZero : candidate.2 ≠ 0 := by
    intro hm
    apply zero_not_mem_propositionSixTwoCofactorCarrier_of_outer_mem
      hcandidateData.1
    simpa only [← hm] using hcandidateData.2
  have hroughData :=
    (mem_propositionSixTwoCofactorCarrier.mp hcandidateData.2).2
  have hrough : strictRoughPredicate
      (X ^ sectionSixThetaGap epsilon) candidate.2 := by
    intro q hqPrime hqDvd
    have hq := hroughData q hqPrime hqDvd
    exact (hpData.2.2.1 j).trans_lt (by simpa only [X, XNat] using hq)
  have hproduct :
      primeTupleProduct candidate.1 * candidate.2 < XNat := by
    have hnearUpper := (mem_typeIINearXCarrier.mp hnearData.2).1
    rw [PropositionSixTwoCandidate.value_eq_mul_primeTupleProduct_of_mem
      hnearData.1] at hnearUpper
    simpa only [XNat, Nat.mul_comm] using hnearUpper
  apply typeIIStableFactorArity_le_two_div_eta hXNat
    (sectionSix_parameter_bounds hepsilon hepsilonSmall).1 hmZero hpData.1
  · simpa only [X, XNat] using hpData.2.2.1
  · exact hrough
  · exact hproduct

/-- The residual arity is bounded by the canonical natural ceiling. -/
theorem propositionSixTwoNearCandidate_residualLength_le_ceil_two_div
    {epsilon rho : Real} {ell length : Nat} {I : Finset (Fin ell)}
    {j : Fin ell} {region : Set (Fin ell -> Real)}
    {band : SectionSixDirectBand} {C : Finset Nat}
    {candidate : PropositionSixTwoCandidate ell}
    (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hcandidate : candidate ∈ propositionSixTwoNearCandidates
      epsilon ell I j region length band rho C) :
    candidate.2.primeFactorsList.length <=
      Nat.ceil (2 / sectionSixThetaGap epsilon) := by
  have htotal := propositionSixTwoNearCandidate_totalArity_le_two_div
    hepsilon hepsilonSmall hlength hcandidate
  have hcomplete : ell + candidate.2.primeFactorsList.length <=
      Nat.ceil (2 / sectionSixThetaGap epsilon) := by
    exact_mod_cast htotal.trans
      (Nat.le_ceil (2 / sectionSixThetaGap epsilon))
  omega

/-- Every near candidate has a concrete tag at the canonical ceiling. -/
theorem exists_propositionSixTwoStablePattern_of_mem_nearCandidates
    {epsilon rho : Real} {ell length : Nat} {I : Finset (Fin ell)}
    {j : Fin ell} {region : Set (Fin ell -> Real)}
    {band : SectionSixDirectBand} {C : Finset Nat}
    {candidate : PropositionSixTwoCandidate ell}
    (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hcandidate : candidate ∈ propositionSixTwoNearCandidates
      epsilon ell I j region length band rho C) :
    ∃ pattern : PropositionSixTwoStablePattern ell
        (Nat.ceil (2 / sectionSixThetaGap epsilon)),
      candidate.stablePatternTag
        (Nat.ceil (2 / sectionSixThetaGap epsilon)) = some pattern := by
  have hbound :=
    propositionSixTwoNearCandidate_residualLength_le_ceil_two_div
      hepsilon hepsilonSmall hlength hcandidate
  unfold PropositionSixTwoCandidate.stablePatternTag
  rw [dif_pos hbound]
  exact ⟨_, rfl⟩

/-- Near candidate occurrences partition exactly over all stable patterns at
the canonical ceiling. -/
theorem card_propositionSixTwoNearCandidates_eq_sum_stablePatterns
    (epsilon rho : Real) (ell : Nat) (I : Finset (Fin ell)) (j : Fin ell)
    (region : Set (Fin ell -> Real)) (length : Nat)
    (band : SectionSixDirectBand) (C : Finset Nat)
    (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length) :
    (propositionSixTwoNearCandidates epsilon ell I j region length band rho
      C).card =
      ∑ pattern : PropositionSixTwoStablePattern ell
          (Nat.ceil (2 / sectionSixThetaGap epsilon)),
        (propositionSixTwoNearCandidatesOfStablePattern epsilon rho ell I j
          region length band C (Nat.ceil (2 / sectionSixThetaGap epsilon))
          pattern).card := by
  classical
  let M := Nat.ceil (2 / sectionSixThetaGap epsilon)
  let S := propositionSixTwoNearCandidates epsilon ell I j region length band
    rho C
  let tag : PropositionSixTwoCandidate ell ->
      Option (PropositionSixTwoStablePattern ell M) :=
    fun candidate => candidate.stablePatternTag M
  let tags : Finset (Option (PropositionSixTwoStablePattern ell M)) :=
    Finset.univ.map Function.Embedding.some
  have hmaps : Set.MapsTo tag (S : Set (PropositionSixTwoCandidate ell))
      (tags : Set (Option (PropositionSixTwoStablePattern ell M))) := by
    intro candidate hcandidate
    change candidate ∈ S at hcandidate
    obtain ⟨pattern, hpattern⟩ :=
      exists_propositionSixTwoStablePattern_of_mem_nearCandidates
        hepsilon hepsilonSmall hlength (by simpa only [S] using hcandidate)
    have htag : tag candidate = some pattern := by
      simpa only [tag, M] using hpattern
    rw [htag]
    simp [tags]
  have hdecomp := Finset.card_eq_sum_card_fiberwise hmaps
  calc
    (propositionSixTwoNearCandidates epsilon ell I j region length band rho
        C).card =
        ∑ tagValue ∈ tags,
          (S.filter fun candidate => tag candidate = tagValue).card := by
      simpa only [S] using hdecomp
    _ = ∑ pattern : PropositionSixTwoStablePattern ell M,
        (S.filter fun candidate => tag candidate = some pattern).card := by
      simp [tags]
    _ = ∑ pattern : PropositionSixTwoStablePattern ell
          (Nat.ceil (2 / sectionSixThetaGap epsilon)),
        (propositionSixTwoNearCandidatesOfStablePattern epsilon rho ell I j
          region length band C (Nat.ceil (2 / sectionSixThetaGap epsilon))
          pattern).card := by
      simp [M, S, tag, propositionSixTwoNearCandidatesOfStablePattern]

private theorem propositionSixTwoStableOuterPosition_strictMono
    {ell : Nat} {outer : Fin ell -> Nat} {m : Nat}
    (houter : Monotone outer) :
    StrictMono (typeIIStableOuterPositionEmbedding outer m) := by
  intro i k hik
  let a := typeIIStableOuterPositionEmbedding outer m i
  let b := typeIIStableOuterPositionEmbedding outer m k
  have habne : a ≠ b := by
    intro hab
    exact hik.ne ((typeIIStableOuterPositionEmbedding outer m).injective hab)
  rcases lt_or_gt_of_ne habne with hab | hba
  · exact hab
  · have hsorted := monotone_typeIIStableFactorTuple outer m hba.le
    have hki : outer k <= outer i := by
      simpa [a, b, typeIIStableFactorTuple_at_outerPositionEmbedding] using
        hsorted
    have heq : outer k = outer i := le_antisymm hki (houter hik.le)
    have htuple : typeIIStableFactorTuple outer m b =
        typeIIStableFactorTuple outer m a := by
      simpa [a, b, typeIIStableFactorTuple_at_outerPositionEmbedding] using heq
    have hsource := typeIIStableFactorPermutation_tie outer m hba htuple
    have hsource' :
        (Fin.castAdd m.primeFactorsList.length k :
          Fin (ell + m.primeFactorsList.length)) <
        Fin.castAdd m.primeFactorsList.length i := by
      simpa [a, b, typeIIStableOuterPositionEmbedding] using hsource
    have hik' :
        (Fin.castAdd m.primeFactorsList.length i :
          Fin (ell + m.primeFactorsList.length)) <
        Fin.castAdd m.primeFactorsList.length k := hik
    exact (lt_asymm hik' hsource').elim

/-- Every realized displayed-position embedding is strictly increasing. -/
theorem propositionSixTwoStablePattern_strictMono_of_mem
    {epsilon : Real} {ell length M : Nat} {I : Finset (Fin ell)}
    {j : Fin ell} {region : Set (Fin ell -> Real)}
    {band : SectionSixDirectBand} {C : Finset Nat}
    {pattern : PropositionSixTwoStablePattern ell M}
    {candidate : PropositionSixTwoCandidate ell}
    (hcandidate : candidate ∈ propositionSixTwoCandidatesOfStablePattern
      epsilon ell I j region length band C M pattern) :
    StrictMono pattern.2 := by
  have hslice := mem_propositionSixTwoCandidatesOfStablePattern.mp hcandidate
  have hcandidateData := mem_propositionSixTwoCandidates.mp hslice.1
  have hpData :=
    mem_propositionSixTwoPrimeTuples_iff_source.mp hcandidateData.1
  have htag :=
    PropositionSixTwoCandidate.stablePatternTag_eq_some_data hslice.2
  have hraw := propositionSixTwoStableOuterPosition_strictMono
    (m := candidate.2) hpData.2.1
  intro i k hik
  have hikRaw := hraw hik
  change (pattern.2 i).1 < (pattern.2 k).1
  rw [← htag.2 i, ← htag.2 k]
  exact hikRaw

/-- Strict roughness places the arbitrary distinguished displayed coordinate
before every stable position outside the displayed embedding range. -/
theorem propositionSixTwoStablePattern_distinguished_lt_offRange_of_mem
    {epsilon : Real} {ell length M : Nat} {I : Finset (Fin ell)}
    {j : Fin ell} {region : Set (Fin ell -> Real)}
    {band : SectionSixDirectBand} {C : Finset Nat}
    {pattern : PropositionSixTwoStablePattern ell M}
    {candidate : PropositionSixTwoCandidate ell}
    (hcandidate : candidate ∈ propositionSixTwoCandidatesOfStablePattern
      epsilon ell I j region length band C M pattern) :
    ∀ z, z ∉ Set.range pattern.2 -> pattern.2 j < z := by
  have hslice := mem_propositionSixTwoCandidatesOfStablePattern.mp hcandidate
  have hcandidateData := mem_propositionSixTwoCandidates.mp hslice.1
  have htag :=
    PropositionSixTwoCandidate.stablePatternTag_eq_some_data hslice.2
  let hdim : ell + candidate.2.primeFactorsList.length =
      ell + pattern.1.1 := congrArg (fun k => ell + k) htag.1
  let cast : Fin (ell + candidate.2.primeFactorsList.length) ≃o
      Fin (ell + pattern.1.1) := Fin.castOrderIso hdim
  let outerPositions :=
    typeIIStableOuterPositionEmbedding candidate.1 candidate.2
  let residualPositions :=
    typeIIStableResidualPositionEmbedding candidate.1 candidate.2
  have hposition (i : Fin ell) : cast (outerPositions i) = pattern.2 i := by
    apply Fin.ext
    simp only [cast, Fin.castOrderIso_apply, Fin.val_cast, outerPositions]
    exact htag.2 i
  have hrough :=
    (mem_propositionSixTwoCofactorCarrier.mp hcandidateData.2).2
  intro z hz
  let rawZ := cast.symm z
  rcases typeIIStablePosition_cases candidate.1 candidate.2 rawZ with
      houter | hresidual
  · rcases houter with ⟨i, hi⟩
    exfalso
    apply hz
    refine ⟨i, ?_⟩
    calc
      pattern.2 i = cast (outerPositions i) := (hposition i).symm
      _ = cast rawZ := congrArg cast hi
      _ = z := cast.apply_symm_apply z
  · rcases hresidual with ⟨r, hr⟩
    have hrMem : candidate.2.primeFactorsList.get r ∈
        candidate.2.primeFactorsList := List.get_mem _ r
    have hstrict := hrough _ (Nat.prime_of_mem_primeFactorsList hrMem)
      (Nat.dvd_of_mem_primeFactorsList hrMem)
    have hle : candidate.1 j <= candidate.2.primeFactorsList.get r := by
      exact_mod_cast hstrict.le
    have hrawLt := typeIIStableOuterPosition_lt_residualPosition_of_le
      candidate.1 candidate.2 hle
    have hcastLt := cast.strictMono hrawLt
    calc
      pattern.2 j = cast (outerPositions j) := (hposition j).symm
      _ < cast (residualPositions r) := hcastLt
      _ = cast rawZ := congrArg cast hr
      _ = z := cast.apply_symm_apply z

/-- One near realization supplies all finite structural data required by the
later fixed-pattern affine transfer. -/
theorem propositionSixTwoStablePattern_realizedData_of_mem
    {epsilon rho : Real} {ell length M : Nat} {I : Finset (Fin ell)}
    {j : Fin ell} {region : Set (Fin ell -> Real)}
    {band : SectionSixDirectBand} {C : Finset Nat}
    {pattern : PropositionSixTwoStablePattern ell M}
    {candidate : PropositionSixTwoCandidate ell}
    (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hrhoSq : rho ^ 2 <= sectionSixThetaGap epsilon)
    (hcandidate : candidate ∈
      propositionSixTwoNearCandidatesOfStablePattern epsilon rho ell I j
        region length band C M pattern) :
    0 < pattern.1.1 ∧
      (((ell + pattern.1.1 : Nat) : Real) <=
        2 / sectionSixThetaGap epsilon) ∧
      StrictMono pattern.2 ∧
      ∀ z, z ∉ Set.range pattern.2 -> pattern.2 j < z := by
  have hslice :=
    mem_propositionSixTwoNearCandidatesOfStablePattern.mp hcandidate
  have hnearData := mem_propositionSixTwoNearCandidates.mp hslice.1
  have hcomplete : candidate ∈ propositionSixTwoCandidatesOfStablePattern
      epsilon ell I j region length band C M pattern :=
    mem_propositionSixTwoCandidatesOfStablePattern.mpr
      ⟨hnearData.1, hslice.2⟩
  have htag :=
    PropositionSixTwoCandidate.stablePatternTag_eq_some_data hslice.2
  have hresidual := propositionSixTwoNearCandidate_residualLength_pos
    hrhoSq hslice.1
  have harity := propositionSixTwoNearCandidate_totalArity_le_two_div
    hepsilon hepsilonSmall hlength hslice.1
  refine ⟨?_, ?_,
    propositionSixTwoStablePattern_strictMono_of_mem hcomplete,
    propositionSixTwoStablePattern_distinguished_lt_offRange_of_mem hcomplete⟩
  · simpa only [htag.1] using hresidual
  · simpa only [htag.1] using harity

end

end PrimesRestrictedDigits
