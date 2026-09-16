import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoStablePatternCoverage
import PrimesRestrictedDigits.SieveAsymptotics.PropositionSixTwoStableTargetRegion
import PrimesRestrictedDigits.SieveAsymptotics.TypeIINearStableFactorization
import PrimesRestrictedDigits.SieveAsymptotics.TypeIINearNormalization

/-!
# Proposition 6.2 stable-pattern forward data

One near candidate in a fixed stable-pattern fiber supplies its complete prime tuple at both
logarithmic bases. This is the forward factorization and normalization step in Maynard's proof
of Lemma 7.3 (`MAYNARD-PRD-PUBLISHED`, pp. 149--152).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- Normalized logarithms add over an arbitrary coordinate subproduct,
including the empty subproduct. -/
theorem sum_normalizedPrimeLog_finset_eq_subproduct
    {X ell : Nat} (p : Fin ell -> Nat) (I : Finset (Fin ell))
    (hp : forall i, p i ≠ 0) :
    (∑ i ∈ I, normalizedPrimeLog X (p i)) =
      normalizedPrimeLog X (primeTupleSubproduct p I) := by
  change (∑ i ∈ I, Real.logb (X : Real) (p i : Real)) =
    Real.logb (X : Real) (primeTupleSubproduct p I : Real)
  rw [primeTupleSubproduct, Nat.cast_prod,
    Real.logb_prod I (fun i => (p i : Real))]
  intro i _hi
  exact_mod_cast hp i

/-- A near candidate in one stable-pattern fiber supplies its exact complete
factor tuple, its base-product simplex point, its base-`X` displayed point,
and the forward landing-or-displayed-failure alternative. -/
theorem propositionSixTwoStablePattern_exists_forwardData_of_mem
    {epsilon rho : Real} {ell length M : Nat}
    {I : Finset (Fin ell)} {j : Fin ell}
    {sourceRegion : Set (Fin ell -> Real)}
    {band : SectionSixDirectBand} {C : Finset Nat}
    {pattern : PropositionSixTwoStablePattern ell M}
    {candidate : PropositionSixTwoCandidate ell}
    (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hcandidate : candidate ∈
      propositionSixTwoNearCandidatesOfStablePattern
        epsilon rho ell I j sourceRegion length band C M pattern) :
    ∃ factors : Fin (ell + pattern.1.1) -> Nat,
      (∀ z, (factors z).Prime) ∧
      primeTupleProduct factors = candidate.value ∧
      1 < candidate.value ∧
      candidate.value ∈ typeIINearXCarrier (10 ^ length) rho ∧
      candidate.value < 10 ^ length ∧
      candidate.value ∈ C ∧
      (fun z => normalizedPrimeLog candidate.value (factors z)) ∈
        typeIIExponentSimplex (sectionSixThetaGap epsilon) ∧
      (fun i => normalizedPrimeLog (10 ^ length)
        (factors (pattern.2 i))) ∈
        propositionSixTwoDisplayedRegion epsilon I sourceRegion band ∧
      (∀ normal,
        |typeIIAffineValue normal
              (fun z => normalizedPrimeLog candidate.value (factors z)) -
            typeIIAffineValue normal
              (fun z => normalizedPrimeLog (10 ^ length) (factors z))| <=
          rho ^ 2 * typeIIAffineNormalMass normal) ∧
      (candidate.value ∈ typeIIOriginalRegionSupport (10 ^ length)
          (propositionSixTwoStableTargetRegion
            epsilon I sourceRegion band pattern) ∨
        (fun i => normalizedPrimeLog candidate.value
          (factors (pattern.2 i))) ∉
            propositionSixTwoDisplayedRegion
              epsilon I sourceRegion band) := by
  have hslice :=
    mem_propositionSixTwoNearCandidatesOfStablePattern.mp hcandidate
  have hnearData := mem_propositionSixTwoNearCandidates.mp hslice.1
  have hcandidateData := mem_propositionSixTwoCandidates.mp hnearData.1
  rcases candidate with ⟨p, m⟩
  have hpData :=
    mem_propositionSixTwoPrimeTuples_iff_source.mp hcandidateData.1
  dsimp [IsPropositionSixTwoPrimeTuple] at hpData
  have hmData :=
    mem_propositionSixTwoCofactorCarrier.mp hcandidateData.2
  have hmZero : m ≠ 0 := by
    intro hm
    subst m
    exact zero_not_mem_propositionSixTwoCofactorCarrier_of_outer_mem
      hcandidateData.1 hcandidateData.2
  have hvalue :
      PropositionSixTwoCandidate.value (Sigma.mk p m) =
        m * primeTupleProduct p :=
    PropositionSixTwoCandidate.value_eq_mul_primeTupleProduct_of_mem
      hnearData.1
  have hmPos : 0 < m := Nat.pos_of_ne_zero hmZero
  have hproductTwo : 2 <= primeTupleProduct p :=
    (hpData.1 j).two_le.trans
      (primeTupleCoordinate_le_product
        (fun i => (hpData.1 i).one_le) j)
  have hvalueGtRaw : 1 < m * primeTupleProduct p := by
    have hproductLe : primeTupleProduct p <= m * primeTupleProduct p :=
      Nat.le_mul_of_pos_left _ hmPos
    omega
  have hvalueGt :
      1 < PropositionSixTwoCandidate.value (Sigma.mk p m) := by
    rw [hvalue]
    exact hvalueGtRaw
  have hnear : PropositionSixTwoCandidate.value (Sigma.mk p m) ∈
      typeIINearXCarrier (10 ^ length) rho := hnearData.2
  have hvalueUpper :
      PropositionSixTwoCandidate.value (Sigma.mk p m) < 10 ^ length :=
    (mem_typeIINearXCarrier.mp hnear).1
  have hXNat : 1 < 10 ^ length := hvalueGt.trans hvalueUpper
  have hX : (1 : Real) < ((10 ^ length : Nat) : Real) := by
    exact_mod_cast hXNat
  have hvalueC :
      PropositionSixTwoCandidate.value (Sigma.mk p m) ∈ C := by
    exact mem_sieveDilation.mp hmData.1
  have hrough : strictRoughPredicate
      (((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon) m := by
    intro q hqPrime hqDvd
    exact (hpData.2.2.1 j).trans_lt (hmData.2 q hqPrime hqDvd)
  have hrawProduct :
      primeTupleProduct p * m =
        PropositionSixTwoCandidate.value (Sigma.mk p m) := by
    rw [hvalue, Nat.mul_comm]
  have hrawSimplex :
      (fun z => normalizedPrimeLog
        (PropositionSixTwoCandidate.value (Sigma.mk p m))
        (typeIIStableFactorTuple p m z)) ∈
          typeIIExponentSimplex (sectionSixThetaGap epsilon) :=
    normalized_typeIIStableFactorTuple_mem_exponentSimplex
      (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
      hmZero hpData.1 hpData.2.2.1 hrough hrawProduct hvalueGt hvalueUpper
  have htagData :=
    PropositionSixTwoCandidate.stablePatternTag_eq_some_data hslice.2
  let hdim : ell + m.primeFactorsList.length = ell + pattern.1.1 :=
    congrArg (fun k => ell + k) htagData.1
  let cast : Fin (ell + m.primeFactorsList.length) ≃o
      Fin (ell + pattern.1.1) := Fin.castOrderIso hdim
  let actualFactors := typeIIStableFactorTuple p m
  let factors : Fin (ell + pattern.1.1) -> Nat :=
    actualFactors ∘ cast.symm
  have hfactorsPrime : forall z, (factors z).Prime := by
    intro z
    exact prime_typeIIStableFactorTuple p m hpData.1 (cast.symm z)
  have hfactorsProduct : primeTupleProduct factors =
      PropositionSixTwoCandidate.value (Sigma.mk p m) := by
    calc
      primeTupleProduct factors = primeTupleProduct actualFactors := by
        exact Equiv.prod_comp cast.symm.toEquiv actualFactors
      _ = primeTupleProduct p * m :=
        primeTupleProduct_typeIIStableFactorTuple p m hmZero
      _ = PropositionSixTwoCandidate.value (Sigma.mk p m) := hrawProduct
  have hposition (i : Fin ell) :
      cast (typeIIStableOuterPositionEmbedding p m i) = pattern.2 i := by
    apply Fin.ext
    simp only [cast, Fin.castOrderIso_apply, Fin.val_cast]
    exact htagData.2 i
  have hfactorDisplayed (i : Fin ell) :
      factors (pattern.2 i) = p i := by
    change actualFactors (cast.symm (pattern.2 i)) = p i
    rw [← hposition i, cast.symm_apply_apply]
    exact typeIIStableFactorTuple_at_outerPositionEmbedding p m i
  have hsimplex :
      (fun z => normalizedPrimeLog
        (PropositionSixTwoCandidate.value (Sigma.mk p m)) (factors z)) ∈
          typeIIExponentSimplex (sectionSixThetaGap epsilon) := by
    refine ⟨?_, ?_, ?_⟩
    · intro z
      exact hrawSimplex.1 (cast.symm z)
    · exact hrawSimplex.2.1.comp cast.symm.monotone
    · change (∑ z, normalizedPrimeLog
          (PropositionSixTwoCandidate.value (Sigma.mk p m))
          (actualFactors (cast.symm z))) = 1
      exact (Equiv.sum_comp cast.symm.toEquiv
        (fun z => normalizedPrimeLog
          (PropositionSixTwoCandidate.value (Sigma.mk p m))
          (actualFactors z))).trans hrawSimplex.2.2
  have hpLogLower : forall i, sectionSixThetaGap epsilon <=
      normalizedPrimeLog (10 ^ length) (p i) := by
    intro i
    change sectionSixThetaGap epsilon <=
      Real.logb ((10 ^ length : Nat) : Real) (p i : Real)
    exact (Real.le_logb_iff_rpow_le hX
      (by exact_mod_cast (hpData.1 i).pos)).2 (hpData.2.2.1 i)
  have hsubproductPos :
      (0 : Real) < (primeTupleSubproduct p I : Real) := by
    exact_mod_cast (show 0 < primeTupleSubproduct p I by
      unfold primeTupleSubproduct
      exact Finset.prod_pos fun i _hi => (hpData.1 i).pos)
  have hsum :
      (∑ i ∈ I, normalizedPrimeLog (10 ^ length) (p i)) =
        normalizedPrimeLog (10 ^ length) (primeTupleSubproduct p I) :=
    sum_normalizedPrimeLog_finset_eq_subproduct p I
      (fun i => (hpData.1 i).ne_zero)
  have hbandLog :
      propositionSixTwoBandLower epsilon band <=
          ∑ i ∈ I, normalizedPrimeLog (10 ^ length) (p i) ∧
        (∑ i ∈ I, normalizedPrimeLog (10 ^ length) (p i)) <=
          propositionSixTwoBandUpper epsilon band := by
    cases band with
    | first =>
        have hrange := hpData.2.2.2.1
        simp only [sectionSixDirectRangeMembership_first] at hrange
        rw [hsum]
        exact ⟨
          (Real.le_logb_iff_rpow_le hX hsubproductPos).2 hrange.1,
          (Real.logb_le_iff_le_rpow hX hsubproductPos).2 hrange.2⟩
    | second =>
        have hrange := hpData.2.2.2.1
        simp only [sectionSixDirectRangeMembership_second] at hrange
        rw [hsum]
        exact ⟨
          (Real.le_logb_iff_rpow_le hX hsubproductPos).2 hrange.1,
          (Real.logb_le_iff_le_rpow hX hsubproductPos).2 hrange.2⟩
  have hdisplayRaw :
      (fun i => normalizedPrimeLog (10 ^ length) (p i)) ∈
        propositionSixTwoDisplayedRegion epsilon I sourceRegion band := by
    exact mem_propositionSixTwoDisplayedRegion.mpr
      ⟨hpData.2.2.2.2.2, hpLogLower, hbandLog⟩
  have hdisplay :
      (fun i => normalizedPrimeLog (10 ^ length)
        (factors (pattern.2 i))) ∈
        propositionSixTwoDisplayedRegion epsilon I sourceRegion band := by
    have hpoint :
        (fun i => normalizedPrimeLog (10 ^ length)
          (factors (pattern.2 i))) =
        fun i => normalizedPrimeLog (10 ^ length) (p i) := by
      funext i
      rw [hfactorDisplayed]
    rw [hpoint]
    exact hdisplayRaw
  have herror : forall normal,
      |typeIIAffineValue normal
            (fun z => normalizedPrimeLog
              (PropositionSixTwoCandidate.value (Sigma.mk p m))
              (factors z)) -
          typeIIAffineValue normal
            (fun z => normalizedPrimeLog (10 ^ length) (factors z))| <=
        rho ^ 2 * typeIIAffineNormalMass normal := by
    intro normal
    exact abs_typeIIAffineValue_normalizedPrimeLog_sub_le
      hXNat hvalueGt (mem_typeIINearXCarrier.mp hnear).2 hvalueUpper
      hfactorsPrime hfactorsProduct
  refine ⟨factors, hfactorsPrime, hfactorsProduct, hvalueGt, hnear,
    hvalueUpper, hvalueC, hsimplex, hdisplay, herror, ?_⟩
  by_cases hdisplayN :
      (fun i => normalizedPrimeLog
        (PropositionSixTwoCandidate.value (Sigma.mk p m))
        (factors (pattern.2 i))) ∈
          propositionSixTwoDisplayedRegion epsilon I sourceRegion band
  · left
    apply mem_typeIIOriginalRegionSupport.mpr
    refine ⟨hvalueUpper, factors, hfactorsPrime, hfactorsProduct, ?_⟩
    exact mem_propositionSixTwoStableTargetRegion.mpr
      ⟨hsimplex, hdisplayN⟩
  · exact Or.inr hdisplayN

end

end PrimesRestrictedDigits
