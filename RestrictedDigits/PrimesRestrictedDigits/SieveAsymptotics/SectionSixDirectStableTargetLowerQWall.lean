import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStableTargetRegion
import PrimesRestrictedDigits.SieveAsymptotics.TypeIINearNormalization

/-!
# Direct stable-target lower-q wall

Failure of the strict direct lower-q inequality inside E2's weak displayed region forces
equality and hence membership in the corresponding projected wall slab at the retained
target-normalized factor tuple.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- A retained target factor tuple whose weak base-X q lower bound is not
strict lies on the literal lower-q wall in AG/Y's projected format. -/
theorem sectionSixDirectStableTargetFactors_exists_lowerQWall_of_not_strict
    {epsilon delta rho : Real} {ell length M N : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {sourcePresentation : TypeIIAffineHalfspacePresentation region}
    {pattern : SectionSixDirectStablePattern ell M}
    {factors : Fin ((ell + pattern.1.1) + 1) -> Nat}
    (hlength : 1 <= length)
    (hnear : N ∈ typeIINearXCarrier (10 ^ length) rho)
    (hprime : ∀ i, (factors i).Prime)
    (hproduct : primeTupleProduct factors = N)
    (htarget :
      (fun i => normalizedPrimeLog N (factors i)) ∈
        sectionSixDirectStableTargetRegion
          epsilon delta region band pattern)
    (hdisplayX :
      (fun i => normalizedPrimeLog (10 ^ length)
        (factors (pattern.canonicalDisplayedEmbedding i))) ∈
          sectionSixDirectDisplayedBandRegion epsilon delta region band)
    (spare : Fin ((ell + pattern.1.1) + 1))
    (hspare : spare ∉ Set.range pattern.canonicalDisplayedEmbedding)
    (hqNotStrict :
      ¬ (((10 ^ length : Nat) : Real) ^ delta <
        (factors (pattern.canonicalDisplayedEmbedding 0) : Real))) :
    let P := sectionSixDirectDisplayedBandPresentation
      sourcePresentation epsilon delta band
    ∃ j : Fin P.constraintCount,
      typeIIProjectedAffineNormal
          (typeIIAffineLiftNormal pattern.canonicalDisplayedEmbedding
            (P.normal j)) ≠ 0 ∧
      |typeIIAffineValue
            (typeIIProjectedAffineNormal
              (typeIIAffineLiftNormal pattern.canonicalDisplayedEmbedding
                (P.normal j)))
            (Fin.init (fun i => normalizedPrimeLog N (factors i))) -
          typeIIProjectedAffineBound
            (typeIIAffineLiftNormal pattern.canonicalDisplayedEmbedding
              (P.normal j))
            (P.bound j)| <=
        rho ^ 2 * typeIIAffineNormalMass (P.normal j) := by
  dsimp only
  let P := sectionSixDirectDisplayedBandPresentation
    sourcePresentation epsilon delta band
  obtain ⟨j, hjnormal, hjbound⟩ :=
    exists_sectionSixDirectDisplayedBandLowerQConstraint
      sourcePresentation epsilon delta band
  let embedding := pattern.canonicalDisplayedEmbedding
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let q : Nat := factors (embedding 0)
  have hXNat : 1 < XNat := by
    dsimp only [XNat]
    exact Nat.one_lt_pow (by omega : length ≠ 0) (by norm_num)
  have hX : (1 : Real) < X := by
    dsimp only [X, XNat]
    exact_mod_cast hXNat
  have htargetData := mem_sectionSixDirectStableTargetRegion.mp htarget
  have hsum : (∑ i, normalizedPrimeLog N (factors i)) = 1 :=
    htargetData.1.2.2
  have hdisplayData := mem_sectionSixDirectDisplayedBandRegion.mp hdisplayX
  have hqLower : delta <= normalizedPrimeLog XNat q := by
    have h := hdisplayData.2.1
    simpa only [q, embedding] using h
  have hqPrime : q.Prime := hprime _
  have hqPos : (0 : Real) < (q : Real) := by
    exact_mod_cast hqPrime.pos
  have hqUpperNat : (q : Real) <= X ^ delta := by
    have hnot := not_lt.mp hqNotStrict
    simpa only [q, X] using hnot
  have hqUpper : normalizedPrimeLog XNat q <= delta := by
    change Real.logb X (q : Real) <= delta
    exact (Real.logb_le_iff_le_rpow hX hqPos).mpr hqUpperNat
  have hqEq : normalizedPrimeLog XNat q = delta :=
    le_antisymm hqUpper hqLower
  have hN : 1 < N := by
    let i0 : Fin ((ell + pattern.1.1) + 1) := 0
    have hcoordinate : factors i0 <= primeTupleProduct factors :=
      primeTupleCoordinate_le_product (fun i => (hprime i).one_le) i0
    rw [hproduct] at hcoordinate
    exact (hprime i0).one_lt.trans_le hcoordinate
  have hNX : N < XNat := (mem_typeIINearXCarrier.mp hnear).1
  have hnearLower : X ^ (1 - rho ^ 2) < (N : Real) := by
    simpa only [X, XNat] using (mem_typeIINearXCarrier.mp hnear).2
  have herror := abs_typeIIAffineValue_normalizedPrimeLog_sub_le
    (normal := typeIIAffineLiftNormal embedding (P.normal j))
    (p := factors) hXNat hN hnearLower hNX hprime hproduct
  have hsourceValue :
      typeIIAffineValue
          (typeIIAffineLiftNormal embedding (P.normal j))
          (fun i => normalizedPrimeLog XNat (factors i)) =
        P.bound j := by
    rw [typeIIAffineValue_liftNormal, hjnormal, hjbound]
    simp [typeIIAffineValue, Pi.single_apply, q, hqEq]
  have hfullWall :
      |typeIIAffineValue
          (typeIIAffineLiftNormal embedding (P.normal j))
          (fun i => normalizedPrimeLog N (factors i)) - P.bound j| <=
        rho ^ 2 * typeIIAffineNormalMass (P.normal j) := by
    rw [← hsourceValue]
    calc
      _ <= rho ^ 2 * typeIIAffineNormalMass
          (typeIIAffineLiftNormal embedding (P.normal j)) := herror
      _ = rho ^ 2 * typeIIAffineNormalMass (P.normal j) := by
        rw [typeIIAffineNormalMass_liftNormal]
  have hnormal : P.normal j ≠ 0 := by
    rw [hjnormal]
    intro hz
    have := congrFun hz (0 : Fin (ell + 1))
    simp at this
  refine ⟨j, ?_, ?_⟩
  · exact typeIIProjectedAffineNormal_lift_ne_zero_of_offRange
      embedding (P.normal j) hnormal hspare
  · have hcomplete : completeProjectedLogTuple
        (Fin.init (fun i => normalizedPrimeLog N (factors i))) =
          (fun i => normalizedPrimeLog N (factors i)) :=
      completeProjectedLogTuple_init_eq_of_sum_eq_one hsum
    have hvalue := typeIIAffineValue_completeProjectedLogTuple
      (typeIIAffineLiftNormal embedding (P.normal j))
      (Fin.init (fun i => normalizedPrimeLog N (factors i)))
    rw [hcomplete] at hvalue
    have hprojected :
        typeIIAffineValue
            (typeIIProjectedAffineNormal
              (typeIIAffineLiftNormal embedding (P.normal j)))
            (Fin.init (fun i => normalizedPrimeLog N (factors i))) -
          typeIIProjectedAffineBound
            (typeIIAffineLiftNormal embedding (P.normal j))
            (P.bound j) =
        typeIIAffineValue
            (typeIIAffineLiftNormal embedding (P.normal j))
            (fun i => normalizedPrimeLog N (factors i)) - P.bound j := by
      unfold typeIIProjectedAffineBound
      rw [hvalue]
      ring
    change |typeIIAffineValue
          (typeIIProjectedAffineNormal
            (typeIIAffineLiftNormal embedding (P.normal j)))
          (Fin.init (fun i => normalizedPrimeLog N (factors i))) -
        typeIIProjectedAffineBound
          (typeIIAffineLiftNormal embedding (P.normal j))
          (P.bound j)| <= _
    rw [hprojected]
    exact hfullWall

end

end PrimesRestrictedDigits
