import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStableTargetRegion

/-!
# Near data from a direct stable-pattern target support

This exposes the prime tuple and normalization data already contained in one near E2
target-support member in the proof of Lemma 7.3 of `MAYNARD-PRD-PUBLISHED`, pp. 150--152.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- A near member of one fixed E2 target support supplies a weakly increasing
prime tuple, the exact target constraints, and the universal affine
normalization error back to the decimal scale. -/
theorem sectionSixDirectStableTargetSupport_exists_nearData_of_mem
    {epsilon delta rho : Real} {ell length M N : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {pattern : SectionSixDirectStablePattern ell M}
    (hlength : 1 <= length)
    (hnear : N ∈ typeIINearXCarrier (10 ^ length) rho)
    (htarget : N ∈ typeIIOriginalRegionSupport (10 ^ length)
      (sectionSixDirectStableTargetRegion
        epsilon delta region band pattern)) :
    ∃ factors : Fin ((ell + pattern.1.1) + 1) -> Nat,
      (∀ i, (factors i).Prime) ∧
      primeTupleProduct factors = N ∧
      1 < N ∧
      N < 10 ^ length ∧
      Monotone factors ∧
      (fun i => normalizedPrimeLog N (factors i)) ∈
        typeIIExponentSimplex delta ∧
      (fun i => normalizedPrimeLog N
        (factors (pattern.canonicalDisplayedEmbedding i))) ∈
        sectionSixDirectDisplayedBandRegion epsilon delta region band ∧
      ∀ normal : Fin ((ell + pattern.1.1) + 1) -> Real,
        |typeIIAffineValue normal
              (fun i => normalizedPrimeLog N (factors i)) -
            typeIIAffineValue normal
              (fun i => normalizedPrimeLog (10 ^ length) (factors i))| <=
          rho ^ 2 * typeIIAffineNormalMass normal := by
  rcases mem_typeIIOriginalRegionSupport.mp htarget with
    ⟨hNX, factors, hprime, hproduct, hregion⟩
  let i0 : Fin ((ell + pattern.1.1) + 1) := 0
  have hcoordinate : factors i0 <= primeTupleProduct factors :=
    primeTupleCoordinate_le_product (fun i => (hprime i).one_le) i0
  have hN : 1 < N := by
    rw [hproduct] at hcoordinate
    exact (hprime i0).one_lt.trans_le hcoordinate
  have htargetData := mem_sectionSixDirectStableTargetRegion.mp hregion
  have hmonotone : Monotone factors :=
    monotone_primeTuple_of_mem_typeIISourceRegion hN hprime
      (sectionSixDirectStableTargetRegion_isTypeIISourceRegion
        epsilon delta region band pattern) hregion
  have hX : 1 < 10 ^ length :=
    Nat.one_lt_pow (by omega : length ≠ 0) (by norm_num)
  refine ⟨factors, hprime, hproduct, hN, hNX, hmonotone,
    htargetData.1, htargetData.2, ?_⟩
  intro normal
  exact abs_typeIIAffineValue_normalizedPrimeLog_sub_le
    hX hN (mem_typeIINearXCarrier.mp hnear).2 hNX hprime hproduct

end

end PrimesRestrictedDigits
