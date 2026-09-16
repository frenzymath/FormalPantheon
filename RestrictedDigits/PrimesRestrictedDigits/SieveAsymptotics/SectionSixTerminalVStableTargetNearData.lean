import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStableTargetRegion

/-!
# Near data from a terminal-V stable-pattern target support

This exposes the prime tuple and normalization data already contained in one near terminal-V
target-support member in the proof of Lemma 7.3 of `MAYNARD-PRD-PUBLISHED`, pp. 149--152 and
156--157.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- A near member of one terminal-V stable target support supplies its exact
base-N target tuple and the universal affine normalization error back to the
decimal scale. -/
theorem sectionSixTerminalVStableTargetSupport_exists_nearData_of_mem
    {epsilon delta rho : Real} {ell length M N : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixStateBand}
    {pattern : SectionSixTerminalVStablePattern ell M}
    (hnear : N ∈ typeIINearXCarrier (10 ^ length) rho)
    (htarget : N ∈ typeIIOriginalRegionSupport (10 ^ length)
      (sectionSixTerminalVStableTargetRegion
        epsilon delta region band pattern)) :
    ∃ factors : Fin ((pattern.1.1 + ell) + pattern.2.1.1) -> Nat,
      (∀ i, (factors i).Prime) ∧
      primeTupleProduct factors = N ∧
      1 < N ∧
      N < 10 ^ length ∧
      Monotone factors ∧
      (fun i => normalizedPrimeLog N (factors i)) ∈
        sectionSixTerminalVStableTargetRegion
          epsilon delta region band pattern ∧
      ∀ normal : Fin ((pattern.1.1 + ell) + pattern.2.1.1) -> Real,
        |typeIIAffineValue normal
              (fun i => normalizedPrimeLog N (factors i)) -
            typeIIAffineValue normal
              (fun i => normalizedPrimeLog (10 ^ length) (factors i))| <=
          rho ^ 2 * typeIIAffineNormalMass normal := by
  rcases mem_typeIIOriginalRegionSupport.mp htarget with
    ⟨hNX, factors, hprime, hproduct, hregion⟩
  obtain ⟨hinner, _hresidual, _⟩ :=
    mem_sectionSixTerminalVStableTargetRegion.mp hregion
  let i0 : Fin ((pattern.1.1 + ell) + pattern.2.1.1) :=
    ⟨0, by omega⟩
  have hcoordinate : factors i0 <= primeTupleProduct factors :=
    primeTupleCoordinate_le_product (fun i => (hprime i).one_le) i0
  have hN : 1 < N := by
    rw [hproduct] at hcoordinate
    exact (hprime i0).one_lt.trans_le hcoordinate
  have hmonotone : Monotone factors :=
    monotone_primeTuple_of_mem_typeIISourceRegion hN hprime
      (sectionSixTerminalVStableTargetRegion_isTypeIISourceRegion
        epsilon delta region band pattern) hregion
  have hX : 1 < 10 ^ length := hN.trans hNX
  refine ⟨factors, hprime, hproduct, hN, hNX, hmonotone, hregion, ?_⟩
  intro normal
  exact abs_typeIIAffineValue_normalizedPrimeLog_sub_le
    hX hN (mem_typeIINearXCarrier.mp hnear).2 hNX hprime hproduct

end

end PrimesRestrictedDigits
