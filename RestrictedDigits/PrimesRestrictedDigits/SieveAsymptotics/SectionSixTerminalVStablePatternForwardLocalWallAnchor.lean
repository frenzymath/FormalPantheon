import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVStablePatternForwardMixedWall
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVBaseXCoreWallProjection
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixProjectedFactorsLocalWallAnchor
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVBaseXCoreLocalWallAnchors

/-!
# Terminal-V fixed-pattern forward local-wall anchor

This assigns the forward wall selected directly from its base-`X` terminal geometry to the
existing locally admissible wall family. It is the boundary-cell step in Lemma 7.3 of
`MAYNARD-PRD-PUBLISHED`, pp. 149--152.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private noncomputable def terminalVForwardDisplayedPositions
    {ell M : Nat} (pattern : SectionSixTerminalVStablePattern ell M) :
    Finset (Fin ((pattern.1.1 + ell) + pattern.2.1.1)) :=
  Finset.univ.map pattern.2.2

private theorem sum_terminalVForwardDisplayedPositions
    {ell M : Nat} (pattern : SectionSixTerminalVStablePattern ell M)
    (x : Fin ((pattern.1.1 + ell) + pattern.2.1.1) -> Real) :
    (∑ j ∈ terminalVForwardDisplayedPositions pattern, x j) =
      sectionSixTerminalVDisplayedSum pattern x := by
  rw [terminalVForwardDisplayedPositions, Finset.sum_map]
  rw [Fin.sum_univ_add]
  change (∑ i : Fin pattern.1.1, x (pattern.innerPositionEmbedding i)) +
      (∑ i : Fin ell, x (pattern.sourcePositionEmbedding i)) = _
  rw [sectionSixTerminalVDisplayedSum, sectionSixTerminalVSourceSum,
    sectionSixTerminalVInnerSum]
  ring

private theorem terminalVForwardDisplayedSum_bounds
    {epsilon delta : Real} {ell M : Nat}
    (band : SectionSixStateBand)
    (pattern : SectionSixTerminalVStablePattern ell M)
    (hinner : 0 < pattern.1.1) (hresidual : 0 < pattern.2.1.1)
    (x : Fin ((pattern.1.1 + ell) + pattern.2.1.1) -> Real)
    (hx : x ∈ sectionSixTerminalVFixedRegion epsilon delta band pattern
      hinner hresidual) :
    match band with
    | .low =>
        sectionSixThetaOne epsilon <
            sectionSixTerminalVDisplayedSum pattern x ∧
          sectionSixTerminalVDisplayedSum pattern x <=
            sectionSixThetaTwo epsilon
    | .high =>
        1 - sectionSixThetaTwo epsilon <
            sectionSixTerminalVDisplayedSum pattern x ∧
          sectionSixTerminalVDisplayedSum pattern x <=
            1 - sectionSixThetaOne epsilon := by
  have hfirstUpper := hx.1 (⟨0, hinner⟩ : Fin pattern.1.1)
  change x (pattern.firstInnerPosition hinner) <=
    sectionSixThetaGap epsilon at hfirstUpper
  cases band with
  | low =>
      have hcutoff := hx.2.2.1
      have hlower := hx.2.2.2.2.2.1
      simp only [sectionSixTerminalVCutoffExponent] at hcutoff
      refine ⟨hlower, ?_⟩
      simp only [sectionSixThetaGap] at hfirstUpper
      linarith
  | high =>
      have hcutoff := hx.2.2.1
      have hlower := hx.2.2.2.2.2.2.1
      simp only [sectionSixTerminalVCutoffExponent] at hcutoff
      refine ⟨hlower, ?_⟩
      simp only [sectionSixThetaGap] at hfirstUpper
      linarith

private theorem sum_terminalVForwardPrefixIndexSet_eq
    {k : Nat} (positions : Finset (Fin (k + 1)))
    (x : Fin (k + 1) -> Real) (hlast : Fin.last k ∉ positions) :
    (∑ i ∈ typeIIPrefixIndexSet positions, x i.castSucc) =
      ∑ j ∈ positions, x j := by
  rw [typeIIPrefixIndexSet, Finset.sum_filter]
  have hall := Fin.sum_univ_castSucc
    (fun j => if j ∈ positions then x j else 0)
  simp only [hlast, if_false, add_zero] at hall
  rw [← hall]
  have hfilter :=
    (Finset.sum_filter (s := Finset.univ) (fun j => j ∈ positions) x).symm
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter] at hfilter
  exact hfilter

private theorem terminalVForwardOneWidthSubsetSum_bounds
    {k : Nat} {rho : Real} {anchor : Fin k -> Nat}
    {z : Fin k -> Real} (hrho : 0 <= rho)
    (hz : z ∈ projectedLogBox (scaledNaturalCubeAnchor rho anchor) rho)
    (I : Finset (Fin k)) :
    (∑ i ∈ I, scaledNaturalCubeAnchor rho anchor i) <= ∑ i ∈ I, z i ∧
      (∑ i ∈ I, z i) <=
        (∑ i ∈ I, scaledNaturalCubeAnchor rho anchor i) +
          (k : Real) * rho := by
  constructor
  · exact Finset.sum_le_sum fun i _ => (hz i).1.le
  · calc
      (∑ i ∈ I, z i) <=
          ∑ i ∈ I, (scaledNaturalCubeAnchor rho anchor i + rho) :=
        Finset.sum_le_sum fun i _ => (hz i).2
      _ = (∑ i ∈ I, scaledNaturalCubeAnchor rho anchor i) +
          (I.card : Real) * rho := by
        simp [Finset.sum_add_distrib, nsmul_eq_mul]
      _ <= (∑ i ∈ I, scaledNaturalCubeAnchor rho anchor i) +
          (k : Real) * rho := by
        gcongr
        simpa using Finset.card_le_univ I

/-- A fixed-pattern terminal-V candidate outside its target support belongs
to one exact locally admissible literal-wall cell. -/
theorem sectionSixTerminalVStablePattern_exists_forwardLocalWallAnchor_of_mem
    {epsilon delta rho : Real} {ell length M : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixStateBand}
    (sourcePresentation : TypeIIAffineHalfspacePresentation region)
    {C : Finset Nat} {pattern : SectionSixTerminalVStablePattern ell M}
    {candidate : SectionSixTerminalVCandidate band ell}
    (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (hrho : 0 < rho)
    (hmarginWidth : 2 * rho <= delta / 2)
    (hconvenienceWidth :
      rho ^ 2 +
          (((((pattern.1.1 + ell) + pattern.2.1.1) - 1 : Nat) : Real) * rho) <=
        epsilon)
    (hcandidate : candidate ∈
      sectionSixSourceBandTerminalVNearCandidatesOfStablePattern region
        hepsilon hepsilonSmall hlength hdeltaGapStrict.le band C
          (((10 ^ length : Nat) : Real) ^ delta)
          (typeIINearXCarrier (10 ^ length) rho) M pattern)
    (houtside : candidate.represented ∉
      typeIIOriginalRegionSupport (10 ^ length)
        (sectionSixTerminalVStableTargetRegion
          epsilon delta region band pattern)) :
    ∃ hinner : 0 < pattern.1.1,
      ∃ hresidual : 0 < pattern.2.1.1,
        ∃ n : Nat,
          ∃ hdimension :
              (pattern.1.1 + ell) + pattern.2.1.1 = n + 2,
            let P := sectionSixTerminalVBaseXCorePresentation
              sourcePresentation epsilon delta band pattern hinner hresidual
            ∃ j : Fin P.constraintCount,
              ∃ anchor : Fin (n + 1) -> Nat,
                anchor ∈ sectionSixTerminalVBaseXCoreLocalWallAnchors
                    epsilon delta rho sourcePresentation band pattern hinner
                      hresidual n hdimension j ∧
                  candidate.represented ∈
                    (primeTupleProductSupport
                      (majorArcPrimeTuples (10 ^ length)
                        (scaledNaturalCubeAnchor rho anchor) rho delta)).filter
                          (fun m => m ∈ C) := by
  have hdelta : 0 < delta := by linarith
  have hgapUpper : sectionSixThetaGap epsilon < 1 := by
    rw [sectionSixThetaGap_eq]
    linarith
  have hrhoLtOne : rho < 1 := by linarith
  have hrhoHalf : rho <= 1 / 2 := by linarith
  have hrhoDelta : rho ^ 2 < delta := by
    nlinarith [mul_pos hrho (sub_pos.mpr hrhoLtOne)]
  obtain ⟨hinner, hresidual, factors, hprime, hproduct, hC, hnear,
      hsimplex, hcoreX, j, hnormal, hwall⟩ :=
    sectionSixTerminalVStablePattern_exists_forwardMixedWall_of_mem
      sourcePresentation hepsilon hepsilonSmall hlength hdeltaGapStrict
        hrhoDelta hcandidate houtside
  obtain ⟨n, hdimension, hprojected, hprojectedWall⟩ :=
    sectionSixTerminalVBaseXCoreWall_exists_projected band sourcePresentation
      pattern hinner hresidual
        (fun i => normalizedPrimeLog candidate.represented (factors i))
          hsimplex.2.2 j hnormal hwall
  let P := sectionSixTerminalVBaseXCorePresentation sourcePresentation
    epsilon delta band pattern hinner hresidual
  let cast : Fin ((pattern.1.1 + ell) + pattern.2.1.1) ≃o Fin (n + 2) :=
    Fin.castOrderIso hdimension
  let transportedFactors : Fin (n + 2) -> Nat := fun i =>
    factors (cast.symm i)
  let fullNormal : Fin (n + 2) -> Real := fun i =>
    P.normal j (cast.symm i)
  let eN : Fin (n + 2) -> Real := fun i =>
    normalizedPrimeLog candidate.represented (transportedFactors i)
  let eX : Fin (n + 2) -> Real := fun i =>
    normalizedPrimeLog (10 ^ length) (transportedFactors i)
  have hprimeTransported : ∀ i, (transportedFactors i).Prime := fun i =>
    hprime (cast.symm i)
  have hproductTransported :
      primeTupleProduct transportedFactors = candidate.represented := by
    unfold primeTupleProduct transportedFactors
    exact (Equiv.prod_comp cast.symm.toEquiv factors).trans hproduct
  have hsimplexTransported : eN ∈ typeIIExponentSimplex delta := by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      exact hsimplex.1 (cast.symm i)
    · intro i i' hii'
      exact hsimplex.2.1 (cast.symm.monotone hii')
    · exact (Equiv.sum_comp cast.symm.toEquiv
        (fun i => normalizedPrimeLog candidate.represented (factors i))).trans
          hsimplex.2.2
  have hprojected' : typeIIProjectedAffineNormal fullNormal ≠ 0 := by
    simpa only [P, cast, fullNormal] using hprojected
  have hprojectedWall' :
      |typeIIAffineValue (typeIIProjectedAffineNormal fullNormal)
            (Fin.init eN) -
          typeIIProjectedAffineBound fullNormal (P.bound j)| <=
        rho ^ 2 * typeIIAffineNormalMass (P.normal j) := by
    simpa only [P, cast, fullNormal, eN, transportedFactors] using
      hprojectedWall
  obtain ⟨anchor, hslab, hcell⟩ :=
    projectedFactors_exists_crossedWallAnchor hlength hdelta hrho hrhoHalf
      hnear hprimeTransported hproductTransported
        (hsimplexTransported.1 (Fin.last (n + 1))) hprojected'
          hprojectedWall'
  have hX : 1 < 10 ^ length :=
    Nat.one_lt_pow (by omega : length ≠ 0) (by norm_num)
  have hN : 1 < candidate.represented :=
    one_lt_of_mem_typeIINearXCarrier hX hrho hrhoHalf hnear
  have hNX : candidate.represented < 10 ^ length :=
    (mem_typeIINearXCarrier.mp hnear).1
  have hpLe (i : Fin (n + 2)) : transportedFactors i <=
      candidate.represented := by
    rw [← hproductTransported]
    exact primeTupleCoordinate_le_product
      (fun q => (hprimeTransported q).one_le) i
  have hcellData := mem_majorArcPrimeTuples_iff.mp hcell
  have hzCell : (fun i : Fin (n + 1) => eX i.castSucc) ∈
      projectedLogBox (scaledNaturalCubeAnchor rho anchor) rho := by
    simpa only [eX, Fin.init_def] using hcellData.2.1
  have heCell : ∀ i : Fin (n + 1),
      eN i.castSucc ∈ Set.Ioc (scaledNaturalCubeAnchor rho anchor i)
        (scaledNaturalCubeAnchor rho anchor i + 2 * rho) := by
    intro i
    exact normalizedPrimeLog_mem_doubled_Ioc_of_near hX hrho hrhoHalf hnear
      (hprimeTransported i.castSucc) (hpLe i.castSucc)
      (by simpa only [eX] using hzCell i)
  have hmargin : ∀ i : Fin (n + 1),
      delta / 2 <= scaledNaturalCubeAnchor rho anchor i := by
    intro i
    have hiLower := hsimplexTransported.1 i.castSucc
    have hiUpper := (heCell i).2
    linarith
  have hanchorPrefix :
      (∑ i, scaledNaturalCubeAnchor rho anchor i) <=
        ∑ i : Fin (n + 1), eN i.castSucc :=
    Finset.sum_le_sum fun i _ => (heCell i).1.le
  have hsumNDecomposition :
      (∑ i : Fin (n + 1), eN i.castSucc) + eN (Fin.last (n + 1)) = 1 := by
    exact (Fin.sum_univ_castSucc eN).symm.trans hsimplexTransported.2.2
  have hroom : (∑ i, scaledNaturalCubeAnchor rho anchor i) <
      1 - delta / 2 := by
    have hlastLower := hsimplexTransported.1 (Fin.last (n + 1))
    linarith
  have hsumX : (∑ i, eX i) =
      normalizedPrimeLog (10 ^ length) candidate.represented := by
    calc
      (∑ i, eX i) =
          ∑ i, normalizedPrimeLog (10 ^ length) (factors i) :=
        Equiv.sum_comp cast.symm.toEquiv
          (fun i => normalizedPrimeLog (10 ^ length) (factors i))
      _ = normalizedPrimeLog (10 ^ length) candidate.represented := by
        rw [sum_normalizedPrimeLog_eq_normalizedPrimeLog_product
          (fun i => (hprime i).ne_zero), hproduct]
  have hratio := normalizedPrimeLog_near_bounds hX
    (mem_typeIINearXCarrier.mp hnear).2 hNX
  let rawPositions := terminalVForwardDisplayedPositions pattern
  let positions : Finset (Fin (n + 2)) :=
    rawPositions.map cast.toEmbedding
  have hdisplayedX : (∑ q ∈ positions, eX q) =
      sectionSixTerminalVDisplayedSum pattern
        (fun i => normalizedPrimeLog (10 ^ length) (factors i)) := by
    simpa [positions, rawPositions, eX, transportedFactors] using
      sum_terminalVForwardDisplayedPositions pattern
        (fun i => normalizedPrimeLog (10 ^ length) (factors i))
  have hfixedX :
      (fun i => normalizedPrimeLog (10 ^ length) (factors i)) ∈
        sectionSixTerminalVFixedRegion epsilon delta band pattern
          hinner hresidual := hcoreX.2
  have hdisplayedBounds := terminalVForwardDisplayedSum_bounds band pattern
    hinner hresidual
      (fun i => normalizedPrimeLog (10 ^ length) (factors i)) hfixedX
  have hconvenienceWidth' :
      rho ^ 2 + (((n + 1 : Nat) : Real) * rho) <= epsilon := by
    have hcount :
        ((pattern.1.1 + ell) + pattern.2.1.1) - 1 = n + 1 := by omega
    rw [← hcount]
    exact hconvenienceWidth
  have htransport
      (selected : Finset (Fin (n + 2)))
      (hlast : Fin.last (n + 1) ∉ selected)
      (lower upper : Real)
      (hlower : lower + 2 * epsilon - rho ^ 2 < ∑ q ∈ selected, eX q)
      (hupper : (∑ q ∈ selected, eX q) <= upper - 2 * epsilon) :
      ∃ I : Finset (Fin (n + 1)),
        (∑ i ∈ I, scaledNaturalCubeAnchor rho anchor i) ∈
          Set.Icc (lower + epsilon) (upper - epsilon) := by
    let I := typeIIPrefixIndexSet selected
    have hprefix : (∑ i ∈ I, eX i.castSucc) =
        ∑ q ∈ selected, eX q := by
      simpa only [I] using
        sum_terminalVForwardPrefixIndexSet_eq selected eX hlast
    have hmove := terminalVForwardOneWidthSubsetSum_bounds hrho.le hzCell I
    rw [hprefix] at hmove
    refine ⟨I, ?_, ?_⟩ <;> linarith
  have hconvenient :
      ∃ I : Finset (Fin (n + 1)),
        (∑ i ∈ I, scaledNaturalCubeAnchor rho anchor i) ∈
            Set.Icc (9 / 25 + epsilon) (17 / 40 - epsilon) ∨
          (∑ i ∈ I, scaledNaturalCubeAnchor rho anchor i) ∈
            Set.Icc (23 / 40 + epsilon) (16 / 25 - epsilon) := by
    by_cases hlast : Fin.last (n + 1) ∈ positions
    · let complement : Finset (Fin (n + 2)) := Finset.univ \ positions
      have hlastComplement : Fin.last (n + 1) ∉ complement := by
        simp [complement, hlast]
      have hsumComplement : (∑ q ∈ complement, eX q) =
          normalizedPrimeLog (10 ^ length) candidate.represented -
            sectionSixTerminalVDisplayedSum pattern
              (fun i => normalizedPrimeLog (10 ^ length) (factors i)) := by
        rw [show complement = Finset.univ \ positions by rfl,
          Finset.sum_sdiff_eq_sub (Finset.subset_univ positions)]
        change (∑ q, eX q) - (∑ q ∈ positions, eX q) = _
        rw [hsumX, hdisplayedX]
      cases band with
      | low =>
          obtain ⟨I, hI⟩ := htransport complement hlastComplement
            (23 / 40) (16 / 25)
              (by
                rw [hsumComplement]
                simp only [sectionSixThetaOne, sectionSixThetaTwo] at hdisplayedBounds
                linarith)
              (by
                rw [hsumComplement]
                simp only [sectionSixThetaOne, sectionSixThetaTwo] at hdisplayedBounds
                linarith)
          exact ⟨I, Or.inr hI⟩
      | high =>
          obtain ⟨I, hI⟩ := htransport complement hlastComplement
            (9 / 25) (17 / 40)
              (by
                rw [hsumComplement]
                simp only [sectionSixThetaOne, sectionSixThetaTwo] at hdisplayedBounds
                linarith)
              (by
                rw [hsumComplement]
                simp only [sectionSixThetaOne, sectionSixThetaTwo] at hdisplayedBounds
                linarith)
          exact ⟨I, Or.inl hI⟩
    · cases band with
      | low =>
          obtain ⟨I, hI⟩ := htransport positions hlast
            (9 / 25) (17 / 40)
              (by
                rw [hdisplayedX]
                simp only [sectionSixThetaOne, sectionSixThetaTwo] at hdisplayedBounds
                nlinarith [sq_nonneg rho])
              (by
                rw [hdisplayedX]
                simp only [sectionSixThetaOne, sectionSixThetaTwo] at hdisplayedBounds
                linarith)
          exact ⟨I, Or.inl hI⟩
      | high =>
          obtain ⟨I, hI⟩ := htransport positions hlast
            (23 / 40) (16 / 25)
              (by
                rw [hdisplayedX]
                simp only [sectionSixThetaOne, sectionSixThetaTwo] at hdisplayedBounds
                nlinarith [sq_nonneg rho])
              (by
                rw [hdisplayedX]
                simp only [sectionSixThetaOne, sectionSixThetaTwo] at hdisplayedBounds
                linarith)
          exact ⟨I, Or.inr hI⟩
  have hanchor : anchor ∈ sectionSixTerminalVBaseXCoreLocalWallAnchors
      epsilon delta rho sourcePresentation band pattern hinner hresidual n
        hdimension j := by
    rw [mem_sectionSixTerminalVBaseXCoreLocalWallAnchors]
    exact ⟨hslab, hmargin, hroom, hconvenient⟩
  have hsupport : candidate.represented ∈
      (primeTupleProductSupport
        (majorArcPrimeTuples (10 ^ length)
          (scaledNaturalCubeAnchor rho anchor) rho delta)).filter
            (fun m => m ∈ C) := by
    rw [Finset.mem_filter]
    exact ⟨mem_primeTupleProductSupport.mpr
      ⟨transportedFactors, hcell, hproductTransported⟩, hC⟩
  refine ⟨hinner, hresidual, n, hdimension, ?_⟩
  exact ⟨j, anchor, hanchor, hsupport⟩

end

end PrimesRestrictedDigits
