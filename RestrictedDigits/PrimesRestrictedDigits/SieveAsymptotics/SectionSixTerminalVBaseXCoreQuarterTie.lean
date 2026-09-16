import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectQuarterTieCardinality
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStableTargetCrossTie
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVBaseXCoreCandidate

/-!
# Charge terminal-V base-X cross ties

A displayed/residual tie in the successful terminal-V decoder is charged to the common
fixed-quarter squareful carrier already used by the direct branch. See Lemma 7.3 of
`MAYNARD-PRD-PUBLISHED`, pp. 150--152.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private theorem sectionSixTerminalV_crossTie_mem_quarterTieCarrier
    {epsilon delta : Real} {ell length M N : Nat}
    {band : SectionSixStateBand} {C : Finset Nat}
    {pattern : SectionSixTerminalVStablePattern ell M}
    (hinner : 0 < pattern.1.1)
    (hresidual : 0 < pattern.2.1.1)
    (factors : Fin ((pattern.1.1 + ell) + pattern.2.1.1) -> Nat)
    (hprime : forall j, (factors j).Prime)
    (hmonotone : Monotone factors)
    (hembedding : StrictMono pattern.2.2)
    (hfixedX :
      (fun j => normalizedPrimeLog (10 ^ length) (factors j)) ∈
        sectionSixTerminalVFixedRegion epsilon delta band pattern
          hinner hresidual)
    (hproduct : primeTupleProduct factors = N)
    (hNX : N < 10 ^ length)
    (hNC : N ∈ C)
    (hfive : 5 <= ((10 ^ length : Nat) : Real) ^ delta)
    {i : Fin (pattern.1.1 + ell)}
    {z : Fin ((pattern.1.1 + ell) + pattern.2.1.1)}
    (hz : z ∉ Set.range pattern.2.2)
    (htie : factors (pattern.2.2 i) = factors z) :
    N ∈ sectionSixDirectQuarterTieCarrier C
      ((10 ^ length : Nat) : Real) delta := by
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let firstInner := pattern.firstInnerPosition hinner
  let firstResidual := pattern.firstResidualPosition hresidual
  let p : Nat := factors (pattern.2.2 i)
  have hNpos : 0 < N := by
    rw [← hproduct]
    exact primeTupleProduct_pos (fun j => (hprime j).ne_zero)
  have hXNat : 1 < XNat := by
    dsimp only [XNat]
    omega
  have hX : (1 : Real) < X := by
    dsimp only [X]
    exact_mod_cast hXNat
  have hfirstLowerLog :
      delta < normalizedPrimeLog XNat (factors firstInner) := by
    cases band with
    | low => exact hfixedX.2.2.2.2.1
    | high => exact hfixedX.2.2.2.2.2.1
  have hfirstLower : X ^ delta < (factors firstInner : Real) := by
    change delta < Real.logb X (factors firstInner : Real) at hfirstLowerLog
    exact (Real.lt_logb_iff_rpow_lt hX (by
      exact_mod_cast (hprime firstInner).pos)).mp hfirstLowerLog
  have hfirstCrossLog :
      normalizedPrimeLog XNat (factors firstInner) <
        normalizedPrimeLog XNat (factors firstResidual) := by
    cases band with
    | low => exact hfixedX.2.2.2.2.2.2
    | high => exact hfixedX.2.2.2.2.2.2.2
  have hfirstCross : factors firstInner < factors firstResidual := by
    change Real.logb X (factors firstInner : Real) <
      Real.logb X (factors firstResidual : Real) at hfirstCrossLog
    exact_mod_cast (Real.logb_lt_logb_iff hX
      (by exact_mod_cast (hprime firstInner).pos)
      (by exact_mod_cast (hprime firstResidual).pos)).mp hfirstCrossLog
  have hfirstLe : forall j, factors firstInner <= factors j := by
    intro j
    by_cases hj : j ∈ Set.range pattern.2.2
    · obtain ⟨a, rfl⟩ := hj
      apply hmonotone
      apply hembedding.monotone
      change (Fin.castAdd ell
        (⟨0, hinner⟩ : Fin pattern.1.1)).val <= a.val
      simp
    · have hjComplement :
          j ∈ Set.range (typeIIComplementPositionEmbedding pattern.2.2) :=
        (mem_range_typeIIComplementPositionEmbedding_iff pattern.2.2 j).2 hj
      obtain ⟨a, rfl⟩ := hjComplement
      apply hfirstCross.le.trans
      apply hmonotone
      apply (typeIIComplementPositionEmbedding pattern.2.2).monotone
      change 0 <= a.val
      omega
  have hfactorFive : forall j, 5 < (factors j : Real) := by
    intro j
    exact hfive.trans_lt (hfirstLower.trans_le (by
      exact_mod_cast hfirstLe j))
  have hfactorTen : forall j, (factors j).Coprime 10 := by
    intro j
    rw [show 10 = 2 * 5 by norm_num, Nat.coprime_mul_iff_right]
    constructor
    · rw [(hprime j).coprime_iff_not_dvd]
      intro hjDvd
      have hjLe : factors j <= 2 := Nat.le_of_dvd (by norm_num) hjDvd
      have hjLeReal : (factors j : Real) <= 2 := by exact_mod_cast hjLe
      linarith [hfactorFive j]
    · rw [(hprime j).coprime_iff_not_dvd]
      intro hjDvd
      have hjLe : factors j <= 5 := Nat.le_of_dvd (by norm_num) hjDvd
      have hjLeReal : (factors j : Real) <= 5 := by exact_mod_cast hjLe
      linarith [hfactorFive j]
  have hNTen : N.Coprime 10 := by
    rw [← hproduct, primeTupleProduct, Nat.coprime_prod_left_iff]
    intro j hj
    exact hfactorTen j
  have hpPrime : p.Prime := hprime _
  have hpSq : p * p ∣ N := by
    have hne : pattern.2.2 i ≠ z := by
      intro h
      exact hz ⟨i, h⟩
    have hsquare := square_dvd_primeTupleProduct_of_distinct_equal
      factors hne htie
    simpa only [p, hproduct] using hsquare
  have hpLower : X ^ delta < (p : Real) := by
    exact hfirstLower.trans_le (by
      exact_mod_cast hfirstLe (pattern.2.2 i))
  have hNUpper : (N : Real) < X := by
    dsimp only [X, XNat]
    exact_mod_cast hNX
  have hpUpper : (p : Real) <= X ^ (1 / 2 : Real) := by
    have hppNat : p * p <= N := Nat.le_of_dvd hNpos hpSq
    have hpp : (p : Real) ^ 2 < X := by
      calc
        (p : Real) ^ 2 = ((p * p : Nat) : Real) := by norm_num [pow_two]
        _ <= (N : Real) := by exact_mod_cast hppNat
        _ < X := hNUpper
    have hpSqrt : (p : Real) < Real.sqrt X := Real.lt_sqrt_of_sq_lt hpp
    rw [Real.sqrt_eq_rpow] at hpSqrt
    exact hpSqrt.le
  rw [mem_sectionSixDirectQuarterTieCarrier]
  rcases le_or_gt (p : Real) (X ^ (1 / 4 : Real)) with hpSmall | hpLarge
  · left
    exact mem_sectionSixRepeatedCoprimeSquarefulCarrier.mpr
      ⟨hNC, hNTen, p,
        mem_sievePrimeInterval.mpr ⟨hpPrime, hpLower, hpSmall⟩, hpSq⟩
  · right
    exact mem_sectionSixRepeatedSquarefulCarrier.mpr
      ⟨hNC, hNpos, p,
        mem_sievePrimeInterval.mpr ⟨hpPrime, hpLarge, hpUpper⟩, hpSq⟩

/-- A successful base-`X` terminal-V core gives its exact candidate or lies in
the common fixed-quarter tie carrier. -/
theorem sectionSixTerminalVBaseXCore_exists_candidate_or_quarterTie
    {epsilon delta rho : Real} {ell length M N : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixStateBand}
    {C : Finset Nat} {pattern : SectionSixTerminalVStablePattern ell M}
    (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdelta : 0 < delta)
    (hdeltaGap : delta <= sectionSixThetaGap epsilon)
    (hinner : 0 < pattern.1.1)
    (hresidual : 0 < pattern.2.1.1)
    (factors : Fin ((pattern.1.1 + ell) + pattern.2.1.1) -> Nat)
    (hprime : forall i, (factors i).Prime)
    (hmonotone : Monotone factors)
    (hembedding : StrictMono pattern.2.2)
    (hcoreX :
      (fun i => normalizedPrimeLog (10 ^ length) (factors i)) ∈
        typeIIAffineEmbeddingPreimageRegion
            pattern.sourcePositionEmbedding region ∩
          sectionSixTerminalVFixedRegion epsilon delta band pattern
            hinner hresidual)
    (hproduct : primeTupleProduct factors = N)
    (hNC : N ∈ C)
    (hnear : N ∈ typeIINearXCarrier (10 ^ length) rho)
    (hfive : 5 <= ((10 ^ length : Nat) : Real) ^ delta) :
    (∃ candidate : SectionSixTerminalVCandidate band ell,
      candidate ∈ sectionSixSourceBandTerminalVNearCandidatesOfStablePattern
        region hepsilon hepsilonSmall hlength hdeltaGap band C
          (((10 ^ length : Nat) : Real) ^ delta)
          (typeIINearXCarrier (10 ^ length) rho) M pattern ∧
      candidate.represented = N) ∨
    N ∈ sectionSixDirectQuarterTieCarrier C
      ((10 ^ length : Nat) : Real) delta := by
  rcases sectionSixTerminalVBaseXCore_exists_candidate_or_crossTie
      hepsilon hepsilonSmall hlength hdelta hdeltaGap hinner hresidual
        factors hprime hmonotone hembedding hcoreX hproduct hNC hnear with
    hcandidate | ⟨i, z, hz, htie⟩
  · exact Or.inl hcandidate
  · right
    apply sectionSixTerminalV_crossTie_mem_quarterTieCarrier
      hinner hresidual factors hprime hmonotone hembedding hcoreX.2
        hproduct (mem_typeIINearXCarrier.mp hnear).1 hNC hfive hz htie

end

end PrimesRestrictedDigits
