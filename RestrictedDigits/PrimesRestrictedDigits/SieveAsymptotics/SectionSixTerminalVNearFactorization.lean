import PrimesRestrictedDigits.SieveAsymptotics.SectionSixNearScalarCaps
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixTerminalVIncidence
import PrimesRestrictedDigits.SieveAsymptotics.TypeIINearNormalization
import PrimesRestrictedDigits.SieveAsymptotics.TypeIINearStableFactorization
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIStableFactorPositions
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Near factorization of canonical Section 6 terminal V cofactors

This file retains the inner, source-outer, and residual labels of one canonical terminal `V`
cofactor on the strict near carrier. The source region is recovered only at normalization base
`10^length`; transport to the complete product is left to the affine compiler.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

@[simp] theorem sectionSixTerminalVPredicate_eq_true
    {band : SectionSixStateBand} {ell : Nat}
    (state : SectionSixAnyState band ell) :
    sectionSixTerminalVPredicate state = true <-> state.2.kind = .V := by
  simp [sectionSixTerminalVPredicate]

/-- Every canonical source-band terminal state retains its recurrence cutoff. -/
theorem sectionSixSourceBandTerminalStates_cutoff
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)}
    {hepsilon : 0 < epsilon} {hepsilonSmall : epsilon <= 1 / 64}
    {hlength : 1 <= length}
    {hdeltaGap : delta <= sectionSixThetaGap epsilon}
    {band : SectionSixStateBand} {state : SectionSixAnyState band ell}
    (hstate : state ∈ sectionSixSourceBandTerminalStates region hepsilon
      hepsilonSmall hlength hdeltaGap band) :
    sectionSixStateCutoffPredicate state.2.kind
      (sectionSixStateBandCutoff band ((10 ^ length : Nat) : Real)
        (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon))
      state.1 state.2.inner := by
  unfold sectionSixSourceBandTerminalStates at hstate
  rcases List.mem_flatMap.mp hstate with ⟨source, _hsource, hstate⟩
  unfold sectionSixSourceMemberTerminalStates at hstate
  rcases List.mem_map.mp hstate with ⟨term, _hterm, htermState⟩
  subst state
  exact term.state_cutoff

/-- A canonical terminal state retains the original source tuple's region at
the decimal normalization base. -/
theorem sectionSixSourceBandTerminalStates_outerLog_mem_region
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)}
    {hepsilon : 0 < epsilon} {hepsilonSmall : epsilon <= 1 / 64}
    {hlength : 1 <= length}
    {hdeltaGap : delta <= sectionSixThetaGap epsilon}
    {band : SectionSixStateBand} {state : SectionSixAnyState band ell}
    (hstate : state ∈ sectionSixSourceBandTerminalStates region hepsilon
      hepsilonSmall hlength hdeltaGap band) :
    (fun i => normalizedPrimeLog (10 ^ length) (state.2.outer i)) ∈ region := by
  unfold sectionSixSourceBandTerminalStates at hstate
  rcases List.mem_flatMap.mp hstate with ⟨source, _hsource, hsourceState⟩
  have houter : state.2.outer = source.1 :=
    sectionSixSourceMemberTerminalStates_outer hepsilon hepsilonSmall
      hlength hdeltaGap band source hsourceState
  have hsource := (mem_sectionSixSourceBandPrimeTuples.mp source.property).1
  have hp : IsPropositionSixOnePrimeTuple epsilon length region source.1 :=
    (mem_propositionSixOnePrimeTuples_iff_source hepsilon hlength).mp hsource
  dsimp [IsPropositionSixOnePrimeTuple] at hp
  rw [houter]
  exact hp.2.2.2.2

/-- The displayed terminal `V` factors: all accumulated inner factors first,
then the original source outer tuple. -/
def sectionSixTerminalVExplicitFactors
    {band : SectionSixStateBand} {ell : Nat}
    (state : SectionSixAnyState band ell) :
    Fin (state.2.inner.length + ell) -> Nat :=
  Fin.append (fun j => state.2.inner.get j) state.2.outer

/-- Stable positions occupied by the accumulated inner-factor labels. -/
def sectionSixTerminalVInnerStablePositionEmbedding
    {band : SectionSixStateBand} {ell m : Nat}
    (state : SectionSixAnyState band ell) :
    Fin state.2.inner.length ↪
      Fin ((state.2.inner.length + ell) + m.primeFactorsList.length) :=
  (Fin.castAddEmb ell).trans
    (typeIIStableOuterPositionEmbedding
      (sectionSixTerminalVExplicitFactors state) m)

/-- Stable positions occupied by the original source-outer labels. -/
def sectionSixTerminalVSourceStablePositionEmbedding
    {band : SectionSixStateBand} {ell m : Nat}
    (state : SectionSixAnyState band ell) :
    Fin ell ↪
      Fin ((state.2.inner.length + ell) + m.primeFactorsList.length) :=
  (Fin.natAddEmb state.2.inner.length).trans
    (typeIIStableOuterPositionEmbedding
      (sectionSixTerminalVExplicitFactors state) m)

theorem sectionSixTerminalVStableFactor_at_innerPosition
    {band : SectionSixStateBand} {ell m : Nat}
    (state : SectionSixAnyState band ell) (j : Fin state.2.inner.length) :
    typeIIStableFactorTuple (sectionSixTerminalVExplicitFactors state) m
        (sectionSixTerminalVInnerStablePositionEmbedding (m := m) state j) =
      state.2.inner.get j := by
  change typeIIStableFactorTuple (sectionSixTerminalVExplicitFactors state) m
    (typeIIStableOuterPositionEmbedding
      (sectionSixTerminalVExplicitFactors state) m (Fin.castAdd ell j)) = _
  rw [typeIIStableFactorTuple_at_outerPositionEmbedding]
  simp [sectionSixTerminalVExplicitFactors]

theorem sectionSixTerminalVStableFactor_at_sourcePosition
    {band : SectionSixStateBand} {ell m : Nat}
    (state : SectionSixAnyState band ell) (i : Fin ell) :
    typeIIStableFactorTuple (sectionSixTerminalVExplicitFactors state) m
        (sectionSixTerminalVSourceStablePositionEmbedding (m := m) state i) =
      state.2.outer i := by
  change typeIIStableFactorTuple (sectionSixTerminalVExplicitFactors state) m
    (typeIIStableOuterPositionEmbedding
      (sectionSixTerminalVExplicitFactors state) m
        (Fin.natAdd state.2.inner.length i)) = _
  rw [typeIIStableFactorTuple_at_outerPositionEmbedding]
  simp [sectionSixTerminalVExplicitFactors]

/-- The stable source-labelled coordinates recover the source region at base
`10^length`. -/
theorem sectionSixSourceBandTerminalV_stableSourceLog_mem_region
    {epsilon delta : Real} {ell length m : Nat}
    {region : Set (Fin ell -> Real)}
    {hepsilon : 0 < epsilon} {hepsilonSmall : epsilon <= 1 / 64}
    {hlength : 1 <= length}
    {hdeltaGap : delta <= sectionSixThetaGap epsilon}
    {band : SectionSixStateBand} {state : SectionSixAnyState band ell}
    (hstate : state ∈ sectionSixSourceBandTerminalStates region hepsilon
      hepsilonSmall hlength hdeltaGap band) :
    (fun i => normalizedPrimeLog (10 ^ length)
      (typeIIStableFactorTuple (sectionSixTerminalVExplicitFactors state) m
        (sectionSixTerminalVSourceStablePositionEmbedding (m := m) state i))) ∈
      region := by
  simpa only [sectionSixTerminalVStableFactor_at_sourcePosition] using
    sectionSixSourceBandTerminalStates_outerLog_mem_region hstate

/-- The explicit displayed tuple has exactly the complete state modulus as
its product. -/
theorem primeTupleProduct_sectionSixTerminalVExplicitFactors
    {band : SectionSixStateBand} {ell : Nat}
    (state : SectionSixAnyState band ell) :
    primeTupleProduct (sectionSixTerminalVExplicitFactors state) = state.1 := by
  rw [primeTupleProduct, Fin.prod_univ_add]
  have hinner : (∏ j : Fin state.2.inner.length,
      sectionSixTerminalVExplicitFactors state (Fin.castAdd ell j)) =
      state.2.inner.prod := by
    calc
      (∏ j : Fin state.2.inner.length,
          sectionSixTerminalVExplicitFactors state (Fin.castAdd ell j)) =
          ∏ j : Fin state.2.inner.length, state.2.inner.get j := by
            apply Finset.prod_congr rfl
            intro j hj
            simp [sectionSixTerminalVExplicitFactors]
      _ = (List.ofFn state.2.inner.get).prod :=
        (List.prod_ofFn (f := state.2.inner.get)).symm
      _ = state.2.inner.prod := by rw [List.ofFn_get]
  have houter : (∏ i : Fin ell,
      sectionSixTerminalVExplicitFactors state
        (Fin.natAdd state.2.inner.length i)) =
      primeTupleProduct state.2.outer := by
    rw [primeTupleProduct]
    apply Finset.prod_congr rfl
    intro i hi
    simp [sectionSixTerminalVExplicitFactors]
  rw [hinner, houter]
  simpa [Nat.mul_comm] using state.2.product_eq

theorem sectionSixTerminalVExplicitFactors_prime
    {band : SectionSixStateBand} {ell : Nat}
    (state : SectionSixAnyState band ell) :
    forall i, (sectionSixTerminalVExplicitFactors state i).Prime := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa [sectionSixTerminalVExplicitFactors] using
      state.2.innerPrime _ (List.get_mem state.2.inner j)
  · intro j
    simpa [sectionSixTerminalVExplicitFactors] using state.2.outerPrime j

theorem sectionSixSourceBandTerminalVExplicitFactors_lower
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)}
    {hepsilon : 0 < epsilon} {hepsilonSmall : epsilon <= 1 / 64}
    {hlength : 1 <= length}
    {hdeltaGap : delta <= sectionSixThetaGap epsilon}
    {band : SectionSixStateBand} {state : SectionSixAnyState band ell}
    (hstate : state ∈ sectionSixSourceBandTerminalStates region hepsilon
      hepsilonSmall hlength hdeltaGap band) :
    forall i, ((10 ^ length : Nat) : Real) ^ delta <=
      (sectionSixTerminalVExplicitFactors state i : Real) := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa [sectionSixTerminalVExplicitFactors] using
      (sectionSixSourceBandTerminalStates_innerRange hstate
        (state.2.inner.get j) (List.get_mem state.2.inner j)).1.le
  · intro j
    simpa [sectionSixTerminalVExplicitFactors] using
      sectionSixSourceBandTerminalStates_outerLower hstate j

/-- A canonical terminal `V` state has a genuine first inner prime and the
literal strict/weak cutoff `R < D <= R*q`. -/
theorem sectionSixSourceBandTerminalV_firstInner_data
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)}
    {hepsilon : 0 < epsilon} {hepsilonSmall : epsilon <= 1 / 64}
    {hlength : 1 <= length}
    {hdeltaGap : delta <= sectionSixThetaGap epsilon}
    {band : SectionSixStateBand} {state : SectionSixAnyState band ell}
    (hstate : state ∈ sectionSixSourceBandTerminalStates region hepsilon
      hepsilonSmall hlength hdeltaGap band)
    (hV : state.2.kind = .V) :
    exists q rest,
      state.2.inner = q :: rest ∧
      sectionSixTerminalFirstInnerPrime state = q ∧
      q.Prime ∧
      ((10 ^ length : Nat) : Real) ^ delta < (q : Real) ∧
      (q : Real) <= ((10 ^ length : Nat) : Real) ^
        sectionSixThetaGap epsilon ∧
      q ∣ state.1 ∧
      sectionSixStateBandCutoff band ((10 ^ length : Nat) : Real)
          (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) <
        (state.1 : Real) ∧
      (state.1 : Real) <=
        sectionSixStateBandCutoff band ((10 ^ length : Nat) : Real)
          (sectionSixThetaOne epsilon) (sectionSixThetaTwo epsilon) *
            (q : Real) := by
  have hcutoff := sectionSixSourceBandTerminalStates_cutoff hstate
  rw [hV] at hcutoff
  rcases hcutoff with ⟨q, rest, hinner, hqDvd, hDLower, hDUpper⟩
  have hqMem : q ∈ state.2.inner := by rw [hinner]; simp
  have hqRange := sectionSixSourceBandTerminalStates_innerRange hstate q hqMem
  have hqPrime := state.2.innerPrime q hqMem
  refine ⟨q, rest, hinner, ?_, hqPrime, hqRange.1, hqRange.2,
    hqDvd, hDLower, hDUpper⟩
  simp [sectionSixTerminalFirstInnerPrime, hinner]

/-- The complete terminal `V` modulus followed by its first inner prime is
strictly below the decimal scale. -/
theorem sectionSixSourceBandTerminalV_modulus_mul_firstInner_lt_decimalScale
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)}
    {hepsilon : 0 < epsilon} {hepsilonSmall : epsilon <= 1 / 64}
    {hlength : 1 <= length}
    {hdeltaGap : delta <= sectionSixThetaGap epsilon}
    {band : SectionSixStateBand} {state : SectionSixAnyState band ell}
    (hstate : state ∈ sectionSixSourceBandTerminalStates region hepsilon
      hepsilonSmall hlength hdeltaGap band)
    (hV : state.2.kind = .V) :
    (((state.1 * sectionSixTerminalFirstInnerPrime state : Nat) : Real)) <
      ((10 ^ length : Nat) : Real) := by
  let X : Real := ((10 ^ length : Nat) : Real)
  have hX : 1 < X := by
    dsimp only [X]
    exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < (10 : Nat))
  obtain ⟨q, rest, hinner, hfirst, hqPrime, hqLower, hqUpper,
      hqDvd, hDLower, hDUpper⟩ :=
    sectionSixSourceBandTerminalV_firstInner_data hstate hV
  have hRCap := sectionSixStateBandCutoff_le_sourceCap
    hepsilon hepsilonSmall hX band
  have hRqSq := sectionSix_sourceCap_mul_sq_lt_decimalScale
    hepsilon hepsilonSmall hX hRCap (by simpa only [X] using hqUpper)
  have hqNonneg : 0 <= (q : Real) := by positivity
  have hDqLe : (state.1 : Real) * (q : Real) <=
      (sectionSixStateBandCutoff band X (sectionSixThetaOne epsilon)
        (sectionSixThetaTwo epsilon) * (q : Real)) * (q : Real) := by
    exact mul_le_mul_of_nonneg_right (by simpa only [X] using hDUpper) hqNonneg
  rw [hfirst]
  norm_num only [Nat.cast_mul]
  simpa only [X] using hDqLe.trans_lt hRqSq

/-- Complete cofactor-level factorization data for one canonical terminal `V`
member of the strict near carrier. -/
theorem sectionSixSourceBandTerminalVNearCofactor_mem_data
    {epsilon delta rho : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)}
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdeltaGap : delta < sectionSixThetaGap epsilon)
    {band : SectionSixStateBand} {state : SectionSixAnyState band ell}
    {C : Finset Nat} {m : Nat}
    (hstate : state ∈ sectionSixSourceBandTerminalStates region hepsilon
      hepsilonSmall hlength hdeltaGap.le band)
    (hV : state.2.kind = .V)
    (hrhoDelta : rho ^ 2 < delta)
    (hm : m ∈ sectionSixTerminalCofactorCarrier C
      (((10 ^ length : Nat) : Real) ^ delta) state)
    (hnear : m * state.1 ∈ typeIINearXCarrier (10 ^ length) rho) :
    1 < m ∧
      0 < m.primeFactorsList.length ∧
      m * state.1 ∈ C ∧
      primeTupleProduct (sectionSixTerminalVExplicitFactors state) * m =
        m * state.1 ∧
      (forall i, (sectionSixTerminalVExplicitFactors state i).Prime) ∧
      (forall i, ((10 ^ length : Nat) : Real) ^ delta <=
        (sectionSixTerminalVExplicitFactors state i : Real)) ∧
      strictRoughPredicate (((10 ^ length : Nat) : Real) ^ delta) m ∧
      (fun i => normalizedPrimeLog (m * state.1)
        (typeIIStableFactorTuple
          (sectionSixTerminalVExplicitFactors state) m i)) ∈
        typeIIExponentSimplex delta ∧
      (((state.2.inner.length + ell + m.primeFactorsList.length : Nat) : Real) <=
        2 / delta) ∧
      (fun i => normalizedPrimeLog (10 ^ length) (state.2.outer i)) ∈ region := by
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  have hXNat : 1 < XNat := by
    dsimp only [XNat]
    exact Nat.one_lt_pow (by omega : length ≠ 0) (by norm_num)
  have hdelta : 0 < delta := (sq_nonneg rho).trans_lt hrhoDelta
  have hN : 1 < m * state.1 :=
    one_lt_of_mem_typeIINearXCarrier_of_sq_lt_sectionSixThetaGap
      hepsilon hepsilonSmall hXNat hrhoDelta hdeltaGap (by simpa only [XNat] using hnear)
  have hNX : m * state.1 < XNat :=
    (mem_typeIINearXCarrier.mp (by simpa only [XNat] using hnear)).1
  have hmNeZero : m ≠ 0 := by
    intro hmZero
    subst m
    simp at hN
  obtain ⟨q, rest, hinner, hfirst, hqPrime, hqLower, hqUpper,
      hqDvd, hDLower, hDUpper⟩ :=
    sectionSixSourceBandTerminalV_firstInner_data hstate hV
  have hmStrict : m ∈ strictSiftedCarrier
      (sieveDilation C (sectionSixStateModulusPNat state.2)) (q : Real) := by
    simpa [sectionSixTerminalCofactorCarrier, hV,
      sectionSixTerminalThreshold, sectionSixTerminalFirstInnerPrime,
      hinner] using hm
  have hmStrictData := mem_strictSiftedCarrier.mp hmStrict
  have hmCarrier : m * state.1 ∈ C := by
    simpa using (mem_sieveDilation.mp hmStrictData.1)
  have hmRough :
      strictRoughPredicate (((10 ^ length : Nat) : Real) ^ delta) m := by
    intro p hp hpm
    exact hqLower.trans (hmStrictData.2 p hp hpm)
  have hDq : (((state.1 * q : Nat) : Real)) < (XNat : Real) := by
    have hcap := sectionSixSourceBandTerminalV_modulus_mul_firstInner_lt_decimalScale
      hstate hV
    rw [hfirst] at hcap
    simpa only [XNat] using hcap
  have hDCap : (state.1 : Real) < (XNat : Real) ^ (1 - delta) :=
    typeIIOuterFactor_lt_rpow_one_sub hXNat hDq (by simpa only [XNat] using hqLower)
  have hmNeOne : m ≠ 1 := by
    apply typeIINearResidual_ne_one (X := XNat) (D := state.1)
      (m := m) (N := m * state.1) (eta := delta) (deltaNear := rho)
      hXNat hrhoDelta (mem_typeIINearXCarrier.mp
        (by simpa only [XNat] using hnear)).2
    · simp [Nat.mul_comm]
    · exact hDCap
  have hmOneLt : 1 < m := by omega
  have hmFactors : 0 < m.primeFactorsList.length :=
    List.length_pos_iff.mpr ((Nat.primeFactorsList_ne_nil m).2 hmOneLt)
  have hproduct :
      primeTupleProduct (sectionSixTerminalVExplicitFactors state) * m =
        m * state.1 := by
    rw [primeTupleProduct_sectionSixTerminalVExplicitFactors]
    exact Nat.mul_comm _ _
  have hprime := sectionSixTerminalVExplicitFactors_prime state
  have hlower := sectionSixSourceBandTerminalVExplicitFactors_lower hstate
  have hsimplex :
      (fun i => normalizedPrimeLog (m * state.1)
        (typeIIStableFactorTuple
          (sectionSixTerminalVExplicitFactors state) m i)) ∈
        typeIIExponentSimplex delta := by
    exact normalized_typeIIStableFactorTuple_mem_exponentSimplex
      hdelta hmNeZero hprime hlower hmRough hproduct hN hNX
  have harity :
      (((state.2.inner.length + ell + m.primeFactorsList.length : Nat) : Real) <=
        2 / delta) := by
    apply typeIIStableFactorArity_le_two_div_eta hXNat hdelta hmNeZero
      hprime hlower hmRough
    simpa only [hproduct] using hNX
  exact ⟨hmOneLt, hmFactors, hmCarrier, hproduct, hprime, hlower, hmRough,
    hsimplex, harity, sectionSixSourceBandTerminalStates_outerLog_mem_region hstate⟩

end

end PrimesRestrictedDigits
