import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectStrictCarrier
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixNearScalarCaps
import PrimesRestrictedDigits.SieveAsymptotics.TypeIINearNormalization
import PrimesRestrictedDigits.SieveAsymptotics.TypeIINearStableFactorization
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIStableFactorPositions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Stable near factorizations for direct strict Section 6 terms

An accepted direct index `(p,q)` displays the factors `q :: p`. This file retains their labels
through the stable complete factorization and adapts one strictly sifted cofactor on the near
carrier to the generic Type II simplex and arity statements.
-/

namespace PrimesRestrictedDigits

noncomputable section

open scoped BigOperators

/-- The displayed direct factors, with the continuation prime before the
original source tuple. -/
def sectionSixDirectExplicitFactors {ell : Nat}
    (index : SectionSixDirectStrictIndex ell) : Fin (ell + 1) -> Nat :=
  Matrix.vecCons index.2 index.1

/-- The stable position occupied by the continuation-prime label. -/
def sectionSixDirectStableThresholdPosition {ell : Nat}
    (index : SectionSixDirectStrictIndex ell) (m : Nat) :
    Fin ((ell + 1) + m.primeFactorsList.length) :=
  typeIIStableOuterPositionEmbedding
    (sectionSixDirectExplicitFactors index) m 0

/-- The stable positions occupied by the original source-coordinate labels. -/
def sectionSixDirectStableSourcePositionEmbedding {ell : Nat}
    (index : SectionSixDirectStrictIndex ell) (m : Nat) :
    Fin ell ↪ Fin ((ell + 1) + m.primeFactorsList.length) :=
  ({ toFun := Fin.succ
     inj' := Fin.succ_injective ell } : Fin ell ↪ Fin (ell + 1)).trans
    (typeIIStableOuterPositionEmbedding
      (sectionSixDirectExplicitFactors index) m)

/-- Recovery of the continuation prime at its stable labelled position. -/
@[simp] theorem sectionSixDirectStableFactor_at_threshold {ell : Nat}
    (index : SectionSixDirectStrictIndex ell) (m : Nat) :
    typeIIStableFactorTuple (sectionSixDirectExplicitFactors index) m
      (sectionSixDirectStableThresholdPosition index m) = index.2 := by
  rw [sectionSixDirectStableThresholdPosition,
    typeIIStableFactorTuple_at_outerPositionEmbedding]
  rfl

/-- Recovery of a source prime at its stable labelled position. -/
@[simp] theorem sectionSixDirectStableFactor_at_source {ell : Nat}
    (index : SectionSixDirectStrictIndex ell) (m : Nat) (i : Fin ell) :
    typeIIStableFactorTuple (sectionSixDirectExplicitFactors index) m
      (sectionSixDirectStableSourcePositionEmbedding index m i) = index.1 i := by
  rw [sectionSixDirectStableSourcePositionEmbedding,
    Function.Embedding.trans_apply,
    typeIIStableFactorTuple_at_outerPositionEmbedding]
  rfl

/-- The displayed tuple has the literal direct product `d*q`. -/
@[simp] theorem primeTupleProduct_sectionSixDirectExplicitFactors
    {ell : Nat} (index : SectionSixDirectStrictIndex ell) :
    primeTupleProduct (sectionSixDirectExplicitFactors index) =
      primeTupleProduct index.1 * index.2 := by
  simp [sectionSixDirectExplicitFactors, primeTupleProduct,
    Fin.prod_univ_succ, Nat.mul_comm]

/-- On an accepted index, the displayed-factor product is the strict key. -/
theorem primeTupleProduct_sectionSixDirectExplicitFactors_eq_key
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {index : SectionSixDirectStrictIndex ell}
    (hindex : index ∈ sectionSixDirectRepeatedIndices
      epsilon delta ell region length band) :
    primeTupleProduct (sectionSixDirectExplicitFactors index) =
      sectionSixDirectStrictKey index := by
  rw [primeTupleProduct_sectionSixDirectExplicitFactors,
    sectionSixDirectStrictKey_eq hindex]

/-- Accepted direct source coordinates retain their original `log X` region
membership.  The continuation and residual coordinates are intentionally not
inserted into this source region. -/
theorem sectionSixDirectSource_mem_region
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {index : SectionSixDirectStrictIndex ell}
    (hindex : index ∈ sectionSixDirectRepeatedIndices
      epsilon delta ell region length band) :
    (fun i => normalizedPrimeLog (10 ^ length) (index.1 i)) ∈ region := by
  have hindexData := mem_sectionSixDirectRepeatedIndices.mp hindex
  have htuple := (mem_sectionSixDirectRangePrimeTuples.mp hindexData.1).1
  exact (mem_propositionSixOnePrimeTuples.mp htuple).2.2.2.2.2

/-- The same source-region witness after lifting source labels into the stable
complete tuple. -/
theorem sectionSixDirectStableSourceLog_mem_region
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {index : SectionSixDirectStrictIndex ell} (m : Nat)
    (hindex : index ∈ sectionSixDirectRepeatedIndices
      epsilon delta ell region length band) :
    (fun i => normalizedPrimeLog (10 ^ length)
      (typeIIStableFactorTuple (sectionSixDirectExplicitFactors index) m
        (sectionSixDirectStableSourcePositionEmbedding index m i))) ∈ region := by
  simpa only [sectionSixDirectStableFactor_at_source] using
    (sectionSixDirectSource_mem_region hindex)

/-- The source product and two copies of the accepted continuation prime stay
strictly below the decimal scale. -/
theorem sectionSixDirectSourceProduct_mul_sq_lt_decimalScale
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {index : SectionSixDirectStrictIndex ell}
    (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hindex : index ∈ sectionSixDirectRepeatedIndices
      epsilon delta ell region length band) :
    (((primeTupleProduct index.1 * index.2) * index.2 : Nat) : Real) <
      ((10 ^ length : Nat) : Real) := by
  let X : Real := ((10 ^ length : Nat) : Real)
  have hX : 1 < X := by
    dsimp [X]
    exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < (10 : Nat))
  have hindexData := mem_sectionSixDirectRepeatedIndices.mp hindex
  have htuple := (mem_sectionSixDirectRangePrimeTuples.mp hindexData.1).1
  have hsource := (mem_propositionSixOnePrimeTuples.mp htuple).2
  have hD : (primeTupleProduct index.1 : Real) <=
      X ^ (1 - sectionSixThetaOne epsilon) := by
    simpa only [X] using hsource.2.2.2.1
  have hq : (index.2 : Real) <= X ^ sectionSixThetaGap epsilon := by
    simpa only [X] using
      (mem_sievePrimeInterval.mp hindexData.2).2.2
  have hcap := sectionSix_sourceCap_mul_sq_lt_decimalScale
    hepsilon hepsilonSmall hX hD hq
  simpa only [X, Nat.cast_mul] using hcap

/-- The same squared cap with the displayed tuple product exposed. -/
theorem sectionSixDirectExplicitProduct_mul_continuation_lt_decimalScale
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {index : SectionSixDirectStrictIndex ell}
    (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hindex : index ∈ sectionSixDirectRepeatedIndices
      epsilon delta ell region length band) :
    ((primeTupleProduct (sectionSixDirectExplicitFactors index) * index.2 : Nat) :
        Real) < ((10 ^ length : Nat) : Real) := by
  rw [primeTupleProduct_sectionSixDirectExplicitFactors]
  exact sectionSixDirectSourceProduct_mul_sq_lt_decimalScale
    hepsilon hepsilonSmall hlength hindex

/-- Accepted displayed direct factors are prime. -/
theorem prime_sectionSixDirectExplicitFactors
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {index : SectionSixDirectStrictIndex ell}
    (hindex : index ∈ sectionSixDirectRepeatedIndices
      epsilon delta ell region length band) :
    forall i, (sectionSixDirectExplicitFactors index i).Prime := by
  have hindexData := mem_sectionSixDirectRepeatedIndices.mp hindex
  have htuple := (mem_sectionSixDirectRangePrimeTuples.mp hindexData.1).1
  have hsource := (mem_propositionSixOnePrimeTuples.mp htuple).2
  have hqPrime := (mem_sievePrimeInterval.mp hindexData.2).1
  intro i
  refine Fin.cases hqPrime ?_ i
  intro j
  exact hsource.1 j

/-- Every displayed direct factor is at least the fixed Section 6 scale. -/
theorem sectionSixDirectExplicitFactors_rpow_lower
    {epsilon delta : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {index : SectionSixDirectStrictIndex ell}
    (hlength : 1 <= length)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (hindex : index ∈ sectionSixDirectRepeatedIndices
      epsilon delta ell region length band) :
    forall i, (((10 ^ length : Nat) : Real) ^ delta) <=
      ((sectionSixDirectExplicitFactors index i : Nat) : Real) := by
  let X : Real := ((10 ^ length : Nat) : Real)
  have hX : 1 < X := by
    dsimp [X]
    exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < (10 : Nat))
  have hindexData := mem_sectionSixDirectRepeatedIndices.mp hindex
  have htuple := (mem_sectionSixDirectRangePrimeTuples.mp hindexData.1).1
  have hsource := (mem_propositionSixOnePrimeTuples.mp htuple).2
  have hqLower := (mem_sievePrimeInterval.mp hindexData.2).2.1
  intro i
  refine Fin.cases hqLower.le ?_ i
  intro j
  exact (Real.rpow_lt_rpow_of_exponent_lt hX hdeltaGapStrict).le.trans
    (by simpa only [X, sectionSixDirectExplicitFactors,
      Matrix.cons_val_succ] using hsource.2.2.1 j)

/-- Complete factorization data for one strict direct cofactor on the near
carrier.  The near width `rho` has no sign restriction. -/
theorem sectionSixDirectNearCofactor_mem_data
    {epsilon delta rho : Real} {ell length : Nat}
    {region : Set (Fin ell -> Real)} {band : SectionSixDirectBand}
    {index : SectionSixDirectStrictIndex ell} {C : Finset Nat} {m : Nat}
    (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length)
    (hdelta : 0 < delta)
    (hdeltaGapStrict : delta < sectionSixThetaGap epsilon)
    (hrhoSq : rho ^ 2 < delta)
    (hindex : index ∈ sectionSixDirectRepeatedIndices
      epsilon delta ell region length band)
    (hm : m ∈ sectionSixDirectStrictCofactorCarrier C index)
    (hnear : m * sectionSixDirectStrictKey index ∈
      typeIINearXCarrier (10 ^ length) rho) :
    1 < m ∧
      0 < m.primeFactorsList.length ∧
      m * sectionSixDirectStrictKey index ∈ C ∧
      primeTupleProduct (sectionSixDirectExplicitFactors index) * m =
        m * sectionSixDirectStrictKey index ∧
      (forall i, (sectionSixDirectExplicitFactors index i).Prime) ∧
      (forall i, (((10 ^ length : Nat) : Real) ^ delta) <=
        ((sectionSixDirectExplicitFactors index i : Nat) : Real)) ∧
      strictRoughPredicate (((10 ^ length : Nat) : Real) ^ delta) m ∧
      (fun i => normalizedPrimeLog
        (m * sectionSixDirectStrictKey index)
        (typeIIStableFactorTuple
          (sectionSixDirectExplicitFactors index) m i)) ∈
        typeIIExponentSimplex delta ∧
      ((((ell + 1) + m.primeFactorsList.length : Nat) : Real) <=
        2 / delta) ∧
      (fun i => normalizedPrimeLog (10 ^ length) (index.1 i)) ∈ region := by
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let N : Nat := m * sectionSixDirectStrictKey index
  have hXNat : 1 < XNat := by
    dsimp [XNat]
    exact Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < (10 : Nat))
  have hnearData : N < XNat ∧ X ^ (1 - rho ^ 2) < (N : Real) := by
    simpa only [N, XNat, X] using (mem_typeIINearXCarrier.mp hnear)
  have hN : 1 < N := by
    exact one_lt_of_mem_typeIINearXCarrier_of_sq_lt_sectionSixThetaGap
      hepsilon hepsilonSmall hXNat hrhoSq hdeltaGapStrict
      (by simpa only [XNat] using hnear)
  have hmZero : m ≠ 0 := by
    intro hm0
    subst m
    simp [N] at hN
  have hindexData := mem_sectionSixDirectRepeatedIndices.mp hindex
  have hqData := mem_sievePrimeInterval.mp hindexData.2
  have hmData : m ∈ sieveDilation C (sectionSixDirectStrictModulus index) ∧
      strictRoughPredicate (index.2 : Real) m := by
    simpa [sectionSixDirectStrictCofactorCarrier] using
      (mem_strictSiftedCarrier.mp hm)
  have hrepresented : N ∈ C := by
    simpa only [N, sectionSixDirectStrictKey] using
      (mem_sieveDilation.mp hmData.1)
  have hproduct :
      primeTupleProduct (sectionSixDirectExplicitFactors index) * m = N := by
    rw [primeTupleProduct_sectionSixDirectExplicitFactors_eq_key hindex]
    simp only [N, Nat.mul_comm]
  have houterPrime : forall i,
      (sectionSixDirectExplicitFactors index i).Prime :=
    prime_sectionSixDirectExplicitFactors hindex
  have houterLower : forall i, X ^ delta <=
      ((sectionSixDirectExplicitFactors index i : Nat) : Real) := by
    simpa only [X, XNat] using
      sectionSixDirectExplicitFactors_rpow_lower
        hlength hdeltaGapStrict hindex
  have hrough : strictRoughPredicate (X ^ delta) m := by
    intro r hr hrm
    exact hqData.2.1.trans (hmData.2 r hr hrm)
  have houterCap :
      (primeTupleProduct (sectionSixDirectExplicitFactors index) : Real) <
        X ^ (1 - delta) := by
    apply typeIIOuterFactor_lt_rpow_one_sub hXNat
      (q := index.2)
    · simpa only [X, XNat] using
        sectionSixDirectExplicitProduct_mul_continuation_lt_decimalScale
          hepsilon hepsilonSmall hlength hindex
    · simpa only [X, XNat] using hqData.2.1
  have hmOne : m ≠ 1 := by
    apply typeIINearResidual_ne_one hXNat hrhoSq hnearData.2 hproduct
    simpa only [X, XNat] using houterCap
  have hmGt : 1 < m := by omega
  have hresidualLength : 0 < m.primeFactorsList.length := by
    rw [List.length_pos_iff, Nat.primeFactorsList_ne_nil]
    exact hmGt
  have hsimplex :
      (fun i => normalizedPrimeLog N
        (typeIIStableFactorTuple
          (sectionSixDirectExplicitFactors index) m i)) ∈
        typeIIExponentSimplex delta :=
    normalized_typeIIStableFactorTuple_mem_exponentSimplex
      hdelta hmZero houterPrime houterLower hrough hproduct hN hnearData.1
  have harity :
      ((((ell + 1) + m.primeFactorsList.length : Nat) : Real) <=
        2 / delta) := by
    apply typeIIStableFactorArity_le_two_div_eta hXNat hdelta hmZero
      houterPrime houterLower hrough
    rw [hproduct]
    exact hnearData.1
  have hsource := sectionSixDirectSource_mem_region hindex
  refine ⟨hmGt, hresidualLength, ?_, ?_, houterPrime, ?_, ?_, ?_, harity, hsource⟩
  · simpa only [N] using hrepresented
  · simpa only [N] using hproduct
  · simpa only [X, XNat] using houterLower
  · simpa only [X, XNat] using hrough
  · simpa only [N] using hsimplex

end

end PrimesRestrictedDigits
