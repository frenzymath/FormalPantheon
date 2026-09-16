import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstRepeatedCarriers
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDirectQuarterTieCardinality
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixDivisorIncidence
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixIncidenceAggregation
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIRegionSupport
import Mathlib.Data.Fin.VecNotation
import Mathlib.Order.Fin.Tuple
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# First-ledger repeated-prime incidence

The outer and nested repeated-prime families retain their complete keys while their
represented values are charged to the common quarter-tie carrier.

Source: MAYNARD-PRD-PUBLISHED, Section 6, pp. 139--140, Eq. (6.5).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- Membership in a repeated represented carrier retains its complete key,
square divisor, positivity, and inherited roughness. -/
theorem sectionSixFirstRepeatedRepresentedCarrier_mem_data
    {X gap : Real} {C : Finset Nat} {d : PNat} {q n : Nat}
    (hy : 5 < X ^ gap)
    (hq : q.Prime)
    (hqLower : X ^ gap < (q : Real))
    (hdRough : weakRoughPredicate (X ^ gap) (d : Nat))
    (hn : n ∈ sectionSixFirstRepeatedRepresentedCarrier C d q) :
    n ∈ C ∧ 0 < n ∧ sectionSixFirstRepeatedKey d q ∣ n ∧
      q * q ∣ n ∧ weakRoughPredicate (X ^ gap) n := by
  rcases mem_sectionSixFirstRepeatedRepresentedCarrier.mp hn with
    ⟨m, hm, hmn⟩
  have hmData : m ∈ sieveDilation C
        (sectionSixFirstRepeatedModulus d q) ∧
      weakRoughPredicate (q : Real) m :=
    mem_weakSiftedCarrier.mp hm
  have hmCarrier : m * sectionSixFirstRepeatedKey d q ∈ C := by
    simpa [sectionSixFirstRepeatedKey] using
      (mem_sieveDilation.mp hmData.1)
  have hmPos : 0 < m := by
    apply Nat.pos_of_ne_zero
    intro hmZero
    subst m
    have hzero := weakRoughPredicate_zero.mp hmData.2
    linarith
  have hkeyPos : 0 < sectionSixFirstRepeatedKey d q :=
    (sectionSixFirstRepeatedModulus d q).pos
  have hkeyDvd : sectionSixFirstRepeatedKey d q ∣ n := by
    refine ⟨m, ?_⟩
    simpa [Nat.mul_comm] using hmn.symm
  have hqSqKey : q * q ∣ sectionSixFirstRepeatedKey d q := by
    refine ⟨(d : Nat), ?_⟩
    rw [sectionSixFirstRepeatedKey_eq d hq]
    ring
  have hmRough : weakRoughPredicate (X ^ gap) m := by
    intro r hr hrm
    exact hqLower.le.trans (hmData.2 r hr hrm)
  have hkeyRough : weakRoughPredicate (X ^ gap)
      (sectionSixFirstRepeatedKey d q) := by
    intro r hr hrKey
    rw [sectionSixFirstRepeatedKey_eq d hq] at hrKey
    rcases hr.dvd_mul.mp hrKey with hrDq | hrQ
    · rcases hr.dvd_mul.mp hrDq with hrD | hrQ
      · exact hdRough r hr hrD
      · have hrEq : r = q :=
          (Nat.prime_dvd_prime_iff_eq hr hq).mp hrQ
        simpa only [hrEq] using hqLower.le
    · have hrEq : r = q :=
        (Nat.prime_dvd_prime_iff_eq hr hq).mp hrQ
      simpa only [hrEq] using hqLower.le
  have hnRough : weakRoughPredicate (X ^ gap) n := by
    intro r hr hrn
    rw [← hmn] at hrn
    rcases hr.dvd_mul.mp hrn with hrm | hrKey
    · exact hmRough r hr hrm
    · exact hkeyRough r hr hrKey
  refine ⟨?_, ?_, hkeyDvd, hqSqKey.trans hkeyDvd, hnRough⟩
  · simpa only [hmn] using hmCarrier
  · rw [← hmn]
    exact Nat.mul_pos hmPos hkeyPos

/-- A repeated represented carrier with its repeated prime below `X^(1/2)`
is contained in the common quarter-tie carrier. -/
theorem sectionSixFirstRepeatedRepresentedCarrier_subset_quarterTie
    {X gap : Real} {C : Finset Nat} {d : PNat} {q : Nat}
    (hy : 5 < X ^ gap)
    (hq : q.Prime)
    (hqLower : X ^ gap < (q : Real))
    (hqUpper : (q : Real) <= X ^ (1 / 2 : Real))
    (hdRough : weakRoughPredicate (X ^ gap) (d : Nat)) :
    sectionSixFirstRepeatedRepresentedCarrier C d q ⊆
      sectionSixDirectQuarterTieCarrier C X gap := by
  intro n hn
  have hnData := sectionSixFirstRepeatedRepresentedCarrier_mem_data
    hy hq hqLower hdRough hn
  have hnTen := weakRoughPredicate_coprime_ten_of_five_lt
    hy hnData.2.2.2.2
  rw [mem_sectionSixDirectQuarterTieCarrier]
  by_cases hqQuarter : (q : Real) <= X ^ (1 / 4 : Real)
  · left
    exact mem_sectionSixRepeatedCoprimeSquarefulCarrier.mpr
      ⟨hnData.1, hnTen, q,
        mem_sievePrimeInterval.mpr ⟨hq, hqLower, hqQuarter⟩,
        hnData.2.2.2.1⟩
  · right
    exact mem_sectionSixRepeatedSquarefulCarrier.mpr
      ⟨hnData.1, hnData.2.1, q,
        mem_sievePrimeInterval.mpr
          ⟨hq, lt_of_not_ge hqQuarter, hqUpper⟩,
        hnData.2.2.2.1⟩

/-- An injective complete-key family has at most one divisor-candidate factor
of incidence at each represented integer. -/
theorem sectionSixFirstRepeatedCarrierFiber_le
    {alpha : Type*} [DecidableEq alpha]
    (states : Finset alpha) (key : alpha -> Nat)
    (carrier : alpha -> Finset Nat)
    {X delta : Real} (hX : 1 < X) (hdelta : 0 < delta)
    (C : Finset Nat) (hC : C ⊆ maynardAmbientCarrier X)
    (hdata : ∀ index ∈ states, ∀ {n}, n ∈ carrier index ->
      n ∈ C ∧ 0 < n ∧ key index ∣ n ∧
        weakRoughPredicate (X ^ delta) n)
    (hinj : Set.InjOn key (states : Set alpha))
    (n : Nat) :
    (states.filter fun index => n ∈ carrier index).card <=
      2 ^ Nat.ceil (1 / delta) := by
  classical
  let selected := states.filter fun index => n ∈ carrier index
  change selected.card <= _
  by_cases hselected : selected = ∅
  · simp [hselected]
  · obtain ⟨witness, hwitness⟩ :=
      Finset.nonempty_iff_ne_empty.mpr hselected
    have hwitnessData := Finset.mem_filter.mp hwitness
    have hnData := hdata witness hwitnessData.1 hwitnessData.2
    have hnX : (n : Real) <= X :=
      (mem_maynardAmbientCarrier.mp (hC hnData.1)).le
    have hcandidates :=
      card_sectionSixDivisorCandidates_le_two_pow_ceil_inv_delta
        hX hdelta (Nat.ne_of_gt hnData.2.1) hnX hnData.2.2.2
    have hmaps : Set.MapsTo key (selected : Set alpha)
        (sectionSixDivisorCandidates n : Set Nat) := by
      intro index hindex
      have hindexData := Finset.mem_filter.mp hindex
      have hrepresented := hdata index hindexData.1 hindexData.2
      exact mem_sectionSixDivisorCandidates_of_dvd
        (Nat.ne_of_gt hnData.2.1) hrepresented.2.2.1
    have hinjSelected : Set.InjOn key (selected : Set alpha) := by
      apply hinj.mono
      intro index hindex
      exact (Finset.mem_filter.mp hindex).1
    exact (Finset.card_le_card_of_injOn key hmaps hinjSelected).trans
      hcandidates

private theorem sectionSixFirstOuterRepeatedKey_injOn
    (a b : Real) :
    Set.InjOn (sectionSixFirstRepeatedKey 1)
      (sievePrimeInterval a b : Set Nat) := by
  intro p hp q hq hkey
  have hpPrime := (mem_sievePrimeInterval.mp hp).1
  have hqPrime := (mem_sievePrimeInterval.mp hq).1
  rw [sectionSixFirstRepeatedKey_eq 1 hpPrime,
    sectionSixFirstRepeatedKey_eq 1 hqPrime] at hkey
  have hkeySq : p * p = q * q := by
    simpa only [PNat.one_coe, one_mul] using hkey
  exact Nat.mul_self_inj.mp hkeySq

/-- The complete-key incidence aggregate for the outer repeated-prime family
is bounded by one divisor-candidate factor times the quarter-tie carrier. -/
theorem sum_card_sectionSixFirstOuterRepeatedRepresentedCarrier_le_quarterTie
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (C : Finset Nat) {length : Nat} (hlength : 1 <= length)
    (hC : C ⊆ maynardAmbientCarrier ((10 ^ length : Nat) : Real))
    (hfive :
      5 < ((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon) :
    let X : Real := ((10 ^ length : Nat) : Real)
    let gap : Real := sectionSixThetaGap epsilon
    let z1 : Real := sectionSixZOne epsilon X
    let z4 : Real := sectionSixZFour X
    let K : Nat := 2 ^ Nat.ceil (1 / gap)
    (∑ p ∈ sievePrimeInterval z1 z4,
      ((sectionSixFirstRepeatedRepresentedCarrier C 1 p).card : Real)) <=
      (K : Real) * ((sectionSixDirectQuarterTieCarrier C X gap).card : Real) := by
  dsimp only
  let X : Real := ((10 ^ length : Nat) : Real)
  let gap : Real := sectionSixThetaGap epsilon
  let states := sievePrimeInterval (sectionSixZOne epsilon X)
    (sectionSixZFour X)
  let carrier : Nat -> Finset Nat := fun p =>
    sectionSixFirstRepeatedRepresentedCarrier C 1 p
  have hX : 1 < X := by
    dsimp only [X]
    exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < (10 : Nat))
  have hgap : 0 < gap :=
    (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
  have hsub : ∀ p ∈ states, carrier p ⊆
      sectionSixDirectQuarterTieCarrier C X gap := by
    intro p hp
    have hpData := mem_sievePrimeInterval.mp hp
    apply sectionSixFirstRepeatedRepresentedCarrier_subset_quarterTie
      (by simpa only [X, gap] using hfive) hpData.1
    · simpa only [states, sectionSixZOne] using hpData.2.1
    · simpa only [states, sectionSixZFour_eq_rpow] using hpData.2.2
    · simp
  have hfiber : ∀ n, n ∈ sectionSixDirectQuarterTieCarrier C X gap ->
      (states.filter fun p => n ∈ carrier p).card <=
        2 ^ Nat.ceil (1 / gap) := by
    intro n _hn
    apply sectionSixFirstRepeatedCarrierFiber_le states
      (sectionSixFirstRepeatedKey 1) carrier hX hgap C hC
    · intro p hp n hn
      have hpData := mem_sievePrimeInterval.mp hp
      have hnData := sectionSixFirstRepeatedRepresentedCarrier_mem_data
        (by simpa only [X, gap] using hfive) hpData.1
        (by simpa only [states, sectionSixZOne] using hpData.2.1)
        (by simp) hn
      exact ⟨hnData.1, hnData.2.1, hnData.2.2.1,
        hnData.2.2.2.2⟩
    · exact sectionSixFirstOuterRepeatedKey_injOn _ _
  simpa only [states, carrier, X, gap] using
    (sum_card_le_of_element_fiber_card_real states
      (sectionSixDirectQuarterTieCarrier C X gap) carrier
      (2 ^ Nat.ceil (1 / gap)) hsub hfiber)

private def sectionSixFirstSecondRepeatedKey
    (index : SectionSixFirstSecondRepeatedIndex) : Nat :=
  sectionSixFirstRepeatedKey (Nat.toPNat' index.1) index.2

private def sectionSixFirstSecondRepeatedPrimeTuple
    (index : SectionSixFirstSecondRepeatedIndex) : Fin 3 -> Nat :=
  Matrix.vecCons index.2
    (Matrix.vecCons index.2 (fun _ : Fin 1 => index.1))

private theorem sectionSixFirstSecondRepeatedKey_eq
    {index : SectionSixFirstSecondRepeatedIndex}
    (hp : index.1.Prime) (hq : index.2.Prime) :
    sectionSixFirstSecondRepeatedKey index =
      index.1 * index.2 * index.2 := by
  unfold sectionSixFirstSecondRepeatedKey
  rw [sectionSixFirstRepeatedKey_eq (Nat.toPNat' index.1) hq,
    Nat.toPNat'_coe, if_pos hp.pos]

private theorem sectionSixFirstSecondRepeatedPrimeTuple_prime
    {length : Nat} {z a b : Real}
    {index : SectionSixFirstSecondRepeatedIndex}
    (hindex : index ∈
      sectionSixFirstSecondRepeatedIndices length z a b) :
    ∀ i, (sectionSixFirstSecondRepeatedPrimeTuple index i).Prime := by
  have hindexData := mem_sectionSixFirstSecondRepeatedIndices.mp hindex
  have hp := (mem_sievePrimeInterval.mp hindexData.1).1
  have hq := (mem_sievePrimeInterval.mp hindexData.2).1
  unfold sectionSixFirstSecondRepeatedPrimeTuple
  intro i
  refine Fin.cases hq ?_ i
  intro j
  refine Fin.cases hq ?_ j
  intro k
  exact hp

private theorem sectionSixFirstSecondRepeatedPrimeTuple_monotone
    {length : Nat} {z a b : Real}
    {index : SectionSixFirstSecondRepeatedIndex}
    (hindex : index ∈
      sectionSixFirstSecondRepeatedIndices length z a b) :
    Monotone (sectionSixFirstSecondRepeatedPrimeTuple index) := by
  have hindexData := mem_sectionSixFirstSecondRepeatedIndices.mp hindex
  have hqUpper := (mem_sievePrimeInterval.mp hindexData.2).2.2
  have hthreshold :
      sectionSixFirstFactorThreshold length index.1 <=
        (index.1 : Real) := by
    simp [sectionSixFirstFactorThreshold]
  have hqLe : index.2 <= index.1 := by
    exact_mod_cast hqUpper.trans hthreshold
  have htail : Monotone (fun _ : Fin 1 => index.1) := by
    intro i j hij
    exact le_rfl
  unfold sectionSixFirstSecondRepeatedPrimeTuple
  exact (htail.vecCons hqLe).vecCons le_rfl

private theorem sectionSixFirstSecondRepeatedKey_injOn
    (length : Nat) (z a b : Real) :
    Set.InjOn sectionSixFirstSecondRepeatedKey
      (sectionSixFirstSecondRepeatedIndices length z a b :
        Set SectionSixFirstSecondRepeatedIndex) := by
  intro i hi j hj hkey
  have hiData := mem_sectionSixFirstSecondRepeatedIndices.mp hi
  have hjData := mem_sectionSixFirstSecondRepeatedIndices.mp hj
  have hip := (mem_sievePrimeInterval.mp hiData.1).1
  have hiq := (mem_sievePrimeInterval.mp hiData.2).1
  have hjp := (mem_sievePrimeInterval.mp hjData.1).1
  have hjq := (mem_sievePrimeInterval.mp hjData.2).1
  rw [sectionSixFirstSecondRepeatedKey_eq hip hiq,
    sectionSixFirstSecondRepeatedKey_eq hjp hjq] at hkey
  have hproduct :
      primeTupleProduct (sectionSixFirstSecondRepeatedPrimeTuple i) =
        primeTupleProduct (sectionSixFirstSecondRepeatedPrimeTuple j) := by
    simpa [sectionSixFirstSecondRepeatedPrimeTuple, primeTupleProduct,
      Fin.prod_univ_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      using hkey
  have htuple := eq_of_monotone_primeTupleProduct_eq
    (sectionSixFirstSecondRepeatedPrimeTuple_prime hi)
    (sectionSixFirstSecondRepeatedPrimeTuple_prime hj)
    (sectionSixFirstSecondRepeatedPrimeTuple_monotone hi)
    (sectionSixFirstSecondRepeatedPrimeTuple_monotone hj)
    hproduct
  have hq : i.2 = j.2 := by
    have h := congrFun htuple (0 : Fin 3)
    simpa [sectionSixFirstSecondRepeatedPrimeTuple] using h
  have hp : i.1 = j.1 := by
    have h := congrFun htuple (Fin.succ (Fin.succ (0 : Fin 1)))
    simpa [sectionSixFirstSecondRepeatedPrimeTuple] using h
  cases i with
  | mk ip iq =>
      cases j with
      | mk jp jq =>
          simp only at hp hq
          subst jp
          subst jq
          rfl

/-- The nested complete-key aggregate over any outer subinterval of
(z1,z4] has the same one-factor quarter-tie bound. -/
theorem
    sum_card_sectionSixFirstSecondRepeatedRepresentedCarrier_le_quarterTie
    (epsilon : Real) (hepsilon : 0 < epsilon)
    (hepsilonSmall : epsilon <= 1 / 64)
    (C : Finset Nat) {length : Nat} (hlength : 1 <= length)
    (hC : C ⊆ maynardAmbientCarrier ((10 ^ length : Nat) : Real))
    (hfive :
      5 < ((10 ^ length : Nat) : Real) ^ sectionSixThetaGap epsilon)
    (a b : Real)
    (houter : ∀ p, p ∈ sievePrimeInterval a b ->
      p ∈ sievePrimeInterval
        (sectionSixZOne epsilon ((10 ^ length : Nat) : Real))
        (sectionSixZFour ((10 ^ length : Nat) : Real))) :
    let X : Real := ((10 ^ length : Nat) : Real)
    let gap : Real := sectionSixThetaGap epsilon
    let z1 : Real := sectionSixZOne epsilon X
    let K : Nat := 2 ^ Nat.ceil (1 / gap)
    (∑ index ∈ sectionSixFirstSecondRepeatedIndices length z1 a b,
      ((sectionSixFirstRepeatedRepresentedCarrier C
        (Nat.toPNat' index.1) index.2).card : Real)) <=
      (K : Real) * ((sectionSixDirectQuarterTieCarrier C X gap).card : Real) := by
  dsimp only
  let X : Real := ((10 ^ length : Nat) : Real)
  let gap : Real := sectionSixThetaGap epsilon
  let z1 : Real := sectionSixZOne epsilon X
  let states := sectionSixFirstSecondRepeatedIndices length z1 a b
  let carrier : SectionSixFirstSecondRepeatedIndex -> Finset Nat :=
    fun index => sectionSixFirstRepeatedRepresentedCarrier C
      (Nat.toPNat' index.1) index.2
  have hX : 1 < X := by
    dsimp only [X]
    exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < (10 : Nat))
  have hgap : 0 < gap :=
    (sectionSix_parameter_bounds hepsilon hepsilonSmall).1
  have hfamilyData : ∀ index ∈ states,
      index.2.Prime ∧ X ^ gap < (index.2 : Real) ∧
      (index.2 : Real) <= X ^ (1 / 2 : Real) ∧
      weakRoughPredicate (X ^ gap) (Nat.toPNat' index.1 : Nat) := by
    intro index hindex
    have hindexData := mem_sectionSixFirstSecondRepeatedIndices.mp hindex
    have hpFull := houter index.1 hindexData.1
    have hpData := mem_sievePrimeInterval.mp hpFull
    have hqData := mem_sievePrimeInterval.mp hindexData.2
    have hthreshold :
        sectionSixFirstFactorThreshold length index.1 <=
          (index.1 : Real) := by
      simp [sectionSixFirstFactorThreshold]
    have hqUpper : (index.2 : Real) <= X ^ (1 / 2 : Real) := by
      calc
        (index.2 : Real) <=
            sectionSixFirstFactorThreshold length index.1 := hqData.2.2
        _ <= (index.1 : Real) := hthreshold
        _ <= X ^ (1 / 2 : Real) := by
          simpa only [X, sectionSixZFour_eq_rpow] using hpData.2.2
    have hpRough :
        weakRoughPredicate (X ^ gap) (Nat.toPNat' index.1 : Nat) := by
      rw [Nat.toPNat'_coe, if_pos hpData.1.pos]
      intro r hr hrp
      have hrEq : r = index.1 :=
        (Nat.prime_dvd_prime_iff_eq hr hpData.1).mp hrp
      simpa only [hrEq, X, gap, sectionSixZOne] using hpData.2.1.le
    exact ⟨hqData.1,
      by simpa only [z1, sectionSixZOne] using hqData.2.1,
      hqUpper, hpRough⟩
  have hsub : ∀ index ∈ states, carrier index ⊆
      sectionSixDirectQuarterTieCarrier C X gap := by
    intro index hindex
    have hdata := hfamilyData index hindex
    exact sectionSixFirstRepeatedRepresentedCarrier_subset_quarterTie
      (by simpa only [X, gap] using hfive)
      hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2
  have hfiber : ∀ n, n ∈ sectionSixDirectQuarterTieCarrier C X gap ->
      (states.filter fun index => n ∈ carrier index).card <=
        2 ^ Nat.ceil (1 / gap) := by
    intro n _hn
    apply sectionSixFirstRepeatedCarrierFiber_le states
      sectionSixFirstSecondRepeatedKey carrier hX hgap C hC
    · intro index hindex n hn
      have hfamily := hfamilyData index hindex
      have hnData := sectionSixFirstRepeatedRepresentedCarrier_mem_data
        (by simpa only [X, gap] using hfive)
        hfamily.1 hfamily.2.1 hfamily.2.2.2 hn
      exact ⟨hnData.1, hnData.2.1, hnData.2.2.1,
        hnData.2.2.2.2⟩
    · exact sectionSixFirstSecondRepeatedKey_injOn length z1 a b
  simpa only [states, carrier, X, gap, z1] using
    (sum_card_le_of_element_fiber_card_real states
      (sectionSixDirectQuarterTieCarrier C X gap) carrier
      (2 ^ Nat.ceil (1 / gap)) hsub hfiber)

end

end PrimesRestrictedDigits
