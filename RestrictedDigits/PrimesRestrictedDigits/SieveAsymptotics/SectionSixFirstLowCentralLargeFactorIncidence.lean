import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeFactorCarriers
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixIncidenceAggregation
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIRegionSupport

/-!
# Low central-large factor-reduction incidence

Every represented factor tail is uniformly below the Type II near carrier. Weakly ordered
prime triples give multiplicity one, so the total tail has no incidence loss.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, p. 141 after Eq. (6.8), referring to Eq. (6.4).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private theorem sectionSixFirstLowCentralLarge_factorPairData
    {epsilon : Real} {length : Nat} {index : SectionSixFirstStrictIndex}
    (hindex : index ∈ sectionSixFirstPairPieceIndices epsilon length
      .lowCentralLarge) :
    index.1.Prime ∧ index.2.Prime ∧ index.2 ≤ index.1 ∧
      (index.1 : Real) ≤
        sectionSixZTwo epsilon ((10 ^ length : Nat) : Real) ∧
      (sectionSixFirstPairProduct index : Real) <
        sectionSixZFive epsilon ((10 ^ length : Nat) : Real) := by
  have hfiltered : index ∈ sectionSixFirstStrictIndices epsilon length ∧
      sectionSixFirstPairMem epsilon length .lowCentralLarge index := by
    classical
    simpa [sectionSixFirstPairPieceIndices] using hindex
  have hpiece : index ∈ sectionSixFirstLowStrictIndices epsilon length ∧
      sectionSixZThree epsilon (((10 ^ length : Nat) : Real)) <
          (sectionSixFirstPairProduct index : Real) ∧
        (sectionSixFirstPairProduct index : Real) <
            sectionSixZFive epsilon (((10 ^ length : Nat) : Real)) ∧
          sectionSixZSix epsilon (((10 ^ length : Nat) : Real)) ≤
            (sectionSixFirstPairSquareProduct index : Real) := by
    simpa [sectionSixFirstPairMem] using hfiltered.2
  have hdata := mem_sectionSixFirstSecondRepeatedIndices.mp hpiece.1
  have hpData := mem_sievePrimeInterval.mp hdata.1
  have hqData := mem_sievePrimeInterval.mp hdata.2
  have hqLeP : index.2 ≤ index.1 := by
    have hqUpper := hqData.2.2
    have hthreshold : sectionSixFirstFactorThreshold length index.1 ≤
        (index.1 : Real) := min_le_left _ _
    exact_mod_cast hqUpper.trans hthreshold
  exact ⟨hpData.1, hqData.1, hqLeP, hpData.2.2, hpiece.2.2.1⟩

private def sectionSixFirstLowCentralLarge_factorPrimeTuple
    (m : Nat) (index : SectionSixFirstStrictIndex) : Fin 3 → Nat :=
  Matrix.vecCons m (Matrix.vecCons index.2 (fun _ : Fin 1 => index.1))

private theorem sectionSixFirstLowCentralLarge_factorPrimeTuple_prime
    {m : Nat} {index : SectionSixFirstStrictIndex}
    (hm : m.Prime) (hq : index.2.Prime) (hp : index.1.Prime) :
    ∀ i, (sectionSixFirstLowCentralLarge_factorPrimeTuple m index i).Prime := by
  intro i
  fin_cases i <;>
    simp [sectionSixFirstLowCentralLarge_factorPrimeTuple, hm, hq, hp]

private theorem sectionSixFirstLowCentralLarge_factorPrimeTuple_monotone
    {m : Nat} {index : SectionSixFirstStrictIndex}
    (hmq : m ≤ index.2) (hqp : index.2 ≤ index.1) :
    Monotone (sectionSixFirstLowCentralLarge_factorPrimeTuple m index) := by
  have hpMono : Monotone (fun _ : Fin 1 => index.1) := by
    intro i j hij
    exact le_rfl
  unfold sectionSixFirstLowCentralLarge_factorPrimeTuple
  exact (hpMono.vecCons hqp).vecCons hmq

/-- Every represented factor tail value lies outside the strict Type II near
carrier. Equality in the width premise is allowed because `p * q < z5` is
strict. -/
theorem sectionSixFirstLowCentralLargeFactorRepresentedTail_subset_outsideNear
    {epsilon delta : Real} (C : Finset Nat)
    {length : Nat} (hlength : 1 ≤ length)
    (hC : C ⊆ maynardAmbientCarrier ((10 ^ length : Nat) : Real))
    (hwidth : delta ^ 2 ≤ sectionSixThetaGap epsilon)
    {index : SectionSixFirstStrictIndex}
    (hindex : index ∈ sectionSixFirstPairPieceIndices epsilon length
      .lowCentralLarge)
    (hquot : (4 : Real) ≤ ((10 ^ length : Nat) : Real) /
      (sectionSixFirstPairProduct index : Real)) :
    sectionSixFirstLowCentralLargeFactorRepresentedTail C length index ⊆
      C \ typeIINearXCarrier (10 ^ length) delta := by
  let X : Real := ((10 ^ length : Nat) : Real)
  have hX : 1 < X := by
    dsimp only [X]
    exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < (10 : Nat))
  rcases sectionSixFirstLowCentralLarge_factorPairData hindex with
    ⟨hp, hq, hqp, hpUpper, hproductUpper⟩
  intro n hn
  rw [sectionSixFirstLowCentralLargeFactorRepresentedTail,
    Finset.mem_image] at hn
  rcases hn with ⟨m, hmTail, rfl⟩
  have hm := (mem_sectionSixFirstLowCentralLargeFactorTail_iff
    hp hq hC hquot).mp hmTail
  rw [Finset.mem_sdiff]
  refine ⟨hm.1, ?_⟩
  intro hnear
  have hmLeP : m ≤ index.1 := hm.2.2.2.trans hqp
  have hmUpper : (m : Real) ≤ sectionSixZTwo epsilon X := by
    exact (by exact_mod_cast hmLeP : (m : Real) ≤ (index.1 : Real)).trans
      (by simpa only [X] using hpUpper)
  have hzTwoPos : 0 < sectionSixZTwo epsilon X := by
    have hpPos : (0 : Real) < (index.1 : Real) := by
      exact_mod_cast hp.pos
    exact hpPos.trans_le (by simpa only [X] using hpUpper)
  have hrepresented :
      (((m * sectionSixFirstPairProduct index : Nat) : Real)) <
        sectionSixZTwo epsilon X * sectionSixZFive epsilon X := by
    calc
      (((m * sectionSixFirstPairProduct index : Nat) : Real)) =
          (m : Real) * (sectionSixFirstPairProduct index : Real) := by
        norm_num
      _ ≤ sectionSixZTwo epsilon X *
          (sectionSixFirstPairProduct index : Real) :=
        mul_le_mul_of_nonneg_right hmUpper (Nat.cast_nonneg _)
      _ < sectionSixZTwo epsilon X * sectionSixZFive epsilon X :=
        mul_lt_mul_of_pos_left (by simpa only [X] using hproductUpper)
          hzTwoPos
  have hcutoff :
      sectionSixZTwo epsilon X * sectionSixZFive epsilon X =
        X ^ (1 - sectionSixThetaGap epsilon) := by
    calc
      sectionSixZTwo epsilon X * sectionSixZFive epsilon X =
          X ^ (sectionSixThetaOne epsilon +
            (1 - sectionSixThetaTwo epsilon)) := by
        simp only [sectionSixZTwo, sectionSixZFive]
        rw [Real.rpow_add (by positivity : 0 < X)]
      _ = X ^ (1 - sectionSixThetaGap epsilon) := by
        congr 1
        unfold sectionSixThetaGap
        ring
  have hexponent : 1 - sectionSixThetaGap epsilon ≤ 1 - delta ^ 2 := by
    linarith
  have hnearUpper :
      (((m * sectionSixFirstPairProduct index : Nat) : Real)) ≤
        X ^ (1 - delta ^ 2) := by
    have hpower : X ^ (1 - sectionSixThetaGap epsilon) ≤
        X ^ (1 - delta ^ 2) :=
      Real.rpow_le_rpow_of_exponent_le hX.le hexponent
    exact ((hcutoff ▸ hrepresented).trans_le hpower).le
  exact (not_lt_of_ge hnearUpper) (mem_typeIINearXCarrier.mp hnear).2

/-- Weakly ordered prime triples make every represented factor-tail fiber have
cardinality at most one, including repeated prime factors. -/
theorem sectionSixFirstLowCentralLargeFactorProductFiber_le_one
    {epsilon : Real} (C : Finset Nat) {length : Nat}
    (hC : C ⊆ maynardAmbientCarrier ((10 ^ length : Nat) : Real))
    (hfour : (4 : Real) ≤ sectionSixZOne epsilon
      ((10 ^ length : Nat) : Real))
    (n : Nat) :
    ((sectionSixFirstPairPieceIndices epsilon length
      .lowCentralLarge).filter fun index =>
        n ∈ sectionSixFirstLowCentralLargeFactorRepresentedTail
          C length index).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro i j hi hj
  have hiData := Finset.mem_filter.mp hi
  have hjData := Finset.mem_filter.mp hj
  rcases sectionSixFirstLowCentralLarge_factorPairData hiData.1 with
    ⟨hip, hiq, hiqp, _hipUpper, _hiProductUpper⟩
  rcases sectionSixFirstLowCentralLarge_factorPairData hjData.1 with
    ⟨hjp, hjq, hjqp, _hjpUpper, _hjProductUpper⟩
  have hiQuot := sectionSixFirstLowCentralLarge_four_le_pairQuotient
    hfour hiData.1
  have hjQuot := sectionSixFirstLowCentralLarge_four_le_pairQuotient
    hfour hjData.1
  rw [sectionSixFirstLowCentralLargeFactorRepresentedTail,
    Finset.mem_image] at hiData hjData
  rcases hiData.2 with ⟨mi, hmiTail, hmiValue⟩
  rcases hjData.2 with ⟨mj, hmjTail, hmjValue⟩
  have hmi := (mem_sectionSixFirstLowCentralLargeFactorTail_iff
    hip hiq hC hiQuot).mp hmiTail
  have hmj := (mem_sectionSixFirstLowCentralLargeFactorTail_iff
    hjp hjq hC hjQuot).mp hmjTail
  have hvalue : mi * sectionSixFirstPairProduct i =
      mj * sectionSixFirstPairProduct j :=
    hmiValue.trans hmjValue.symm
  have hproduct :
      primeTupleProduct
          (sectionSixFirstLowCentralLarge_factorPrimeTuple mi i) =
        primeTupleProduct
          (sectionSixFirstLowCentralLarge_factorPrimeTuple mj j) := by
    simpa [sectionSixFirstLowCentralLarge_factorPrimeTuple,
      primeTupleProduct, Fin.prod_univ_succ, sectionSixFirstPairProduct,
      Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hvalue
  have htuple := eq_of_monotone_primeTupleProduct_eq
    (sectionSixFirstLowCentralLarge_factorPrimeTuple_prime hmi.2.1 hiq hip)
    (sectionSixFirstLowCentralLarge_factorPrimeTuple_prime hmj.2.1 hjq hjp)
    (sectionSixFirstLowCentralLarge_factorPrimeTuple_monotone
      hmi.2.2.2 hiqp)
    (sectionSixFirstLowCentralLarge_factorPrimeTuple_monotone
      hmj.2.2.2 hjqp)
    hproduct
  have hq : i.2 = j.2 := by
    have h := congrFun htuple (1 : Fin 3)
    simpa [sectionSixFirstLowCentralLarge_factorPrimeTuple] using h
  have hp : i.1 = j.1 := by
    have h := congrFun htuple (2 : Fin 3)
    simpa [sectionSixFirstLowCentralLarge_factorPrimeTuple] using h
  cases i with
  | mk ip iq =>
      cases j with
      | mk jp jq =>
          simp only at hp hq
          subst jp
          subst jq
          rfl

/-- The total low central-large factor tail is bounded by the common
small-product complement with no incidence loss. -/
theorem sectionSixFirstLowCentralLargeFactorTailSum_le_outsideNear
    {epsilon delta : Real} (C : Finset Nat)
    {length : Nat} (hlength : 1 ≤ length)
    (hC : C ⊆ maynardAmbientCarrier ((10 ^ length : Nat) : Real))
    (hfour : (4 : Real) ≤ sectionSixZOne epsilon
      ((10 ^ length : Nat) : Real))
    (hwidth : delta ^ 2 ≤ sectionSixThetaGap epsilon) :
    sectionSixFirstLowCentralLargeFactorTailSum C epsilon length ≤
      ((C \ typeIINearXCarrier (10 ^ length) delta).card : Real) := by
  let states := sectionSixFirstPairPieceIndices epsilon length .lowCentralLarge
  let outside := C \ typeIINearXCarrier (10 ^ length) delta
  calc
    sectionSixFirstLowCentralLargeFactorTailSum C epsilon length =
        ∑ index ∈ states,
          ((sectionSixFirstLowCentralLargeFactorRepresentedTail
            C length index).card : Real) := by
      unfold sectionSixFirstLowCentralLargeFactorTailSum
      apply Finset.sum_congr rfl
      intro index hindex
      rcases sectionSixFirstLowCentralLarge_factorPairData
          (by simpa only [states] using hindex) with
        ⟨hp, hq, _hqp, _hpUpper, _hproductUpper⟩
      rw [card_sectionSixFirstLowCentralLargeFactorRepresentedTail
        C length hp hq]
    _ ≤ (1 : Real) * (outside.card : Real) := by
      simpa only [Nat.cast_one] using
        (sum_card_le_of_element_fiber_card_real states outside
          (sectionSixFirstLowCentralLargeFactorRepresentedTail C length) 1
          (by
            intro index hindex
            dsimp only [states, outside] at hindex ⊢
            exact
              sectionSixFirstLowCentralLargeFactorRepresentedTail_subset_outsideNear
                C hlength hC hwidth hindex
                (sectionSixFirstLowCentralLarge_four_le_pairQuotient
                  hfour hindex))
          (by
            intro n hn
            dsimp only [states, outside] at hn ⊢
            exact sectionSixFirstLowCentralLargeFactorProductFiber_le_one
              C hC hfour n))
    _ = ((C \ typeIINearXCarrier (10 ^ length) delta).card : Real) := by
      simp only [one_mul, outside]

end

end PrimesRestrictedDigits
