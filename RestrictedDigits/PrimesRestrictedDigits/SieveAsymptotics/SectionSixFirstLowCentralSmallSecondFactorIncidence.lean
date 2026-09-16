import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallSecondFactorCarriers
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixIncidenceAggregation
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIRegionSupport
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Low central-small second-factor incidence

Every represented second-factor tail lies uniformly below the Type II near carrier. Weakly
ordered prime quadruples give multiplicity one, so the total tail has no incidence loss.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, p. 143, Eq. (6.12).
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private theorem sectionSixFirstLowCentralSmallSecondFactor_tripleData
    {epsilon : Real} {length : Nat}
    {index : SectionSixFirstLowCentralSmallTripleIndex}
    (hindex : index ∈ sectionSixFirstLowCentralSmallTripleIndices
      epsilon length) :
    index.1.1.Prime ∧ index.1.2.Prime ∧ index.2.Prime ∧
      index.2 ≤ index.1.2 ∧ index.1.2 ≤ index.1.1 ∧
      (index.1.1 : Real) ≤
        sectionSixZTwo epsilon ((10 ^ length : Nat) : Real) ∧
      sectionSixZThree epsilon ((10 ^ length : Nat) : Real) <
        (sectionSixFirstPairProduct index.1 : Real) ∧
      (sectionSixFirstPairSquareProduct index.1 : Real) <
        sectionSixZSix epsilon ((10 ^ length : Nat) : Real) := by
  have htriple :=
    mem_sectionSixFirstLowCentralSmallTripleIndices.mp hindex
  have hfiltered :
      index.1 ∈ sectionSixFirstStrictIndices epsilon length ∧
        sectionSixFirstPairMem epsilon length .lowCentralSmall index.1 := by
    classical
    simpa [sectionSixFirstPairPieceIndices] using htriple.1
  have hpiece :
      index.1 ∈ sectionSixFirstLowStrictIndices epsilon length ∧
        sectionSixZThree epsilon ((10 ^ length : Nat) : Real) <
          (sectionSixFirstPairProduct index.1 : Real) ∧
        (sectionSixFirstPairProduct index.1 : Real) <
          sectionSixZFive epsilon ((10 ^ length : Nat) : Real) ∧
        (sectionSixFirstPairSquareProduct index.1 : Real) <
          sectionSixZSix epsilon ((10 ^ length : Nat) : Real) := by
    simpa [sectionSixFirstPairMem] using hfiltered.2
  have hpq := mem_sectionSixFirstSecondRepeatedIndices.mp hpiece.1
  have hp := mem_sievePrimeInterval.mp hpq.1
  have hq := mem_sievePrimeInterval.mp hpq.2
  have hr := mem_sievePrimeInterval.mp htriple.2
  have hqp : index.1.2 ≤ index.1.1 := by
    have hthreshold : sectionSixFirstFactorThreshold length index.1.1 ≤
        (index.1.1 : Real) := min_le_left _ _
    exact_mod_cast hq.2.2.trans hthreshold
  have hrq : index.2 ≤ index.1.2 := by
    exact_mod_cast hr.2.2
  exact ⟨hp.1, hq.1, hr.1, hrq, hqp, hp.2.2,
    hpiece.2.1, hpiece.2.2.2⟩

private theorem sectionSixFirstLowCentralSmallSecondFactor_zSix_mul_zTwo
    {epsilon X : Real} (hX : 0 < X) :
    sectionSixZSix epsilon X * sectionSixZTwo epsilon X = X := by
  rw [sectionSixZSix, sectionSixZTwo, ← Real.rpow_add hX]
  have : (1 - sectionSixThetaOne epsilon) +
      sectionSixThetaOne epsilon = 1 := by ring
  rw [this, Real.rpow_one]

private theorem sectionSixFirstLowCentralSmallSecondFactor_four_le_quotient
    {epsilon : Real} {length : Nat}
    {index : SectionSixFirstLowCentralSmallTripleIndex}
    (hfour : (4 : Real) ≤
      sectionSixZOne epsilon ((10 ^ length : Nat) : Real))
    (hindex : index ∈ sectionSixFirstLowCentralSmallTripleIndices
      epsilon length) :
    (4 : Real) ≤ ((10 ^ length : Nat) : Real) /
      (sectionSixFirstLowCentralSmallTripleProduct index : Real) := by
  let X : Real := ((10 ^ length : Nat) : Real)
  let p : Real := (index.1.1 : Real)
  let q : Real := (index.1.2 : Real)
  let r : Real := (index.2 : Real)
  let d : Real :=
    (sectionSixFirstLowCentralSmallTripleProduct index : Real)
  rcases sectionSixFirstLowCentralSmallSecondFactor_tripleData hindex with
    ⟨hp, hq, hr, hrqNat, hqpNat, hpUpper, _hcentral, hsquare⟩
  have hpPos : 0 < p := by dsimp only [p]; exact_mod_cast hp.pos
  have hqPos : 0 < q := by dsimp only [q]; exact_mod_cast hq.pos
  have hrPos : 0 < r := by dsimp only [r]; exact_mod_cast hr.pos
  have hdPos : 0 < d := by
    dsimp only [d]
    exact_mod_cast Nat.mul_pos (Nat.mul_pos hp.pos hq.pos) hr.pos
  have hXPos : 0 < X := by dsimp only [X]; positivity
  have hrq : r ≤ q := by dsimp only [r, q]; exact_mod_cast hrqNat
  have hqp : q ≤ p := by dsimp only [q, p]; exact_mod_cast hqpNat
  have hqUpper : q ≤ sectionSixZTwo epsilon X :=
    hqp.trans (by simpa only [X, p] using hpUpper)
  have hrr : r * r ≤ q * q :=
    mul_self_le_mul_self hrPos.le hrq
  have hcap : d * r < X := by
    calc
      d * r = (p * q) * (r * r) := by
        dsimp only [d, p, q, r,
          sectionSixFirstLowCentralSmallTripleProduct,
          sectionSixFirstPairProduct]
        norm_num
        ring
      _ ≤ (p * q) * (q * q) :=
        mul_le_mul_of_nonneg_left hrr (mul_nonneg hpPos.le hqPos.le)
      _ = (sectionSixFirstPairSquareProduct index.1 : Real) * q := by
        dsimp only [p, q, sectionSixFirstPairSquareProduct]
        norm_num
        ring
      _ < sectionSixZSix epsilon X * sectionSixZTwo epsilon X := by
        apply mul_lt_mul
        · simpa only [X] using hsquare
        · exact hqUpper
        · exact hqPos
        · exact (Real.rpow_pos_of_pos hXPos _).le
      _ = X :=
        sectionSixFirstLowCentralSmallSecondFactor_zSix_mul_zTwo hXPos
  have hrLower :=
    (mem_sievePrimeInterval.mp
      (mem_sectionSixFirstLowCentralSmallTripleIndices.mp hindex).2).2.1
  have hrQuot : r < X / d :=
    (lt_div_iff₀ hdPos).2 (by simpa [mul_comm] using hcap)
  exact hfour.trans (by simpa only [X, r] using hrLower.le) |>.trans
    hrQuot.le

private theorem sectionSixFirstLowCentralSmallSecondFactor_represented_lt
    {epsilon : Real} (hepsilon : 0 < epsilon)
    {length m : Nat}
    {index : SectionSixFirstLowCentralSmallTripleIndex}
    (hindex : index ∈ sectionSixFirstLowCentralSmallTripleIndices
      epsilon length) (hmr : m ≤ index.2) :
    (((m * sectionSixFirstLowCentralSmallTripleProduct index : Nat) : Real)) <
      ((10 ^ length : Nat) : Real) ^
        (1 - sectionSixThetaGap epsilon) := by
  let X : Real := ((10 ^ length : Nat) : Real)
  let p : Real := (index.1.1 : Real)
  let q : Real := (index.1.2 : Real)
  let r : Real := (index.2 : Real)
  let mR : Real := (m : Real)
  rcases sectionSixFirstLowCentralSmallSecondFactor_tripleData hindex with
    ⟨hp, hq, hr, hrqNat, _hqp, hpUpper, hcentral, hsquare⟩
  have hX : 1 < X := by
    have hlength : length ≠ 0 := by
      intro hzero
      subst length
      have hpTwo : (2 : Real) ≤ p := by
        dsimp only [p]
        exact_mod_cast hp.two_le
      have hpOne : p ≤ 1 := by
        norm_num [X, sectionSixZTwo] at hpUpper
        dsimp only [p]
        exact_mod_cast hpUpper
      linarith
    dsimp only [X]
    exact_mod_cast Nat.one_lt_pow hlength (by norm_num : 1 < (10 : Nat))
  have hXPos : 0 < X := zero_lt_one.trans hX
  have hpPos : 0 < p := by dsimp only [p]; exact_mod_cast hp.pos
  have hqPos : 0 < q := by dsimp only [q]; exact_mod_cast hq.pos
  have hrPos : 0 < r := by dsimp only [r]; exact_mod_cast hr.pos
  have hmrR : mR ≤ r := by dsimp only [mR, r]; exact_mod_cast hmr
  have hrq : r ≤ q := by dsimp only [r, q]; exact_mod_cast hrqNat
  have hmrq : mR * r ≤ q * q := by
    exact mul_le_mul (hmrR.trans hrq) hrq hrPos.le hqPos.le
  have hzThreePos : 0 < sectionSixZThree epsilon X :=
    Real.rpow_pos_of_pos hXPos _
  have hzSixPos : 0 < sectionSixZSix epsilon X :=
    Real.rpow_pos_of_pos hXPos _
  have hqTimesZThree :
      q * sectionSixZThree epsilon X < sectionSixZSix epsilon X := by
    calc
      q * sectionSixZThree epsilon X < q * (p * q) :=
        mul_lt_mul_of_pos_left
          (by simpa only [X, p, q, sectionSixFirstPairProduct,
            Nat.cast_mul] using hcentral) hqPos
      _ = (sectionSixFirstPairSquareProduct index.1 : Real) := by
        dsimp only [p, q, sectionSixFirstPairSquareProduct]
        norm_num
        ring
      _ < sectionSixZSix epsilon X := by simpa only [X] using hsquare
  have hqBound :
      q < sectionSixZSix epsilon X / sectionSixZThree epsilon X := by
    exact (lt_div_iff₀ hzThreePos).2
      (by simpa [mul_comm] using hqTimesZThree)
  have hrepresented :
      (((m * sectionSixFirstLowCentralSmallTripleProduct index : Nat) : Real)) <
        sectionSixZSix epsilon X *
          (sectionSixZSix epsilon X / sectionSixZThree epsilon X) := by
    calc
      (((m * sectionSixFirstLowCentralSmallTripleProduct index : Nat) : Real)) =
          (p * q) * (mR * r) := by
        dsimp only [p, q, r, mR,
          sectionSixFirstLowCentralSmallTripleProduct,
          sectionSixFirstPairProduct]
        norm_num
        ring
      _ ≤ (p * q) * (q * q) :=
        mul_le_mul_of_nonneg_left hmrq (mul_nonneg hpPos.le hqPos.le)
      _ = (sectionSixFirstPairSquareProduct index.1 : Real) * q := by
        dsimp only [p, q, sectionSixFirstPairSquareProduct]
        norm_num
        ring
      _ < sectionSixZSix epsilon X * q :=
        mul_lt_mul_of_pos_right (by simpa only [X] using hsquare) hqPos
      _ < sectionSixZSix epsilon X *
          (sectionSixZSix epsilon X / sectionSixZThree epsilon X) :=
        mul_lt_mul_of_pos_left hqBound hzSixPos
  have hpower :
      sectionSixZSix epsilon X *
          (sectionSixZSix epsilon X / sectionSixZThree epsilon X) =
        X ^ (2 - 2 * sectionSixThetaOne epsilon -
          sectionSixThetaTwo epsilon) := by
    simp only [sectionSixZSix, sectionSixZThree]
    rw [← Real.rpow_sub hXPos, ← Real.rpow_add hXPos]
    congr 1
    ring
  have hexponent :
      2 - 2 * sectionSixThetaOne epsilon - sectionSixThetaTwo epsilon <
        1 - sectionSixThetaGap epsilon := by
    rw [sectionSixThetaGap_eq]
    simp only [sectionSixThetaOne, sectionSixThetaTwo]
    linarith
  simpa only [X] using (hpower ▸ hrepresented).trans
    (Real.rpow_lt_rpow_of_exponent_lt hX hexponent)

private def sectionSixFirstLowCentralSmallSecondFactor_primeTuple
    (m : Nat) (index : SectionSixFirstLowCentralSmallTripleIndex) :
    Fin 4 → Nat :=
  Matrix.vecCons m
    (Matrix.vecCons index.2
      (Matrix.vecCons index.1.2 (fun _ : Fin 1 => index.1.1)))

private theorem sectionSixFirstLowCentralSmallSecondFactor_primeTuple_prime
    {m : Nat} {index : SectionSixFirstLowCentralSmallTripleIndex}
    (hm : m.Prime) (hr : index.2.Prime)
    (hq : index.1.2.Prime) (hp : index.1.1.Prime) :
    ∀ i, (sectionSixFirstLowCentralSmallSecondFactor_primeTuple
      m index i).Prime := by
  intro i
  fin_cases i <;>
    simp [sectionSixFirstLowCentralSmallSecondFactor_primeTuple,
      hm, hr, hq, hp]

private theorem sectionSixFirstLowCentralSmallSecondFactor_primeTuple_monotone
    {m : Nat} {index : SectionSixFirstLowCentralSmallTripleIndex}
    (hmr : m ≤ index.2) (hrq : index.2 ≤ index.1.2)
    (hqp : index.1.2 ≤ index.1.1) :
    Monotone (sectionSixFirstLowCentralSmallSecondFactor_primeTuple m index) := by
  have hpMono : Monotone (fun _ : Fin 1 => index.1.1) := by
    intro i j hij
    exact le_rfl
  unfold sectionSixFirstLowCentralSmallSecondFactor_primeTuple
  exact ((hpMono.vecCons hqp).vecCons hrq).vecCons hmr

private theorem sectionSixFirstLowCentralSmallSecondFactor_index_eq
    {mi mj : Nat} {i j : SectionSixFirstLowCentralSmallTripleIndex}
    (hmi : mi.Prime) (hmj : mj.Prime)
    (hip : i.1.1.Prime) (hiq : i.1.2.Prime) (hir : i.2.Prime)
    (hjp : j.1.1.Prime) (hjq : j.1.2.Prime) (hjr : j.2.Prime)
    (hmiR : mi ≤ i.2) (hiRQ : i.2 ≤ i.1.2) (hiQP : i.1.2 ≤ i.1.1)
    (hmjR : mj ≤ j.2) (hjRQ : j.2 ≤ j.1.2) (hjQP : j.1.2 ≤ j.1.1)
    (hproduct : mi * sectionSixFirstLowCentralSmallTripleProduct i =
      mj * sectionSixFirstLowCentralSmallTripleProduct j) : i = j := by
  have htupleProduct :
      primeTupleProduct
          (sectionSixFirstLowCentralSmallSecondFactor_primeTuple mi i) =
        primeTupleProduct
          (sectionSixFirstLowCentralSmallSecondFactor_primeTuple mj j) := by
    simpa [sectionSixFirstLowCentralSmallSecondFactor_primeTuple,
      primeTupleProduct, Fin.prod_univ_succ,
      sectionSixFirstLowCentralSmallTripleProduct,
      sectionSixFirstPairProduct, Nat.mul_assoc, Nat.mul_left_comm,
      Nat.mul_comm] using hproduct
  have htuple := eq_of_monotone_primeTupleProduct_eq
    (sectionSixFirstLowCentralSmallSecondFactor_primeTuple_prime
      hmi hir hiq hip)
    (sectionSixFirstLowCentralSmallSecondFactor_primeTuple_prime
      hmj hjr hjq hjp)
    (sectionSixFirstLowCentralSmallSecondFactor_primeTuple_monotone
      hmiR hiRQ hiQP)
    (sectionSixFirstLowCentralSmallSecondFactor_primeTuple_monotone
      hmjR hjRQ hjQP) htupleProduct
  have hp : i.1.1 = j.1.1 := by
    have h := congrFun htuple (3 : Fin 4)
    simpa [sectionSixFirstLowCentralSmallSecondFactor_primeTuple] using h
  have hq : i.1.2 = j.1.2 := by
    have h := congrFun htuple (2 : Fin 4)
    simpa [sectionSixFirstLowCentralSmallSecondFactor_primeTuple] using h
  have hr : i.2 = j.2 := by
    have h := congrFun htuple (1 : Fin 4)
    simpa [sectionSixFirstLowCentralSmallSecondFactor_primeTuple] using h
  cases i with
  | mk iPair iR =>
      cases j with
      | mk jPair jR =>
          cases iPair with
          | mk ip iq =>
              cases jPair with
              | mk jp jq =>
                  simp only at hp hq hr
                  subst jp
                  subst jq
                  subst jR
                  rfl

private noncomputable def
    sectionSixFirstLowCentralSmallSecondFactor_representedTail
    (C : Finset Nat) (length : Nat)
    (index : SectionSixFirstLowCentralSmallTripleIndex) : Finset Nat :=
  (sectionSixFirstLowCentralSmallSecondFactorTail C length index).image
    (fun m => m * sectionSixFirstLowCentralSmallTripleProduct index)

private theorem
    sectionSixFirstLowCentralSmallSecondFactor_card_representedTail
    (C : Finset Nat) (length : Nat)
    {index : SectionSixFirstLowCentralSmallTripleIndex}
    (hp : index.1.1.Prime) (hq : index.1.2.Prime) (hr : index.2.Prime) :
    (sectionSixFirstLowCentralSmallSecondFactor_representedTail
      C length index).card =
      (sectionSixFirstLowCentralSmallSecondFactorTail C length index).card := by
  unfold sectionSixFirstLowCentralSmallSecondFactor_representedTail
  rw [Finset.card_image_of_injective]
  intro a b hab
  exact Nat.eq_of_mul_eq_mul_right
    (Nat.mul_pos (Nat.mul_pos hp.pos hq.pos) hr.pos) hab

private theorem
    sectionSixFirstLowCentralSmallSecondFactor_representedTail_subset
    {epsilon delta : Real} (hepsilon : 0 < epsilon) (C : Finset Nat)
    {length : Nat} (hlength : 1 ≤ length)
    (hC : C ⊆ maynardAmbientCarrier ((10 ^ length : Nat) : Real))
    (hwidth : delta ^ 2 ≤ sectionSixThetaGap epsilon)
    {index : SectionSixFirstLowCentralSmallTripleIndex}
    (hindex : index ∈ sectionSixFirstLowCentralSmallTripleIndices
      epsilon length)
    (hquot : (4 : Real) ≤ ((10 ^ length : Nat) : Real) /
      (sectionSixFirstLowCentralSmallTripleProduct index : Real)) :
    sectionSixFirstLowCentralSmallSecondFactor_representedTail
        C length index ⊆
      C \ typeIINearXCarrier (10 ^ length) delta := by
  let X : Real := ((10 ^ length : Nat) : Real)
  have hX : 1 < X := by
    dsimp only [X]
    exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < (10 : Nat))
  rcases sectionSixFirstLowCentralSmallSecondFactor_tripleData hindex with
    ⟨hp, hq, hr, _hrq, _hqp, _hpUpper, _hcentral, _hsquare⟩
  intro n hn
  rw [sectionSixFirstLowCentralSmallSecondFactor_representedTail,
    Finset.mem_image] at hn
  rcases hn with ⟨m, hmTail, rfl⟩
  have hm := (mem_sectionSixFirstLowCentralSmallSecondFactorTail_iff
    hp hq hr hC hquot).mp hmTail
  rw [Finset.mem_sdiff]
  refine ⟨hm.1, ?_⟩
  intro hnear
  have hrepresented :=
    sectionSixFirstLowCentralSmallSecondFactor_represented_lt
      hepsilon hindex hm.2.2.2
  have hexponent :
      1 - sectionSixThetaGap epsilon ≤ 1 - delta ^ 2 := by linarith
  have hpower :
      X ^ (1 - sectionSixThetaGap epsilon) ≤ X ^ (1 - delta ^ 2) :=
    Real.rpow_le_rpow_of_exponent_le hX.le hexponent
  have hupper :
      ((((m * sectionSixFirstLowCentralSmallTripleProduct index : Nat) :
        Real))) ≤ X ^ (1 - delta ^ 2) := by
    simpa only [X] using hrepresented.trans_le hpower |>.le
  exact (not_lt_of_ge hupper) (mem_typeIINearXCarrier.mp hnear).2

private theorem sectionSixFirstLowCentralSmallSecondFactor_fiber_le_one
    {epsilon : Real} (C : Finset Nat) {length : Nat}
    (hC : C ⊆ maynardAmbientCarrier ((10 ^ length : Nat) : Real))
    (hfour : (4 : Real) ≤ sectionSixZOne epsilon
      ((10 ^ length : Nat) : Real)) (n : Nat) :
    ((sectionSixFirstLowCentralSmallTripleIndices epsilon length).filter
      fun index => n ∈
        sectionSixFirstLowCentralSmallSecondFactor_representedTail
          C length index).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro i j hi hj
  have hiData := Finset.mem_filter.mp hi
  have hjData := Finset.mem_filter.mp hj
  rcases sectionSixFirstLowCentralSmallSecondFactor_tripleData hiData.1 with
    ⟨hip, hiq, hir, hiRQ, hiQP, _hiUpper, _hiCentral, _hiSquare⟩
  rcases sectionSixFirstLowCentralSmallSecondFactor_tripleData hjData.1 with
    ⟨hjp, hjq, hjr, hjRQ, hjQP, _hjUpper, _hjCentral, _hjSquare⟩
  have hiQuot := sectionSixFirstLowCentralSmallSecondFactor_four_le_quotient
    hfour hiData.1
  have hjQuot := sectionSixFirstLowCentralSmallSecondFactor_four_le_quotient
    hfour hjData.1
  rw [sectionSixFirstLowCentralSmallSecondFactor_representedTail,
    Finset.mem_image] at hiData hjData
  rcases hiData.2 with ⟨mi, hmiTail, hmiValue⟩
  rcases hjData.2 with ⟨mj, hmjTail, hmjValue⟩
  have hmi := (mem_sectionSixFirstLowCentralSmallSecondFactorTail_iff
    hip hiq hir hC hiQuot).mp hmiTail
  have hmj := (mem_sectionSixFirstLowCentralSmallSecondFactorTail_iff
    hjp hjq hjr hC hjQuot).mp hmjTail
  exact sectionSixFirstLowCentralSmallSecondFactor_index_eq
    hmi.2.1 hmj.2.1 hip hiq hir hjp hjq hjr
    hmi.2.2.2 hiRQ hiQP hmj.2.2.2 hjRQ hjQP
    (hmiValue.trans hmjValue.symm)

/-- The total low central-small second-factor tail is bounded by the common
outside-near carrier, with no incidence loss. -/
theorem sectionSixFirstLowCentralSmallSecondFactorTailSum_le_outsideNear
    {epsilon delta : Real} (hepsilon : 0 < epsilon) (C : Finset Nat)
    {length : Nat} (hlength : 1 ≤ length)
    (hC : C ⊆ maynardAmbientCarrier ((10 ^ length : Nat) : Real))
    (hfour : (4 : Real) ≤ sectionSixZOne epsilon
      ((10 ^ length : Nat) : Real))
    (hwidth : delta ^ 2 ≤ sectionSixThetaGap epsilon) :
    (∑ index ∈ sectionSixFirstLowCentralSmallTripleIndices epsilon length,
      ((sectionSixFirstLowCentralSmallSecondFactorTail
        C length index).card : Real)) ≤
      ((C \ typeIINearXCarrier (10 ^ length) delta).card : Real) := by
  let states := sectionSixFirstLowCentralSmallTripleIndices epsilon length
  let outside := C \ typeIINearXCarrier (10 ^ length) delta
  let represented := fun index =>
    sectionSixFirstLowCentralSmallSecondFactor_representedTail
      C length index
  calc
    (∑ index ∈ sectionSixFirstLowCentralSmallTripleIndices epsilon length,
        ((sectionSixFirstLowCentralSmallSecondFactorTail
          C length index).card : Real)) =
        ∑ index ∈ states, ((represented index).card : Real) := by
      apply Finset.sum_congr rfl
      intro index hindex
      rcases sectionSixFirstLowCentralSmallSecondFactor_tripleData
          (by simpa only [states] using hindex) with
        ⟨hp, hq, hr, _hrq, _hqp, _hpUpper, _hcentral, _hsquare⟩
      rw [sectionSixFirstLowCentralSmallSecondFactor_card_representedTail
        C length hp hq hr]
    _ ≤ (1 : Real) * (outside.card : Real) := by
      simpa only [Nat.cast_one] using
        (sum_card_le_of_element_fiber_card_real states outside represented 1
          (by
            intro index hindex
            dsimp only [represented, outside] at hindex ⊢
            exact
              sectionSixFirstLowCentralSmallSecondFactor_representedTail_subset
                hepsilon C hlength hC hwidth hindex
                (sectionSixFirstLowCentralSmallSecondFactor_four_le_quotient
                  hfour hindex))
          (by
            intro n hn
            dsimp only [states, represented, outside] at hn ⊢
            exact sectionSixFirstLowCentralSmallSecondFactor_fiber_le_one
              C hC hfour n))
    _ = ((C \ typeIINearXCarrier (10 ^ length) delta).card : Real) := by
      simp only [one_mul, outside]

end

end PrimesRestrictedDigits
