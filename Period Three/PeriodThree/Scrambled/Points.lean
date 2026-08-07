module

public import PeriodThree.Interval.Itinerary
public import PeriodThree.Scrambled.Realization

meta import all Mathlib.Tactic.Continuity -- shake: keep (used by realization continuity)
meta import all Mathlib.Tactic.Linarith -- shake: keep (used by endpoint estimates)

/-!
# Realized coded points

This file realizes every repeated-bit itinerary, recovers its code with the
uniform endpoint gap, and constructs the uncountable nonperiodic candidate set
from [LY75, Appendix 2, pp. 990-992].
-/

@[expose] public section

open Set

namespace PeriodThree

/-- All reviewed interval, continuity, and gap data needed to realize the
Appendix 2 codes [LY75, Appendix 2, pp. 990-992]. -/
structure CodingContext (J : Set ℝ) (F : ℝ → ℝ) (a : ℝ) where
  /-- Continuity of the map on the ambient interval. -/
  continuousOn : ContinuousOn F J
  /-- Forward invariance of the ambient interval. -/
  mapsTo : MapsTo F J J
  /-- The interval and limit data used by the code realization. -/
  reversing : IncreasingReversingData J F a
  /-- The uniform endpoint gap for the realization. -/
  gap : IncreasingUniformGap reversing

/-- The increasing orbit-order hypotheses supply a complete coding context for
[LY75, Appendix 2, pp. 990-992]. -/
theorem existsCodingContext
    {J : Set ℝ} {F : ℝ → ℝ} {a : ℝ}
    (hJ : J.OrdConnected) (hF : ContinuousOn F J)
    (hFJ : MapsTo F J J) (haJ : a ∈ J)
    (horder : (F^[3]) a ≤ a ∧ a < F a ∧ F a < (F^[2]) a) :
    Nonempty (CodingContext J F a) := by
  obtain ⟨D⟩ := existsReversingNestOfIncreasingOrder hJ hF hFJ haJ horder
  obtain ⟨gap⟩ := existsIncreasingUniformGap hF hFJ horder D
  exact ⟨⟨hF, hFJ, D, gap⟩⟩

/-- Every code has a point following all its scheduled compact intervals, by
[LY75, Lemma 1 and Appendix 2, pp. 987, 990-992]. -/
theorem existsPointFollowingCode
    {J : Set ℝ} {F : ℝ → ℝ} {a : ℝ}
    (C : CodingContext J F a) (beta : ℕ → Bool) :
    ∃ x ∈ Icc (codeLeft C.reversing beta 0)
        (codeRight C.reversing beta 0),
      ∀ n : ℕ,
        (F^[n]) x ∈ Icc (codeLeft C.reversing beta n)
          (codeRight C.reversing beta n) :=
  existsOrbitFollowingIntervals C.continuousOn C.mapsTo
    (codeLeft_le_codeRight C.reversing beta)
    (codeInterval_subset C.reversing beta)
    (codeInterval_succ_subset_image C.reversing beta)

/-- A chosen point realizing a repeated-bit itinerary from
[LY75, Appendix 2, pp. 990-992]. -/
noncomputable def codedPoint
    {J : Set ℝ} {F : ℝ → ℝ} {a : ℝ}
    (C : CodingContext J F a) (beta : ℕ → Bool) : ℝ :=
  (existsPointFollowingCode C beta).choose

/-- Every iterate of a chosen coded point lies in its scheduled interval
[LY75, Appendix 2, pp. 990-992]. -/
theorem codedPoint_iterate_mem
    {J : Set ℝ} {F : ℝ → ℝ} {a : ℝ}
    (C : CodingContext J F a) (beta : ℕ → Bool) (n : ℕ) :
    (F^[n]) (codedPoint C beta) ∈
      Icc (codeLeft C.reversing beta n)
        (codeRight C.reversing beta n) :=
  (existsPointFollowingCode C beta).choose_spec.2 n

/-- Every chosen coded point belongs to the ambient interval `J`, as required
in [LY75, Theorem I, part T2, p. 987]. -/
theorem codedPoint_mem
    {J : Set ℝ} {F : ℝ → ℝ} {a : ℝ}
    (C : CodingContext J F a) (beta : ℕ → Bool) :
    codedPoint C beta ∈ J := by
  apply codeInterval_subset C.reversing beta 0
  simpa using codedPoint_iterate_mem C beta 0

/-- At a `K` tag, a realized orbit lies uniformly below the common endpoint,
formalizing the exclusion in [LY75, Appendix 2, p. 991]. -/
theorem codedPoint_lt_of_tag_k
    {J : Set ℝ} {F : ℝ → ℝ} {a : ℝ}
    (C : CodingContext J F a) (beta : ℕ → Bool) {n : ℕ}
    (hn : codeTag beta n = .k) :
    (F^[n]) (codedPoint C beta) < F a - C.gap.delta := by
  have hxK : (F^[n]) (codedPoint C beta) ∈ Icc a (F a) := by
    simpa [codeLeft, codeRight, CodeTag.leftEndpoint, CodeTag.rightEndpoint, hn]
      using codedPoint_iterate_mem C beta n
  have hn2Base : (codeTag beta (n + 2)).IsInBase :=
    (codeTag_k_next_two_inBase beta hn).2
  have hx2Base : (F^[n + 2]) (codedPoint C beta) ∈ Icc (F a) ((F^[2]) a) :=
    CodeTag.interval_subset_base C.reversing hn2Base
      (codedPoint_iterate_mem C beta (n + 2))
  apply C.gap.k_value_lt hxK
  rw [show n + 2 = 2 + n by omega] at hx2Base
  simpa [Function.iterate_add_apply] using hx2Base

/-- At a base-contained tag, a realized orbit lies on or above the common
endpoint [LY75, Appendix 2, p. 991]. -/
theorem le_codedPoint_of_tag_inBase
    {J : Set ℝ} {F : ℝ → ℝ} {a : ℝ}
    (C : CodingContext J F a) (beta : ℕ → Bool) {n : ℕ}
    (hn : (codeTag beta n).IsInBase) :
    F a ≤ (F^[n]) (codedPoint C beta) :=
  (CodeTag.interval_subset_base C.reversing hn
    (codedPoint_iterate_mem C beta n)).1

/-- Different bits give orbit values separated by the uniform gap at the same
encoding time [LY75, Appendix 2, claim (A.4), p. 991]. -/
theorem codedPoints_encodingDistance_ge
    {J : Set ℝ} {F : ℝ → ℝ} {a : ℝ}
    (C : CodingContext J F a) {beta gamma : ℕ → Bool} {i t : ℕ}
    (ht : (Nat.unpair t).1 = i) (hbit : beta i ≠ gamma i) :
    C.gap.delta ≤
      |(F^[encodingTime t]) (codedPoint C beta) -
        (F^[encodingTime t]) (codedPoint C gamma)| := by
  have hbetaTag := codeTag_encodingTime beta t
  have hgammaTag := codeTag_encodingTime gamma t
  rw [ht] at hbetaTag hgammaTag
  cases hbeta : beta i <;> cases hgamma : gamma i
  · exact (hbit (by simp [hbeta, hgamma])).elim
  · have hx := le_codedPoint_of_tag_inBase (n := encodingTime t) C beta
      (by rw [hbetaTag]; simp [hbeta, CodeTag.IsInBase])
    have hy := codedPoint_lt_of_tag_k (n := encodingTime t) C gamma
      (by simpa [hgamma] using hgammaTag)
    have hyx : (F^[encodingTime t]) (codedPoint C gamma) ≤
        (F^[encodingTime t]) (codedPoint C beta) := by
      linarith [C.gap.delta_pos]
    rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
    linarith
  · have hx := codedPoint_lt_of_tag_k (n := encodingTime t) C beta
      (by simpa [hbeta] using hbetaTag)
    have hy := le_codedPoint_of_tag_inBase (n := encodingTime t) C gamma
      (by rw [hgammaTag]; simp [hgamma, CodeTag.IsInBase])
    have hxy : (F^[encodingTime t]) (codedPoint C beta) ≤
        (F^[encodingTime t]) (codedPoint C gamma) := by
      linarith [C.gap.delta_pos]
    rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
    linarith
  · exact (hbit (by simp [hbeta, hgamma])).elim

/-- A universal start and any positive in-block shift are uniformly separated,
the estimate used for condition (B) in [LY75, Appendix 2, p. 991]. -/
theorem codedPoint_universalShiftDistance_ge
    {J : Set ℝ} {F : ℝ → ℝ} {a : ℝ}
    (C : CodingContext J F a) (beta : ℕ → Bool) (t : ℕ) {p : ℕ}
    (hp : 0 < p) (hpBound : p < 2 * universalRoot t + 1) :
    C.gap.delta ≤
      |(F^[universalTime t]) (codedPoint C beta) -
        (F^[universalTime t + p]) (codedPoint C beta)| := by
  obtain ⟨hstart, hshift⟩ := codeTag_universalShift_inBase beta t hp hpBound
  have hx := codedPoint_lt_of_tag_k C beta hstart
  have hy := le_codedPoint_of_tag_inBase C beta hshift
  have hxy : (F^[universalTime t]) (codedPoint C beta) ≤
      (F^[universalTime t + p]) (codedPoint C beta) := by
    linarith [C.gap.delta_pos]
  rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
  linarith

/-- The first universal bridge iterate lies in the common lower interval used
for equation (2.1) of [LY75, Appendix 2, p. 992]. -/
theorem codedPoint_universalFirstBridge_mem
    {J : Set ℝ} {F : ℝ → ℝ} {a : ℝ}
    (C : CodingContext J F a) (beta : ℕ → Bool) (t : ℕ) :
    (F^[universalTime t + 1]) (codedPoint C beta) ∈
      Icc
        (C.reversing.nest.lower (2 * universalRoot t - 1))
        C.reversing.limits.lowerLimit := by
  simpa [codeLeft, codeRight, CodeTag.leftEndpoint, CodeTag.rightEndpoint,
    codeTag_universalFirstBridge] using
      codedPoint_iterate_mem C beta (universalTime t + 1)

/-- The candidate scrambled set is the range of the realized code map, as in
[LY75, Appendix 2, pp. 990-992]. -/
def codedSet
    {J : Set ℝ} {F : ℝ → ℝ} {a : ℝ}
    (C : CodingContext J F a) : Set ℝ :=
  Set.range (codedPoint C)

/-- The uniform encoding gap makes the realized code map injective, proving the
parameter recovery claimed in [LY75, Appendix 2, p. 991]. -/
theorem codedPoint_injective
    {J : Set ℝ} {F : ℝ → ℝ} {a : ℝ}
    (C : CodingContext J F a) :
    Function.Injective (codedPoint C) := by
  intro beta gamma hpoints
  apply funext
  intro i
  by_contra hbit
  have hsep := codedPoints_encodingDistance_ge C
    (i := i) (t := Nat.pair i 0) (by simp) hbit
  rw [hpoints] at hsep
  simp only [sub_self, abs_zero] at hsep
  exact (not_le_of_gt C.gap.delta_pos) hsep

private theorem boolSeq_uncountable : Uncountable (ℕ → Bool) := by
  rw [uncountable_iff_forall_not_surjective]
  intro e he
  let diagonal : ℕ → Bool := fun n => Bool.not (e n n)
  obtain ⟨n, hn⟩ := he diagonal
  have hcoord := congrFun hn n
  cases hvalue : e n n <;> simp [diagonal, hvalue] at hcoord

/-- The range of the injective Boolean code map is uncountable, completing the
cardinality argument of [LY75, Appendix 2, pp. 990-991]. -/
theorem codedSet_not_countable
    {J : Set ℝ} {F : ℝ → ℝ} {a : ℝ}
    (C : CodingContext J F a) :
    ¬(codedSet C).Countable := by
  intro hcount
  letI : Uncountable (ℕ → Bool) := boolSeq_uncountable
  have hpre : ((codedPoint C) ⁻¹' codedSet C).Countable :=
    hcount.preimage (codedPoint_injective C)
  rw [codedSet, Set.preimage_range] at hpre
  exact Set.not_countable_univ hpre

/-- No realized coded point is periodic; a positive period would identify two
uniformly separated universal-block iterates [LY75, Appendix 2, p. 991]. -/
theorem codedPoint_not_mem_periodicPts
    {J : Set ℝ} {F : ℝ → ℝ} {a : ℝ}
    (C : CodingContext J F a) (beta : ℕ → Bool) :
    codedPoint C beta ∉ Function.periodicPts F := by
  intro hperiodic
  obtain ⟨p, hp, hperiod⟩ := Function.mem_periodicPts.mp hperiodic
  have hpBound : p < 2 * universalRoot p + 1 := by
    simp [universalRoot]
    omega
  have hsep := codedPoint_universalShiftDistance_ge C beta p hp hpBound
  have heq : (F^[universalTime p + p]) (codedPoint C beta) =
      (F^[universalTime p]) (codedPoint C beta) := by
    rw [Function.iterate_add_apply, hperiod.eq]
  rw [heq] at hsep
  simp only [sub_self, abs_zero] at hsep
  exact (not_le_of_gt C.gap.delta_pos) hsep

/-- The coded candidate set lies in the ambient interval, as required by
[LY75, Theorem I, part T2, p. 987]. -/
theorem codedSet_subset
    {J : Set ℝ} {F : ℝ → ℝ} {a : ℝ}
    (C : CodingContext J F a) :
    codedSet C ⊆ J := by
  rintro _ ⟨beta, rfl⟩
  exact codedPoint_mem C beta

/-- The coded candidate set is disjoint from all periodic points, the explicit
nonperiodicity clause in [LY75, Theorem I, part T2, p. 987]. -/
theorem codedSet_disjoint_periodicPts
    {J : Set ℝ} {F : ℝ → ℝ} {a : ℝ}
    (C : CodingContext J F a) :
    Disjoint (codedSet C) (Function.periodicPts F) := by
  refine Set.disjoint_left.mpr fun _ hx hperiodic => ?_
  obtain ⟨beta, rfl⟩ := hx
  exact codedPoint_not_mem_periodicPts C beta hperiodic

end PeriodThree
