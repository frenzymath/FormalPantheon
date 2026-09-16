module

public import PeriodThree.Limits
public import PeriodThree.Scrambled.Points

meta import all Mathlib.Tactic.Linarith -- shake: keep (used by separation arithmetic)

/-!
# Scrambled-set estimates

This file proves the three frequent real inequalities behind the pairwise
Li-Yorke limits and separation from periodic points, then assembles the
increasing-orientation T2 conclusion from [LY75, Appendix 2, pp. 991-992].
-/

@[expose] public section

open Set Filter

namespace PeriodThree

/-- Distinct codes are separated by the uniform gap at arbitrarily late common
encoding times [LY75, Appendix 2, claim (A.4), p. 991]. -/
theorem frequently_pair_separated
    {J : Set ℝ} {F : ℝ → ℝ} {a : ℝ}
    (C : CodingContext J F a) {beta gamma : ℕ → Bool}
    (h : beta ≠ gamma) :
    ∃ᶠ n in Filter.atTop,
      C.gap.delta ≤
        |(F^[n]) (codedPoint C beta) - (F^[n]) (codedPoint C gamma)| := by
  obtain ⟨i, hbit⟩ := Function.ne_iff.mp h
  exact (frequently_encodingTime_of_bit i).mono fun n ⟨t, hn, ht⟩ => by
    subst n
    exact codedPoints_encodingDistance_ge C ht hbit

/-- Every pair of coded orbits enters the same shrinking lower bridge
arbitrarily late [LY75, Appendix 2, equation (2.1), p. 992]. -/
theorem frequently_pair_close
    {J : Set ℝ} {F : ℝ → ℝ} {a : ℝ}
    (C : CodingContext J F a) (beta gamma : ℕ → Bool) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ᶠ n in Filter.atTop,
      |(F^[n]) (codedPoint C beta) - (F^[n]) (codedPoint C gamma)| < epsilon := by
  refine Filter.frequently_atTop.2 fun N => ?_
  have hconv : Tendsto
      (fun t => C.reversing.nest.lower (2 * universalRoot t - 1))
      atTop (nhds C.reversing.limits.lowerLimit) :=
    C.reversing.limits.lower_tendsto.comp tendsto_universalBridgeIndex
  have hclose : ∀ᶠ t in atTop,
      |C.reversing.nest.lower (2 * universalRoot t - 1) -
        C.reversing.limits.lowerLimit| < epsilon := by
    have hball := hconv.eventually (Metric.ball_mem_nhds _ hepsilon)
    simpa [Metric.mem_ball, Real.dist_eq] using hball
  have hlate : ∀ᶠ t in atTop, N ≤ universalTime t :=
    tendsto_universalTime.eventually (eventually_ge_atTop N)
  obtain ⟨t, htclose, htlate⟩ := (hclose.and hlate).exists
  let m := 2 * universalRoot t - 1
  let n := universalTime t + 1
  have hbeta := codedPoint_universalFirstBridge_mem C beta t
  have hgamma := codedPoint_universalFirstBridge_mem C gamma t
  change (F^[n]) (codedPoint C beta) ∈
    Icc (C.reversing.nest.lower m) C.reversing.limits.lowerLimit at hbeta
  change (F^[n]) (codedPoint C gamma) ∈
    Icc (C.reversing.nest.lower m) C.reversing.limits.lowerLimit at hgamma
  rcases hbeta with ⟨hbetaLower, hbetaUpper⟩
  rcases hgamma with ⟨hgammaLower, hgammaUpper⟩
  have hlower : C.reversing.nest.lower m ≤ C.reversing.limits.lowerLimit :=
    C.reversing.limits.lower_le_limit m
  have hdiameter : C.reversing.limits.lowerLimit - C.reversing.nest.lower m < epsilon := by
    rw [abs_of_nonpos (sub_nonpos.mpr hlower)] at htclose
    simpa [m] using htclose
  refine ⟨n, htlate.trans (Nat.le_add_right _ _), ?_⟩
  rw [abs_lt]
  constructor <;> linarith

/-- A coded orbit is separated frequently from every periodic orbit by half
the uniform gap [LY75, Appendix 2, condition (B), p. 991]. -/
theorem frequently_separated_from_periodic
    {J : Set ℝ} {F : ℝ → ℝ} {a : ℝ}
    (C : CodingContext J F a) (beta : ℕ → Bool) {q : ℝ}
    (hq : q ∈ Function.periodicPts F) :
    ∃ᶠ n in Filter.atTop,
      C.gap.delta / 2 ≤ |(F^[n]) (codedPoint C beta) - (F^[n]) q| := by
  obtain ⟨p, hp, hperiod⟩ := Function.mem_periodicPts.mp hq
  refine Filter.frequently_atTop.2 fun N => ?_
  obtain ⟨n, hnN, t, rfl, hpBound⟩ :=
    Filter.frequently_atTop.mp (frequently_universalShiftTime hp) N
  have hsep := codedPoint_universalShiftDistance_ge C beta t hp hpBound
  have hqEq : (F^[universalTime t + p]) q = (F^[universalTime t]) q := by
    rw [Function.iterate_add_apply, hperiod.eq]
  have htriangle := abs_sub_le
    ((F^[universalTime t]) (codedPoint C beta))
    ((F^[universalTime t]) q)
    ((F^[universalTime t + p]) (codedPoint C beta))
  have hsecond :
      |(F^[universalTime t]) q - (F^[universalTime t + p]) (codedPoint C beta)| =
        |(F^[universalTime t + p]) (codedPoint C beta) -
          (F^[universalTime t + p]) q| := by
    rw [← hqEq, abs_sub_comm]
  rw [hsecond] at htriangle
  have hsum := hsep.trans htriangle
  by_cases hfirst : C.gap.delta / 2 ≤
      |(F^[universalTime t]) (codedPoint C beta) - (F^[universalTime t]) q|
  · exact ⟨universalTime t, hnN, hfirst⟩
  · refine ⟨universalTime t + p, hnN.trans (Nat.le_add_right _ _), ?_⟩
    linarith

/-- Distinct realized codes satisfy both public Li-Yorke limit conditions from
[LY75, Theorem I, part T2 and Appendix 2, pp. 987, 991-992]. -/
theorem liYorkePair_codedPoints
    {J : Set ℝ} {F : ℝ → ℝ} {a : ℝ}
    (C : CodingContext J F a) {beta gamma : ℕ → Bool}
    (h : beta ≠ gamma) :
    LiYorkePair F (codedPoint C beta) (codedPoint C gamma) := by
  constructor
  · change 0 < Filter.limsup
      (fun n => ENNReal.ofReal
        |(F^[n]) (codedPoint C beta) - (F^[n]) (codedPoint C gamma)|) Filter.atTop
    exact positiveLimsupOfFrequentlyLe C.gap.delta_pos
      (frequently_pair_separated C h)
  · change Filter.liminf
      (fun n => ENNReal.ofReal
        |(F^[n]) (codedPoint C beta) - (F^[n]) (codedPoint C gamma)|) Filter.atTop = 0
    exact liminfEqZeroOfFrequentlyLt (fun epsilon hepsilon =>
      frequently_pair_close C beta gamma hepsilon)

/-- Every realized code has positive public limsup separation from every
periodic point [LY75, Theorem I, condition (B), p. 987]. -/
theorem separatedFromPeriodic_codedPoint
    {J : Set ℝ} {F : ℝ → ℝ} {a : ℝ}
    (C : CodingContext J F a) (beta : ℕ → Bool) {q : ℝ}
    (hq : q ∈ Function.periodicPts F) :
    SeparatedFromPeriodic F (codedPoint C beta) q := by
  unfold SeparatedFromPeriodic
  have hhalf : 0 < C.gap.delta / 2 := by linarith [C.gap.delta_pos]
  change 0 < Filter.limsup
    (fun n => ENNReal.ofReal |(F^[n]) (codedPoint C beta) - (F^[n]) q|) Filter.atTop
  exact positiveLimsupOfFrequentlyLe hhalf
    (frequently_separated_from_periodic C beta hq)

/-- The range of realized codes is an uncountable nonperiodic scrambled set in
the exact sense of [LY75, Theorem I, part T2, p. 987]. -/
theorem codedSet_isLiYorkeScrambledSet
    {J : Set ℝ} {F : ℝ → ℝ} {a : ℝ}
    (C : CodingContext J F a) :
    LiYorkeScrambledSet F J (codedSet C) := by
  refine ⟨codedSet_subset C, codedSet_not_countable C,
    codedSet_disjoint_periodicPts C, ?_⟩
  intro p q hp hq hpq
  obtain ⟨beta, rfl⟩ := hp
  obtain ⟨gamma, rfl⟩ := hq
  apply liYorkePair_codedPoints C
  intro hcodes
  exact hpq (congrArg (codedPoint C) hcodes)

/-- Every point in the coded set is separated from every periodic point in the
ambient interval, condition (B) of [LY75, Theorem I, p. 987]. -/
theorem codedSet_separatedFromPeriodic
    {J : Set ℝ} {F : ℝ → ℝ} {a : ℝ}
    (C : CodingContext J F a) :
    ∀ ⦃p q : ℝ⦄, p ∈ codedSet C → q ∈ J →
      q ∈ Function.periodicPts F → SeparatedFromPeriodic F p q := by
  intro p q hp _ hq
  obtain ⟨beta, rfl⟩ := hp
  exact separatedFromPeriodic_codedPoint C beta hq

/-- The increasing orbit-order branch supplies the complete T2 package of
[LY75, Theorem I, p. 987]. -/
theorem existsLiYorkeScrambledSetOfIncreasingOrder
    {J : Set ℝ} {F : ℝ → ℝ} {a : ℝ}
    (hJ : J.OrdConnected) (hF : ContinuousOn F J)
    (hFJ : MapsTo F J J) (haJ : a ∈ J)
    (horder : (F^[3]) a ≤ a ∧ a < F a ∧ F a < (F^[2]) a) :
    ∃ S : Set ℝ,
      LiYorkeScrambledSet F J S ∧
        ∀ ⦃p q : ℝ⦄, p ∈ S → q ∈ J →
          q ∈ Function.periodicPts F → SeparatedFromPeriodic F p q := by
  obtain ⟨C⟩ := existsCodingContext hJ hF hFJ haJ horder
  exact ⟨codedSet C, codedSet_isLiYorkeScrambledSet C,
    codedSet_separatedFromPeriodic C⟩

end PeriodThree
