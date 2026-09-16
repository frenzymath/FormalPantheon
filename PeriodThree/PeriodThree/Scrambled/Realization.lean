module

public import PeriodThree.Interval.ReversingLimits
public import PeriodThree.Scrambled.Coding

meta import all Mathlib.Tactic.Linarith -- shake: keep (used by gap arithmetic)

/-!
# Real interval interpretation of the square-index codes

This file interprets the symbolic schedule as the reversing intervals from
[LY75, Appendix 2, pp. 990-992] and extracts the uniform endpoint gap needed
for the scrambled-set estimates.
-/

@[expose] public section

open Set

namespace PeriodThree
namespace CodeTag

variable {J : Set ℝ} {F : ℝ → ℝ} {a : ℝ}

/-- Left endpoint of the real interval represented by a code tag in
[LY75, Appendix 2, pp. 991-992]. -/
def leftEndpoint (D : IncreasingReversingData J F a) : CodeTag → ℝ
  | .k => a
  | .base => F a
  | .lower m => D.nest.lower m
  | .upper _ => D.limits.upperLimit

/-- Right endpoint of the real interval represented by a code tag in
[LY75, Appendix 2, pp. 991-992]. -/
def rightEndpoint (D : IncreasingReversingData J F a) : CodeTag → ℝ
  | .k => F a
  | .base => (F^[2]) a
  | .lower _ => D.limits.lowerLimit
  | .upper m => D.nest.upper m

/-- The compact real interval represented by a code tag in
[LY75, Appendix 2, pp. 991-992]. -/
def interval (D : IncreasingReversingData J F a) (tag : CodeTag) : Set ℝ :=
  Icc (tag.leftEndpoint D) (tag.rightEndpoint D)

private theorem k_order
    (D : IncreasingReversingData J F a) : a ≤ F a := by
  have hbase : F a ∈ Icc (F a) ((F^[2]) a) := by
    constructor
    · exact le_rfl
    · simpa [D.nest.lower_zero, D.nest.upper_zero] using (D.nest.lower_lt_upper 0).le
  obtain ⟨x, hx, _⟩ := D.base_subset_image_k hbase
  exact hx.1.trans hx.2

/-- Every represented interval has ordered endpoints, for the interval
itineraries of [LY75, Appendix 2, pp. 991-992]. -/
theorem leftEndpoint_le_rightEndpoint
    (D : IncreasingReversingData J F a) (tag : CodeTag) :
    tag.leftEndpoint D ≤ tag.rightEndpoint D := by
  cases tag with
  | k => exact k_order D
  | base =>
      simpa [leftEndpoint, rightEndpoint, D.nest.lower_zero, D.nest.upper_zero]
        using (D.nest.lower_lt_upper 0).le
  | lower m => exact D.limits.lower_le_limit m
  | upper m => exact D.limits.limit_le_upper m

/-- Every non-`K` represented interval lies in the base interval `L` from
[LY75, Appendix 2, p. 991]. -/
theorem interval_subset_base
    (D : IncreasingReversingData J F a) {tag : CodeTag}
    (htag : tag.IsInBase) :
    tag.interval D ⊆ Icc (F a) ((F^[2]) a) := by
  cases tag with
  | k => simp [IsInBase] at htag
  | base => exact subset_rfl
  | lower m =>
      apply Icc_subset_Icc
      · exact (D.limits.lower_mem m).1
      · exact D.limits.limits_ordered.trans
          ((D.limits.limit_le_upper 0).trans (by simp [D.nest.upper_zero]))
  | upper m =>
      apply Icc_subset_Icc
      · exact ((D.limits.lower_mem 0).1.trans (D.limits.lower_le_limit 0)).trans
          D.limits.limits_ordered
      · exact (D.limits.upper_mem m).2

/-- Every represented interval lies in the ambient interval `J`, as required
by [LY75, Lemma 1 and Appendix 2, pp. 987, 991-992]. -/
theorem interval_subset
    (D : IncreasingReversingData J F a) (tag : CodeTag) :
    tag.interval D ⊆ J := by
  cases tag with
  | k => exact D.k_subset
  | base | lower _ | upper _ =>
      exact (interval_subset_base D (by simp [IsInBase])).trans D.base_subset

/-- A symbolic edge is exactly a covering relation between its interpreted
real intervals [LY75, Appendix 2, pp. 991-992]. -/
theorem interval_subset_image_of_follows
    (D : IncreasingReversingData J F a) {source target : CodeTag}
    (h : source.Follows target) :
    target.interval D ⊆ F '' source.interval D := by
  cases source with
  | k =>
      exact (interval_subset_base D h).trans D.base_subset_image_k
  | base =>
      cases target with
      | k => exact D.k_subset_image_base
      | base | lower _ | upper _ =>
          exact (interval_subset_base D (by simp [IsInBase])).trans
            D.base_subset_image_base
  | lower m =>
      cases m with
      | zero => simp [Follows] at h
      | succ m =>
          cases target with
          | k | base | lower _ => simp [Follows] at h
          | upper n =>
              simp only [Follows] at h
              subst n
              exact D.limits.lowerToUpperCover D.continuousOn_base m
  | upper m =>
      cases m with
      | zero =>
          cases target with
          | k =>
              simpa [interval, leftEndpoint, rightEndpoint, D.nest.upper_zero] using
                D.upperZero_covers_k
          | base | lower _ | upper _ => simp [Follows] at h
      | succ m =>
          cases target with
          | k | base | upper _ => simp [Follows] at h
          | lower n =>
              simp only [Follows] at h
              subst n
              exact D.limits.upperToLowerCover D.continuousOn_base m

end CodeTag

variable {J : Set ℝ} {F : ℝ → ℝ} {a : ℝ}

/-- Left endpoint of the interval scheduled at time `n` for
[LY75, Appendix 2, pp. 991-992]. -/
def codeLeft (D : IncreasingReversingData J F a)
    (beta : ℕ → Bool) (n : ℕ) : ℝ :=
  (codeTag beta n).leftEndpoint D

/-- Right endpoint of the interval scheduled at time `n` for
[LY75, Appendix 2, pp. 991-992]. -/
def codeRight (D : IncreasingReversingData J F a)
    (beta : ℕ → Bool) (n : ℕ) : ℝ :=
  (codeTag beta n).rightEndpoint D

/-- Scheduled interval endpoints are ordered, as required by the application of
[LY75, Lemma 1 and Appendix 2, pp. 987, 991-992]. -/
theorem codeLeft_le_codeRight (D : IncreasingReversingData J F a)
    (beta : ℕ → Bool) (n : ℕ) :
    codeLeft D beta n ≤ codeRight D beta n :=
  CodeTag.leftEndpoint_le_rightEndpoint D (codeTag beta n)

/-- Every scheduled interval lies in `J`, as required by [LY75, Lemma 1 and
Appendix 2, pp. 987, 991-992]. -/
theorem codeInterval_subset (D : IncreasingReversingData J F a)
    (beta : ℕ → Bool) (n : ℕ) :
    Icc (codeLeft D beta n) (codeRight D beta n) ⊆ J :=
  CodeTag.interval_subset D (codeTag beta n)

/-- Every scheduled interval is covered by the preceding one, the itinerary
hypothesis in [LY75, Lemma 1 and Appendix 2, pp. 987, 991-992]. -/
theorem codeInterval_succ_subset_image
    (D : IncreasingReversingData J F a) (beta : ℕ → Bool) (n : ℕ) :
    Icc (codeLeft D beta (n + 1)) (codeRight D beta (n + 1)) ⊆
      F '' Icc (codeLeft D beta n) (codeRight D beta n) :=
  CodeTag.interval_subset_image_of_follows D (codeTag_follows beta n)

/-- A uniform positive gap below the common endpoint of `K` and `L`, formalizing
the endpoint exclusion in [LY75, Appendix 2, p. 991]. -/
structure IncreasingUniformGap (D : IncreasingReversingData J F a) where
  /-- Positive distance below the common endpoint. -/
  delta : ℝ
  /-- Positivity of the endpoint gap. -/
  delta_pos : 0 < delta
  /-- Every admissible `K` point lies below the gap endpoint. -/
  k_value_lt : ∀ {x : ℝ},
    x ∈ Icc a (F a) →
    (F^[2]) x ∈ Icc (F a) ((F^[2]) a) →
    x < F a - delta

/-- The increasing orbit-order configuration has a uniform endpoint gap.  The
proof maximizes the closed set of `K`-points whose second iterate lies on or
above the base endpoint, as in [LY75, Appendix 2, p. 991]. -/
theorem existsIncreasingUniformGap
    (hF : ContinuousOn F J) (hFJ : MapsTo F J J)
    (horder : (F^[3]) a ≤ a ∧ a < F a ∧ F a < (F^[2]) a)
    (D : IncreasingReversingData J F a) :
    Nonempty (IncreasingUniformGap D) := by
  let A : Set (Icc a (F a)) := {x | F a ≤ (F^[2]) (x : ℝ)}
  letI : CompactSpace (Icc a (F a)) := isCompact_iff_compactSpace.mp isCompact_Icc
  have hIter : ContinuousOn (F^[2]) (Icc a (F a)) :=
    (hF.iterate hFJ 2).mono D.k_subset
  have hclosed : IsClosed A := by
    exact isClosed_le continuous_const hIter.restrict
  by_cases hA : A.Nonempty
  · obtain ⟨m, hmA, hmax⟩ :=
      hclosed.isCompact.exists_isMaxOn hA continuous_subtype_val.continuousOn
    have hmLt : (m : ℝ) < F a := by
      refine lt_of_le_of_ne m.property.2 ?_
      intro hmEq
      have hbad : F a ≤ (F^[3]) a := by
        have := hmA
        simpa [A, hmEq, Function.iterate_succ_apply'] using this
      linarith [horder.1, horder.2.1]
    refine ⟨{
      delta := (F a - (m : ℝ)) / 2
      delta_pos := by linarith
      k_value_lt := ?_
    }⟩
    intro x hxK hx2
    have hxA : (⟨x, hxK⟩ : Icc a (F a)) ∈ A := hx2.1
    have hxle : x ≤ (m : ℝ) := @hmax ⟨x, hxK⟩ hxA
    linarith
  · refine ⟨{
      delta := (F a - a) / 2
      delta_pos := by linarith [horder.2.1]
      k_value_lt := ?_
    }⟩
    intro x hxK hx2
    exact (hA ⟨⟨x, hxK⟩, hx2.1⟩).elim

end PeriodThree
