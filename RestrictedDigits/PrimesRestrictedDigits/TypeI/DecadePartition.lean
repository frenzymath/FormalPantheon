import PrimesRestrictedDigits.TypeI.ModulusAggregation
import PrimesRestrictedDigits.Digits.FactorTenLocalization
import Mathlib.Data.Finset.Card

/-!
# Exact decimal-band partition for the Type I estimate

This implements the factor-ten partition immediately after equation (8.1) in the proof of
`MAYNARD-PRD-PUBLISHED`, Proposition 7.1. The final scale is capped at the real cutoff,
preserving the source endpoint `Q1 <= Q`.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- Reduced nondecimal denominators in the exact strict real-cutoff range. -/
def typeIReducedDenominatorsBelow (Q : Real) : Finset Nat :=
  (Finset.range (Nat.ceil Q)).filter fun q =>
    1 < q ∧ q.Coprime 10

/-- The source band upper endpoint, with one possible final partial band. -/
def typeIDecadeScale (Q : Real) (q : Nat) : Real :=
  min Q (factorTenScale q : Real)

/-- The active factor-ten scales below a real cutoff. -/
def typeIDecadeScalesBelow (Q : Real) : Finset Real :=
  (typeIReducedDenominatorsBelow Q).image (typeIDecadeScale Q)

/-- The reduced denominators assigned to one active factor-ten scale. -/
def typeIDecadeFiber (Q R : Real) : Finset Nat :=
  (typeIReducedDenominatorsBelow Q).filter fun q =>
    typeIDecadeScale Q q = R

private theorem typeIReducedDenominatorsBelow_mem
    {Q : Real} {q : Nat} (hq : q ∈ typeIReducedDenominatorsBelow Q) :
    q < Nat.ceil Q ∧ 1 < q ∧ q.Coprime 10 := by
  rcases Finset.mem_filter.mp hq with ⟨hqRange, hqOne, hqTen⟩
  exact ⟨Finset.mem_range.mp hqRange, hqOne, hqTen⟩

private theorem typeIDecadeScale_bounds
    {Q : Real} {q : Nat} (hq : q ∈ typeIReducedDenominatorsBelow Q) :
    typeIDecadeScale Q q / 10 < (q : Real) ∧
      (q : Real) ≤ typeIDecadeScale Q q ∧ typeIDecadeScale Q q ≤ Q := by
  rcases typeIReducedDenominatorsBelow_mem hq with
    ⟨hqCeil, hqOne, hqTen⟩
  have hqPos : 0 < q := by omega
  have hqQ : (q : Real) < Q := Nat.lt_ceil.mp hqCeil
  have hcanonical := factorTenScale_band q hqPos
  by_cases hQScale : Q ≤ (factorTenScale q : Real)
  · rw [typeIDecadeScale, min_eq_left hQScale]
    exact ⟨by linarith [hcanonical.1], hqQ.le, le_rfl⟩
  · have hscaleQ : (factorTenScale q : Real) ≤ Q :=
      le_of_not_ge hQScale
    rw [typeIDecadeScale, min_eq_right hscaleQ]
    exact ⟨hcanonical.1, hcanonical.2, hscaleQ⟩

/-- Every fiber is the exact source band `(R / 10, R]`, with `R <= Q`. -/
theorem typeIDecadeFiber_bounds
    {Q R : Real} {q : Nat} (hq : q ∈ typeIDecadeFiber Q R) :
    R / 10 < (q : Real) ∧ (q : Real) ≤ R ∧ R ≤ Q := by
  rcases Finset.mem_filter.mp hq with ⟨hqCarrier, hscale⟩
  have hbounds := typeIDecadeScale_bounds hqCarrier
  rw [hscale] at hbounds
  exact hbounds

/-- Summing over active scales and their equality fibers is an exact
partition of the reduced denominator carrier. -/
theorem sum_typeIDecadeFiber (Q : Real) (w : Nat → Real) :
    (∑ R ∈ typeIDecadeScalesBelow Q,
      ∑ q ∈ typeIDecadeFiber Q R, w q) =
      ∑ q ∈ typeIReducedDenominatorsBelow Q, w q := by
  classical
  simp only [typeIDecadeScalesBelow, typeIDecadeFiber]
  apply Finset.sum_fiberwise_of_maps_to (g := typeIDecadeScale Q)
  intro q hq
  exact Finset.mem_image.mpr ⟨q, hq, rfl⟩

private def typeIDecadeScaleCandidates (Q : Real) : Finset Real :=
  insert Q <| (Finset.range (Nat.clog 10 (Nat.ceil Q) + 1)).image fun j =>
    ((10 ^ j : Nat) : Real)

private theorem typeIDecadeScalesBelow_subset_candidates (Q : Real) :
    typeIDecadeScalesBelow Q ⊆ typeIDecadeScaleCandidates Q := by
  intro R hR
  rcases Finset.mem_image.mp hR with ⟨q, hq, rfl⟩
  rcases typeIReducedDenominatorsBelow_mem hq with
    ⟨hqCeil, hqOne, hqTen⟩
  by_cases hQScale : Q ≤ (factorTenScale q : Real)
  · rw [typeIDecadeScale, min_eq_left hQScale]
    exact Finset.mem_insert_self _ _
  · have hscaleQ : (factorTenScale q : Real) ≤ Q :=
      le_of_not_ge hQScale
    rw [typeIDecadeScale, min_eq_right hscaleQ]
    apply Finset.mem_insert.mpr
    right
    apply Finset.mem_image.mpr
    refine ⟨Nat.clog 10 q, ?_, rfl⟩
    exact Finset.mem_range.mpr <| Nat.lt_succ_of_le <|
      Nat.clog_mono_right 10 (Nat.le_of_lt hqCeil)

/-- There are at most logarithmically many active bands; `+2` accounts for
the exponent-zero candidate and the possible real-capped final scale. -/
theorem card_typeIDecadeScalesBelow_le (Q : Real) :
    (typeIDecadeScalesBelow Q).card ≤ Nat.clog 10 (Nat.ceil Q) + 2 := by
  classical
  calc
    (typeIDecadeScalesBelow Q).card ≤
        (typeIDecadeScaleCandidates Q).card :=
      Finset.card_le_card (typeIDecadeScalesBelow_subset_candidates Q)
    _ ≤ ((Finset.range (Nat.clog 10 (Nat.ceil Q) + 1)).image fun j =>
        ((10 ^ j : Nat) : Real)).card + 1 := by
      exact Finset.card_insert_le _ _
    _ ≤ (Finset.range (Nat.clog 10 (Nat.ceil Q) + 1)).card + 1 := by
      exact Nat.add_le_add_right Finset.card_image_le 1
    _ = Nat.clog 10 (Nat.ceil Q) + 2 := by simp

end


end PrimesRestrictedDigits
