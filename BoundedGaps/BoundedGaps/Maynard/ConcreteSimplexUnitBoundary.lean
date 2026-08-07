import BoundedGaps.Maynard.ConcreteSimplexOuter

noncomputable section

namespace BoundedGaps.Maynard

open Filter
open scoped BigOperators

def unitBoundaryBeta {H : Finset ℕ} (h : H) : H → ℝ :=
  fun i => if i = h then 0 else 1

def normalizedEngelsmaUnitBoundaryBoxMassSum
    (H : Finset ℕ) (alpha : ℝ) (N : ℕ) : ℝ :=
  ∑ h : H,
    normalizedEngelsmaFractionalTupleBoxMass H alpha
      (unitBoundaryBeta h) N

def engelsmaUnitBoundaryBoxUnion
    (H : Finset ℕ) (alpha : ℝ) (N : ℕ) : Finset (H → ℕ) :=
  (Finset.univ : Finset H).biUnion fun h =>
    engelsmaFractionalTupleBox H alpha (unitBoundaryBeta h) N

def engelsmaUnitBoundaryBoxUnionMass
    (H : Finset ℕ) (alpha : ℝ) (N : ℕ) : ℝ :=
  ∑ u ∈ engelsmaUnitBoundaryBoxUnion H alpha N,
    reciprocalTotientTupleWeight H u

def normalizedEngelsmaUnitBoundaryBoxUnionMass
    (H : Finset ℕ) (alpha : ℝ) (N : ℕ) : ℝ :=
  engelsmaUnitBoundaryBoxUnionMass H alpha N /
    (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
      Real.log (engelsmaMaynardRadius alpha N)) ^ Fintype.card H

theorem sum_biUnion_le_sum_sum_of_nonneg
    {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (I : Finset ι) (S : ι → Finset α) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    (∑ x ∈ I.biUnion S, f x) ≤
      ∑ i ∈ I, ∑ x ∈ S i, f x := by
  induction I using Finset.induction_on with
  | empty => simp
  | @insert a I ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have hinter : 0 ≤ ∑ x ∈ S a ∩ I.biUnion S, f x := by
      apply Finset.sum_nonneg
      intro x hx
      exact hf x
    have hunion := Finset.sum_union_inter
      (s₁ := S a) (s₂ := I.biUnion S) (f := f)
    linarith

theorem tendsto_normalizedEngelsmaUnitBoundaryBoxMassSum_zero
    {H : Finset ℕ} {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (fun N : ℕ =>
      normalizedEngelsmaUnitBoundaryBoxMassSum H alpha N)
      atTop (nhds 0) := by
  have hsum : Tendsto (fun N : ℕ =>
      ∑ h : H, normalizedEngelsmaFractionalTupleBoxMass H alpha
        (unitBoundaryBeta h) N) atTop (nhds (∑ _h : H, (0 : ℝ))) := by
    apply tendsto_finsetSum Finset.univ
    intro h hh
    have hlim := tendsto_normalizedEngelsmaFractionalTupleBoxMass
      halpha (unitBoundaryBeta h)
        (fun i => by
          by_cases hi : i = h <;> simp [unitBoundaryBeta, hi])
    have hzero : ∏ i : H, unitBoundaryBeta h i = 0 := by
      classical
      apply Finset.prod_eq_zero (Finset.mem_univ h)
      simp [unitBoundaryBeta]
    rw [hzero] at hlim
    simpa using hlim
  simpa [normalizedEngelsmaUnitBoundaryBoxMassSum] using hsum

theorem mem_engelsmaFractionalTupleBox_of_unit_coordinate
    {H : Finset ℕ} {alpha : ℝ} {N : ℕ} {u : H → ℕ} {h : H}
    (hu : u ∈ preSievedSimplexTupleSupport H
      (engelsmaMaynardRadius alpha N)
      (engelsmaMaynardModulus N)) (hunit : u h = 1) :
    u ∈ engelsmaFractionalTupleBox H alpha (unitBoundaryBeta h) N := by
  rw [engelsmaFractionalTupleBox, squarefreeCoprimeTupleBox,
    Fintype.mem_piFinset]
  intro i
  by_cases hi : i = h
  · subst i
    simp [unitBoundaryBeta, squarefreeCoprimeCoordinateSupport,
      engelsmaMaynardRadius, maynardDivisorCutoff, hunit]
  · have huCommon := (mem_preSievedSimplexTupleSupport_iff.mp hu).1
    have hui := Fintype.mem_piFinset.mp huCommon i
    have huiData := Finset.mem_filter.mp hui
    simp only [unitBoundaryBeta, hi, ↓reduceIte, mul_one]
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_Icc.mpr
        ⟨huiData.2.1, (Finset.mem_range.mp huiData.1).le⟩
    · simpa [unitBoundaryBeta, hi] using huiData.2.2

theorem preSievedSimplexUnitBoundary_subset_boxSumSupport
    {H : Finset ℕ} {alpha : ℝ} :
    ∀ N : ℕ, ∀ u : H → ℕ,
      u ∈ preSievedSimplexTupleSupport H
          (engelsmaMaynardRadius alpha N)
          (engelsmaMaynardModulus N) →
      (∃ h : H, u h = 1) →
      ∃ h : H, u ∈ engelsmaFractionalTupleBox H alpha
          (unitBoundaryBeta h) N := by
  intro N u hu hExists
  obtain ⟨h, hh⟩ := hExists
  exact ⟨h, mem_engelsmaFractionalTupleBox_of_unit_coordinate hu hh⟩

theorem preSievedSimplexUnitBoundary_subset_boxUnion
    {H : Finset ℕ} {alpha : ℝ} {N : ℕ} {u : H → ℕ}
    (hu : u ∈ preSievedSimplexTupleSupport H
      (engelsmaMaynardRadius alpha N)
      (engelsmaMaynardModulus N)) (hunit : ∃ h : H, u h = 1) :
    u ∈ engelsmaUnitBoundaryBoxUnion H alpha N := by
  obtain ⟨h, huh⟩ := preSievedSimplexUnitBoundary_subset_boxSumSupport
    N u hu hunit
  rw [engelsmaUnitBoundaryBoxUnion, Finset.mem_biUnion]
  exact ⟨h, Finset.mem_univ h,
    huh⟩

theorem engelsmaUnitBoundaryBoxUnionMass_le_sum
    (H : Finset ℕ) (alpha : ℝ) (N : ℕ) :
    engelsmaUnitBoundaryBoxUnionMass H alpha N ≤
      ∑ h : H, engelsmaFractionalTupleBoxMass H alpha
        (unitBoundaryBeta h) N := by
  unfold engelsmaUnitBoundaryBoxUnionMass engelsmaUnitBoundaryBoxUnion
    engelsmaFractionalTupleBoxMass
  apply sum_biUnion_le_sum_sum_of_nonneg
  intro u
  unfold reciprocalTotientTupleWeight
  positivity

theorem tendsto_normalizedEngelsmaUnitBoundaryBoxUnionMass_zero
    {H : Finset ℕ} {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (fun N : ℕ =>
      normalizedEngelsmaUnitBoundaryBoxUnionMass H alpha N)
      atTop (nhds 0) := by
  have henvelope := tendsto_normalizedEngelsmaUnitBoundaryBoxMassSum_zero
    (H := H) halpha
  have hR := tendsto_log_engelsmaMaynardRadius_atTop halpha
  have hnonneg : ∀ᶠ N : ℕ in atTop,
      0 ≤ normalizedEngelsmaUnitBoundaryBoxUnionMass H alpha N := by
    filter_upwards [hR.eventually (eventually_gt_atTop 0)] with N hlog
    unfold normalizedEngelsmaUnitBoundaryBoxUnionMass
      engelsmaUnitBoundaryBoxUnionMass
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro u hu
      unfold reciprocalTotientTupleWeight
      positivity
    · have hS := preSieveSingularSeries_pos (tripleLogCutoff (N - 1))
      positivity
  apply squeeze_zero' hnonneg ?_ henvelope
  filter_upwards [hR.eventually (eventually_gt_atTop 0)] with N hlog
  unfold normalizedEngelsmaUnitBoundaryBoxUnionMass
    normalizedEngelsmaUnitBoundaryBoxMassSum
    normalizedEngelsmaFractionalTupleBoxMass
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right
    (engelsmaUnitBoundaryBoxUnionMass_le_sum H alpha N)
  have hS := preSieveSingularSeries_pos (tripleLogCutoff (N - 1))
  positivity

end BoundedGaps.Maynard
