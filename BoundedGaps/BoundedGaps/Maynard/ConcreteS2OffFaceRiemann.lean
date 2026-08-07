import BoundedGaps.Maynard.ConcreteFiniteSimplexRiemann

noncomputable section

namespace BoundedGaps.Maynard

open Filter MeasureTheory Set
open scoped BigOperators

def engelsmaS2OffFaceMeasurableEquiv
    (m : BoundedGaps.engelsmaTuple) :
    (engelsmaOffFaceFinset m → ℝ) ≃ᵐ
      (maynardFaceIndex 105 (engelsmaIndexEquiv m) → ℝ) :=
  MeasurableEquiv.piCongrLeft
    (fun _ : maynardFaceIndex 105 (engelsmaIndexEquiv m) => ℝ)
    (engelsmaOffFaceIndexEquiv m)

@[simp] theorem engelsmaS2OffFaceMeasurableEquiv_apply_apply
    (m : BoundedGaps.engelsmaTuple)
    (t : engelsmaOffFaceFinset m → ℝ)
    (h : engelsmaOffFaceFinset m) :
    engelsmaS2OffFaceMeasurableEquiv m t
        (engelsmaOffFaceIndexEquiv m h) = t h := by
  exact MeasurableEquiv.piCongrLeft_apply_apply
    (β := fun _ : maynardFaceIndex 105 (engelsmaIndexEquiv m) => ℝ)
    (engelsmaOffFaceIndexEquiv m) t h

theorem engelsmaS2OffFaceMeasurableEquiv_apply
    (m : BoundedGaps.engelsmaTuple)
    (t : engelsmaOffFaceFinset m → ℝ)
    (j : maynardFaceIndex 105 (engelsmaIndexEquiv m)) :
    engelsmaS2OffFaceMeasurableEquiv m t j =
      t ((engelsmaOffFaceIndexEquiv m).symm j) := by
  obtain ⟨h, rfl⟩ := (engelsmaOffFaceIndexEquiv m).surjective j
  calc
    engelsmaS2OffFaceMeasurableEquiv m t
        (engelsmaOffFaceIndexEquiv m h) = t h :=
      engelsmaS2OffFaceMeasurableEquiv_apply_apply m t h
    _ = t ((engelsmaOffFaceIndexEquiv m).symm
        (engelsmaOffFaceIndexEquiv m h)) := by
      rw [(engelsmaOffFaceIndexEquiv m).symm_apply_apply]

theorem engelsmaS2OffFaceMeasurableEquiv_measurePreserving
    (m : BoundedGaps.engelsmaTuple) :
    MeasurePreserving (engelsmaS2OffFaceMeasurableEquiv m) volume volume :=
  volume_measurePreserving_piCongrLeft _ _

theorem engelsmaS2OffFaceMeasurableEquiv_sum
    (m : BoundedGaps.engelsmaTuple)
    (t : engelsmaOffFaceFinset m → ℝ) :
    (∑ j, engelsmaS2OffFaceMeasurableEquiv m t j) = ∑ h, t h := by
  rw [← (engelsmaOffFaceIndexEquiv m).sum_comp
    (engelsmaS2OffFaceMeasurableEquiv m t)]
  apply Finset.sum_congr rfl
  intro h hh
  exact engelsmaS2OffFaceMeasurableEquiv_apply_apply m t h

theorem engelsmaS2OffFaceMeasurableEquiv_sq_sum
    (m : BoundedGaps.engelsmaTuple)
    (t : engelsmaOffFaceFinset m → ℝ) :
    (∑ j, (engelsmaS2OffFaceMeasurableEquiv m t j) ^ 2) =
      ∑ h, (t h) ^ 2 := by
  rw [← (engelsmaOffFaceIndexEquiv m).sum_comp
    (fun j => (engelsmaS2OffFaceMeasurableEquiv m t j) ^ 2)]
  apply Finset.sum_congr rfl
  intro h hh
  rw [engelsmaS2OffFaceMeasurableEquiv_apply_apply]

theorem engelsmaS2OffFaceQuadraticIntegrand_eq
    (m : BoundedGaps.engelsmaTuple) (b c : ℕ)
    (t : engelsmaOffFaceFinset m → ℝ) :
    engelsmaS2OffFaceQuadraticIntegrand m b c t =
      (1 - ∑ h, t h) ^ b * (∑ h, (t h) ^ 2) ^ c := by
  unfold engelsmaS2OffFaceQuadraticIntegrand faceQuadraticIntegrand
  rw [show (fun j => t ((engelsmaOffFaceIndexEquiv m).symm j)) =
      engelsmaS2OffFaceMeasurableEquiv m t by
        funext j
        exact (engelsmaS2OffFaceMeasurableEquiv_apply m t j).symm,
    engelsmaS2OffFaceMeasurableEquiv_sum,
    engelsmaS2OffFaceMeasurableEquiv_sq_sum]

theorem abs_engelsmaS2OffFaceQuadraticIntegrand_le_one
    {m : BoundedGaps.engelsmaTuple} {b c : ℕ}
    {t : engelsmaOffFaceFinset m → ℝ}
    (ht : t ∈ finiteSimplexOf (engelsmaOffFaceFinset m)) :
    |engelsmaS2OffFaceQuadraticIntegrand m b c t| ≤ 1 := by
  have hcoord : ∀ h : engelsmaOffFaceFinset m,
      t h ∈ Set.Icc (0 : ℝ) 1 := by
    intro h
    exact ht.1 h (by simp)
  have hsumNonneg : 0 ≤ ∑ h, t h :=
    Finset.sum_nonneg (fun h hh => (hcoord h).1)
  have hslackNonneg : 0 ≤ 1 - ∑ h, t h := sub_nonneg.mpr ht.2
  have hslackLe : 1 - ∑ h, t h ≤ 1 := by linarith
  have hsqNonneg : 0 ≤ ∑ h, (t h) ^ 2 :=
    Finset.sum_nonneg (fun h hh => sq_nonneg (t h))
  have hsqLeSum : (∑ h, (t h) ^ 2) ≤ ∑ h, t h := by
    apply Finset.sum_le_sum
    intro h hh
    have hhData := hcoord h
    nlinarith [mul_nonneg hhData.1 (sub_nonneg.mpr hhData.2)]
  have hsqLe : (∑ h, (t h) ^ 2) ≤ 1 := hsqLeSum.trans ht.2
  have hslackPowNonneg : 0 ≤ (1 - ∑ h, t h) ^ b :=
    pow_nonneg hslackNonneg b
  have hsqPowNonneg : 0 ≤ (∑ h, (t h) ^ 2) ^ c :=
    pow_nonneg hsqNonneg c
  have hslackPowLe : (1 - ∑ h, t h) ^ b ≤ 1 :=
    pow_le_one₀ hslackNonneg hslackLe
  have hsqPowLe : (∑ h, (t h) ^ 2) ^ c ≤ 1 :=
    pow_le_one₀ hsqNonneg hsqLe
  rw [engelsmaS2OffFaceQuadraticIntegrand_eq,
    abs_of_nonneg (mul_nonneg hslackPowNonneg hsqPowNonneg)]
  nlinarith [mul_nonneg hslackPowNonneg hsqPowNonneg,
    mul_nonneg (sub_nonneg.mpr hslackPowLe)
      (sub_nonneg.mpr hsqPowLe)]

theorem engelsmaS2OffFaceMeasurableEquiv_mem_faceSimplex_iff
    (m : BoundedGaps.engelsmaTuple)
    (t : engelsmaOffFaceFinset m → ℝ) :
    engelsmaS2OffFaceMeasurableEquiv m t ∈
        maynardFaceSimplex (engelsmaIndexEquiv m) ↔
      t ∈ finiteSimplexOf (engelsmaOffFaceFinset m) := by
  constructor
  · intro ht
    constructor
    · rw [maynardCubeOf, Set.mem_pi]
      intro h hh
      have hnonneg : 0 ≤ t h := by
        have hh := ht.1 (engelsmaOffFaceIndexEquiv m h)
        rw [engelsmaS2OffFaceMeasurableEquiv_apply_apply] at hh
        exact hh
      have hsingle : t h ≤ ∑ i, t i :=
        Finset.single_le_sum (fun i hi => by
          have hi' := ht.1 (engelsmaOffFaceIndexEquiv m i)
          rw [engelsmaS2OffFaceMeasurableEquiv_apply_apply] at hi'
          exact hi') (by simp)
      have hsum : (∑ i, t i) ≤ 1 := by
        rw [← engelsmaS2OffFaceMeasurableEquiv_sum]
        exact ht.2
      exact ⟨hnonneg, hsingle.trans hsum⟩
    · rw [← engelsmaS2OffFaceMeasurableEquiv_sum]
      exact ht.2
  · intro ht
    constructor
    · intro j
      obtain ⟨h, rfl⟩ := (engelsmaOffFaceIndexEquiv m).surjective j
      have hh := (ht.1 h (by simp)).1
      rw [engelsmaS2OffFaceMeasurableEquiv_apply_apply]
      exact hh
    · rw [engelsmaS2OffFaceMeasurableEquiv_sum]
      exact ht.2

theorem engelsmaS2OffFace_setIntegral_reindex
    (m : BoundedGaps.engelsmaTuple) (b c : ℕ) :
    (∫ t in maynardFaceSimplex (engelsmaIndexEquiv m),
        faceQuadraticIntegrand (engelsmaIndexEquiv m) b c t) =
      ∫ u in finiteSimplexOf (engelsmaOffFaceFinset m),
        engelsmaS2OffFaceQuadraticIntegrand m b c u := by
  let e := engelsmaS2OffFaceMeasurableEquiv m
  have he := engelsmaS2OffFaceMeasurableEquiv_measurePreserving m
  let F := faceQuadraticIntegrand (engelsmaIndexEquiv m) b c
  calc
    (∫ t in maynardFaceSimplex (engelsmaIndexEquiv m), F t) =
        ∫ t, (maynardFaceSimplex (engelsmaIndexEquiv m)).indicator F t := by
      rw [integral_indicator
        (maynardFaceSimplex_measurable (engelsmaIndexEquiv m))]
    _ = ∫ u, (maynardFaceSimplex (engelsmaIndexEquiv m)).indicator F
        (e u) := by
      exact (he.integral_comp'
        ((maynardFaceSimplex (engelsmaIndexEquiv m)).indicator F)).symm
    _ = ∫ u, (finiteSimplexOf (engelsmaOffFaceFinset m)).indicator
        (engelsmaS2OffFaceQuadraticIntegrand m b c) u := by
      apply integral_congr_ae
      filter_upwards [] with u
      have hvalue : F (e u) =
          engelsmaS2OffFaceQuadraticIntegrand m b c u := by
        unfold F e engelsmaS2OffFaceQuadraticIntegrand
        apply congrArg (faceQuadraticIntegrand
          (engelsmaIndexEquiv m) b c)
        funext j
        exact engelsmaS2OffFaceMeasurableEquiv_apply m u j
      by_cases hu : u ∈ finiteSimplexOf (engelsmaOffFaceFinset m)
      · rw [Set.indicator_of_mem hu,
          Set.indicator_of_mem
            ((engelsmaS2OffFaceMeasurableEquiv_mem_faceSimplex_iff m u).2 hu),
          hvalue]
      · rw [Set.indicator_of_notMem hu,
          Set.indicator_of_notMem
            ((engelsmaS2OffFaceMeasurableEquiv_mem_faceSimplex_iff m u).not.mpr hu)]
    _ = ∫ u in finiteSimplexOf (engelsmaOffFaceFinset m),
        engelsmaS2OffFaceQuadraticIntegrand m b c u := by
      rw [integral_indicator (isCompact_finiteSimplexOf
        (engelsmaOffFaceFinset m)).measurableSet]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1200000 in
theorem tendsto_engelsmaS2OffFaceRiemannStep
    (m : BoundedGaps.engelsmaTuple) (b c : ℕ) :
    Tendsto (fun mesh : ℕ =>
      ∑ j ∈ fractionalSimplexInnerGridIndex
          (engelsmaOffFaceFinset m) mesh,
        engelsmaS2OffFaceQuadraticIntegrand m b c
            (fractionalGridLower mesh j) *
          ∏ h : engelsmaOffFaceFinset m,
            (fractionalGridUpper mesh j h -
              fractionalGridLower mesh j h))
      atTop (nhds (∫ t in maynardFaceSimplex (engelsmaIndexEquiv m),
        faceQuadraticIntegrand (engelsmaIndexEquiv m) b c t)) := by
  obtain ⟨h, hh⟩ := engelsmaOffFaceFinset_nonempty m
  have hlim := tendsto_finiteSimplexInnerGridWeightedSum
    (⟨h, hh⟩ : engelsmaOffFaceFinset m)
    (continuous_engelsmaS2OffFaceQuadraticIntegrand m b c)
    (fun t ht => abs_engelsmaS2OffFaceQuadraticIntegrand_le_one ht)
  rw [← engelsmaS2OffFace_setIntegral_reindex m b c] at hlim
  simpa [finiteSimplexInnerGridWeightedSum] using hlim

end BoundedGaps.Maynard
