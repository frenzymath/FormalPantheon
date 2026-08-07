import BoundedGaps.Maynard.VariationalBridge
import BoundedGaps.Maynard.SmallKNumeratorBridge

/-!
# Conditional bridge for the small-k numerator

The numerator is reduced to ordered face-pair integrals.  The inner expansion
and the face-pair moment equalities are explicit hypotheses; the finite square
expansion and the sum over the 105 symmetric faces are kernel-checked here.
-/

namespace BoundedGaps.Maynard

open MeasureTheory Set
open scoped BigOperators

noncomputable section

noncomputable def smallKRealSupportedTerm (m : Fin 105) (i : Fin 42)
    (t : maynardFaceIndex 105 m → ℝ) (x : ℝ) : ℝ := by
  classical
  exact if maynardInsertCoordinate m x t ∈ maynardSimplex 105 then
    smallKRealTerm i (maynardInsertCoordinate m x t) else 0

theorem smallKRealSupportedTerm_measurable (m : Fin 105) (i : Fin 42)
    (t : maynardFaceIndex 105 m → ℝ) :
    Measurable (smallKRealSupportedTerm m i t) := by
  classical
  have hinsert : Measurable (fun x : ℝ => maynardInsertCoordinate m x t) := by
    rw [measurable_pi_iff]
    intro j
    by_cases hj : j = m
    · simp only [maynardInsertCoordinate, dif_pos hj]
      exact measurable_id
    · let jp : maynardFaceIndex 105 m := ⟨j, hj⟩
      simp [maynardInsertCoordinate, hj]
  unfold smallKRealSupportedTerm
  apply Measurable.ite
    ((maynardSimplex_measurable (k := 105)).preimage hinsert)
  · unfold smallKRealTerm smallKRealMonomial smallKRealP1 smallKRealP2
    fun_prop
  · exact measurable_const

theorem smallKRealSupportedTerm_norm_le (m : Fin 105) (i : Fin 42)
    (t : maynardFaceIndex 105 m → ℝ) (x : ℝ) :
    ‖smallKRealSupportedTerm m i t x‖ ≤ smallKRealTermBound i := by
  classical
  by_cases hs : maynardInsertCoordinate m x t ∈ maynardSimplex 105
  · simpa [smallKRealSupportedTerm, hs] using
      smallKRealTerm_norm_le i (maynardInsertCoordinate m x t) hs.1
  · simp [smallKRealSupportedTerm, hs, smallKRealTermBound_nonneg]

theorem smallKRealSupportedTerm_integrableOn (m : Fin 105) (i : Fin 42)
    (t : maynardFaceIndex 105 m → ℝ) :
    IntegrableOn (smallKRealSupportedTerm m i t) (Set.Icc 0 1) := by
  refine maynard_integrableOn_of_measurable_bounded
    (s := Set.Icc (0 : ℝ) 1) (hs := measurableSet_Icc)
    (hsfinite := measure_Icc_lt_top) (f := smallKRealSupportedTerm m i t)
    (smallKRealSupportedTerm_measurable m i t) (smallKRealTermBound i) ?_
  intro x hx
  exact smallKRealSupportedTerm_norm_le m i t x

noncomputable def smallKRealFaceInnerTerm (m : Fin 105) (i : Fin 42)
    (t : maynardFaceIndex 105 m → ℝ) : ℝ :=
  ∫ x in Set.Icc (0 : ℝ) 1, smallKRealSupportedTerm m i t x

def smallKRealFacePairTerm (m : Fin 105) (i j : Fin 42)
    (t : maynardFaceIndex 105 m → ℝ) : ℝ :=
  smallKRealFaceInnerTerm m i t * smallKRealFaceInnerTerm m j t

theorem smallKRealFaceInner_expansion_of_integrability
    (m : Fin 105) (t : maynardFaceIndex 105 m → ℝ)
    (hInt : ∀ i : Fin 42,
      IntegrableOn (smallKRealSupportedTerm m i t)
        (Set.Icc 0 1)) :
    (∫ x in Set.Icc (0 : ℝ) 1,
      smallKCandidate (maynardInsertCoordinate m x t)) =
      ∑ i : Fin 42, smallKRealFaceInnerTerm m i t := by
  classical
  have hpoint : (fun x : ℝ =>
      smallKCandidate (maynardInsertCoordinate m x t)) =
      (fun x : ℝ => ∑ i : Fin 42,
        smallKRealSupportedTerm m i t x) := by
    funext x
    by_cases hs : maynardInsertCoordinate m x t ∈ maynardSimplex 105
    · simp [smallKCandidate, smallKRealSupportedTerm, hs,
        smallKRealPolynomial_eq_sum_terms]
    · simp [smallKCandidate, smallKRealSupportedTerm, hs]
  rw [hpoint]
  have hsum :
      (∫ x, ∑ i : Fin 42,
        smallKRealSupportedTerm m i t x
        ∂volume.restrict (Set.Icc (0 : ℝ) 1)) =
        ∑ i : Fin 42, ∫ x, smallKRealSupportedTerm m i t x
          ∂volume.restrict (Set.Icc (0 : ℝ) 1) := by
    simpa using (integral_finsetSum
      (μ := volume.restrict (Set.Icc (0 : ℝ) 1)) (s := Finset.univ)
      (f := fun i x => smallKRealSupportedTerm m i t x)
      (fun i hi => (hInt i).integrable))
  rw [hsum]
  rfl

theorem smallKRealFaceInner_expansion (m : Fin 105)
    (t : maynardFaceIndex 105 m → ℝ) :
    (∫ x in Set.Icc (0 : ℝ) 1,
      smallKCandidate (maynardInsertCoordinate m x t)) =
      ∑ i : Fin 42, smallKRealFaceInnerTerm m i t := by
  exact smallKRealFaceInner_expansion_of_integrability m t
    (fun i => smallKRealSupportedTerm_integrableOn m i t)

noncomputable def smallKRealSupportedTermJoint (m : Fin 105) (i : Fin 42) :
    ((maynardFaceIndex 105 m → ℝ) × ℝ) → ℝ := fun z =>
  if z.2 ∈ Set.Icc (0 : ℝ) 1 then
    smallKRealSupportedTerm m i z.1 z.2 else 0

theorem smallKRealSupportedTermJoint_measurable (m : Fin 105) (i : Fin 42) :
    Measurable (smallKRealSupportedTermJoint m i) := by
  classical
  have hinsert : Measurable
      (fun z : (maynardFaceIndex 105 m → ℝ) × ℝ =>
        maynardInsertCoordinate m z.2 z.1) := by
    rw [measurable_pi_iff]
    intro j
    by_cases hj : j = m
    · simp only [maynardInsertCoordinate, dif_pos hj]
      exact measurable_snd
    · let jp : maynardFaceIndex 105 m := ⟨j, hj⟩
      simpa [maynardInsertCoordinate, hj, jp, Function.comp_def] using
        ((measurable_pi_apply jp).comp measurable_fst)
  unfold smallKRealSupportedTermJoint
  apply Measurable.ite (measurableSet_Icc.preimage measurable_snd)
  · unfold smallKRealSupportedTerm
    apply Measurable.ite
      ((maynardSimplex_measurable (k := 105)).preimage hinsert)
    · unfold smallKRealTerm smallKRealMonomial smallKRealP1 smallKRealP2
      fun_prop
    · exact measurable_const
  · exact measurable_const

theorem smallKRealFaceInnerTerm_measurable (m : Fin 105) (i : Fin 42) :
    Measurable (fun t : maynardFaceIndex 105 m → ℝ =>
      smallKRealFaceInnerTerm m i t) := by
  have hsm : StronglyMeasurable (fun t : maynardFaceIndex 105 m → ℝ =>
      ∫ x : ℝ, smallKRealSupportedTermJoint m i (t, x)) :=
    (smallKRealSupportedTermJoint_measurable m i).stronglyMeasurable
      |>.integral_prod_right'
  have hm : Measurable (fun t : maynardFaceIndex 105 m → ℝ =>
      ∫ x, smallKRealSupportedTermJoint m i (t, x)) := hsm.measurable
  convert hm using 1
  funext t
  simp only [smallKRealFaceInnerTerm, smallKRealSupportedTermJoint]
  rw [← integral_indicator measurableSet_Icc]
  congr 1
  funext x
  by_cases hx : x ∈ Set.Icc (0 : ℝ) 1 <;>
    simp [Set.indicator, smallKRealSupportedTerm, hx]

theorem smallKRealFaceInnerTerm_norm_le (m : Fin 105) (i : Fin 42)
    (t : maynardFaceIndex 105 m → ℝ) :
    ‖smallKRealFaceInnerTerm m i t‖ ≤ smallKRealTermBound i := by
  unfold smallKRealFaceInnerTerm
  calc
    ‖∫ x in Set.Icc (0 : ℝ) 1, smallKRealSupportedTerm m i t x‖ ≤
        smallKRealTermBound i * volume.real (Set.Icc (0 : ℝ) 1) :=
      norm_setIntegral_le_of_norm_le_const measure_Icc_lt_top
        (fun x _ => smallKRealSupportedTerm_norm_le m i t x)
    _ = smallKRealTermBound i := by rw [Real.volume_real_Icc_of_le] <;> norm_num

theorem smallKRealFacePairTerm_integrableOn (m : Fin 105) (i j : Fin 42) :
    IntegrableOn (smallKRealFacePairTerm m i j)
      (maynardCubeOf (maynardFaceIndex 105 m)) := by
  refine maynard_integrableOn_of_measurable_bounded
    (s := maynardCubeOf (maynardFaceIndex 105 m))
    (hs := MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Icc))
    (hsfinite := maynardCubeOf_measure_lt_top _)
    (f := smallKRealFacePairTerm m i j)
    ((smallKRealFaceInnerTerm_measurable m i).mul
      (smallKRealFaceInnerTerm_measurable m j))
    (smallKRealTermBound i * smallKRealTermBound j) ?_
  intro t ht
  unfold smallKRealFacePairTerm
  rw [norm_mul]
  exact mul_le_mul (smallKRealFaceInnerTerm_norm_le m i t)
    (smallKRealFaceInnerTerm_norm_le m j t)
    (norm_nonneg _) (smallKRealTermBound_nonneg i)

def smallKSourceFaceMoment (i j : Fin 42) : ℚ :=
  ∑ cp ∈ Finset.range (smallKExponentC i + 1),
    ∑ dp ∈ Finset.range (smallKExponentC j + 1),
      smallKFacePairTerm i j cp dp

theorem maynardJ_eq_face_pair_integral_sum (m : Fin 105) :
    maynardJ 105 m smallKCandidate =
      ∑ i : Fin 42, ∑ j : Fin 42,
        ∫ t in maynardCubeOf (maynardFaceIndex 105 m),
          smallKRealFacePairTerm m i j t := by
  unfold maynardJ
  simp_rw [smallKRealFaceInner_expansion m]
  simp only [pow_two]
  simp_rw [Finset.sum_mul_sum]
  change
    (∫ t, ∑ i : Fin 42, ∑ j : Fin 42,
      smallKRealFacePairTerm m i j t ∂volume.restrict
        (maynardCubeOf (maynardFaceIndex 105 m))) =
      ∑ i : Fin 42, ∑ j : Fin 42,
        (∫ t, smallKRealFacePairTerm m i j t ∂volume.restrict
          (maynardCubeOf (maynardFaceIndex 105 m)))
  have hInt' : ∀ i j : Fin 42,
      Integrable (smallKRealFacePairTerm m i j)
        (volume.restrict (maynardCubeOf (maynardFaceIndex 105 m))) := by
    intro i j
    exact (smallKRealFacePairTerm_integrableOn m i j).integrable
  have hInner : ∀ i : Fin 42,
      Integrable (fun t => ∑ j : Fin 42, smallKRealFacePairTerm m i j t)
        (volume.restrict (maynardCubeOf (maynardFaceIndex 105 m))) := by
    intro i
    exact integrable_finsetSum Finset.univ (fun j hj => hInt' i j)
  have hOuter :
      (∫ t, ∑ i : Fin 42, ∑ j : Fin 42,
        smallKRealFacePairTerm m i j t ∂volume.restrict
          (maynardCubeOf (maynardFaceIndex 105 m))) =
        ∑ i : Fin 42, ∫ t, ∑ j : Fin 42,
          smallKRealFacePairTerm m i j t ∂volume.restrict
            (maynardCubeOf (maynardFaceIndex 105 m)) := by
    simpa using (integral_finsetSum
      (μ := volume.restrict (maynardCubeOf (maynardFaceIndex 105 m)))
      (s := Finset.univ)
      (f := fun i t => ∑ j : Fin 42, smallKRealFacePairTerm m i j t)
      (fun i hi => hInner i))
  rw [hOuter]
  apply Finset.sum_congr rfl
  intro i hi
  simpa using (integral_finsetSum
    (μ := volume.restrict (maynardCubeOf (maynardFaceIndex 105 m)))
    (s := Finset.univ) (f := fun j t => smallKRealFacePairTerm m i j t)
    (fun j hj => hInt' i j))

theorem maynardNumerator_eq_face_pair_integral_sum :
    (∑ m : Fin 105, maynardJ 105 m smallKCandidate) =
      ∑ m : Fin 105, ∑ i : Fin 42, ∑ j : Fin 42,
        ∫ t in maynardCubeOf (maynardFaceIndex 105 m),
          smallKRealFacePairTerm m i j t := by
  apply Finset.sum_congr rfl
  intro m hm
  exact maynardJ_eq_face_pair_integral_sum m

theorem maynardNumerator_eq_smallKNumerator_of_face_moments
    (hMoment : ∀ i j : Fin 42,
      (∑ m : Fin 105,
        ∫ t in maynardCubeOf (maynardFaceIndex 105 m),
          smallKRealFacePairTerm m i j t) =
        ((105 * smallKCoefficient i * smallKCoefficient j *
          smallKSourceFaceMoment i j : ℚ) : ℝ)) :
    (∑ m : Fin 105, maynardJ 105 m smallKCandidate) =
      (smallKNumerator : ℝ) := by
  rw [maynardNumerator_eq_face_pair_integral_sum]
  calc
    (∑ m : Fin 105, ∑ i : Fin 42, ∑ j : Fin 42,
      ∫ t in maynardCubeOf (maynardFaceIndex 105 m),
        smallKRealFacePairTerm m i j t) =
      ∑ i : Fin 42, ∑ m : Fin 105, ∑ j : Fin 42,
        ∫ t in maynardCubeOf (maynardFaceIndex 105 m),
          smallKRealFacePairTerm m i j t := by
      rw [Finset.sum_comm]
    _ = ∑ i : Fin 42, ∑ j : Fin 42, ∑ m : Fin 105,
        ∫ t in maynardCubeOf (maynardFaceIndex 105 m),
          smallKRealFacePairTerm m i j t := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ i : Fin 42, ∑ j : Fin 42,
        ((105 * smallKCoefficient i * smallKCoefficient j *
          smallKSourceFaceMoment i j : ℚ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact hMoment i j
    _ = (smallKNumerator : ℝ) := by
      exact_mod_cast (show
        (∑ i : Fin 42, ∑ j : Fin 42,
          105 * smallKCoefficient i * smallKCoefficient j *
            (∑ cp ∈ Finset.range (smallKExponentC i + 1),
              ∑ dp ∈ Finset.range (smallKExponentC j + 1),
                smallKFacePairTerm i j cp dp)) = smallKNumerator by
        unfold smallKNumerator
        simp_rw [Finset.mul_sum]
        simp only [smallKFacePairTerm]
        ring_nf)

theorem maynardM_gt_four_of_simplex_moment_hypotheses
    (hbound : BddAbove (maynardRatioSet 105))
    (hDenMoment : ∀ i j : Fin 42,
      (∫ t in maynardSimplex 105, smallKRealPairTerm i j t) =
        ((smallKCoefficient i * smallKCoefficient j *
          smallKSimplexMoment
            (smallKExponentB i + smallKExponentB j)
            (smallKExponentC i + smallKExponentC j) : ℚ) : ℝ))
    (hNumMoment : ∀ i j : Fin 42,
      (∑ m : Fin 105,
        ∫ t in maynardCubeOf (maynardFaceIndex 105 m),
          smallKRealFacePairTerm m i j t) =
        ((105 * smallKCoefficient i * smallKCoefficient j *
          smallKSourceFaceMoment i j : ℚ) : ℝ)) :
    (4 : ℝ) < maynardM 105 := by
  have hI := maynardI_eq_smallKDenominator_of_pair_moments hDenMoment
  have hN := maynardNumerator_eq_smallKNumerator_of_face_moments hNumMoment
  exact maynardM_gt_four_of_smallKCandidate_of_functionals hbound hI hN

theorem maynardM_gt_four_of_face_moment_hypothesis
    (hbound : BddAbove (maynardRatioSet 105))
    (hNumMoment : ∀ i j : Fin 42,
      (∑ m : Fin 105,
        ∫ t in maynardCubeOf (maynardFaceIndex 105 m),
          smallKRealFacePairTerm m i j t) =
        ((105 * smallKCoefficient i * smallKCoefficient j *
          smallKSourceFaceMoment i j : ℚ) : ℝ)) :
    (4 : ℝ) < maynardM 105 := by
  exact maynardM_gt_four_of_simplex_moment_hypotheses hbound
    (fun i j => smallKRealPairTerm_moment i j) hNumMoment

end
end BoundedGaps.Maynard
