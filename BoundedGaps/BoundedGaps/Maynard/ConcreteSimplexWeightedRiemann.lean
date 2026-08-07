import BoundedGaps.Maynard.ConcreteSimplexGeometricGrid

noncomputable section
namespace BoundedGaps.Maynard

open Filter MeasureTheory Set
open scoped BigOperators

def simplexInnerGridQuadraticWeightedSum (m b c : ℕ) : ℝ :=
  ∑ j ∈ fractionalSimplexInnerGridIndex BoundedGaps.engelsmaTuple m,
    simplexQuadraticIntegrand 105 b c (engelsmaGridLowerPoint m j) *
      ∏ h : BoundedGaps.engelsmaTuple,
        (fractionalGridUpper m j h - fractionalGridLower m j h)

theorem measurableSet_engelsmaGridCellUnion
    (I : Finset (BoundedGaps.engelsmaTuple → ℕ)) (m : ℕ) :
    MeasurableSet (engelsmaGridCellUnion I m) := by
  unfold engelsmaGridCellUnion
  apply MeasurableSet.iUnion
  intro j
  apply MeasurableSet.iUnion
  intro hj
  exact measurableSet_engelsmaGridCell m j

set_option maxRecDepth 10000 in
theorem engelsmaInnerGridCellUnion_subset_maynardSimplex
    {m : ℕ} (hm : 0 < m) :
    engelsmaGridCellUnion
        (fractionalSimplexInnerGridIndex BoundedGaps.engelsmaTuple m) m ⊆
      maynardSimplex 105 := by
  intro x hx
  rw [engelsmaGridCellUnion, Set.mem_iUnion] at hx
  obtain ⟨j, hxj⟩ := hx
  rw [Set.mem_iUnion] at hxj
  obtain ⟨hj, hxCell⟩ := hxj
  exact engelsmaGridCell_subset_maynardSimplex_of_inner hm hj hxCell

set_option maxRecDepth 10000 in
theorem eventually_innerGridCell_quadratic_oscillation (b c : ℕ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ m : ℕ in atTop, ∀ j ∈
        fractionalSimplexInnerGridIndex BoundedGaps.engelsmaTuple m,
      ∀ x ∈ engelsmaGridCell m j,
        |simplexQuadraticIntegrand 105 b c x -
          simplexQuadraticIntegrand 105 b c
            (engelsmaGridLowerPoint m j)| < epsilon := by
  have huc := uniformContinuousOn_simplexQuadraticIntegrand_cube 105 b c
  obtain ⟨delta, hdelta, hcontrol⟩ :=
    (Metric.uniformContinuousOn_iff.mp huc) epsilon hepsilon
  have hmeshT : Tendsto (fun m : ℕ => (1 : ℝ) / m) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
  have hmesh := hmeshT.eventually (Iio_mem_nhds hdelta)
  filter_upwards [hmesh, eventually_ge_atTop 1] with m hmeshM hm j hj x hx
  have hmPos : 0 < m := by omega
  have hxSimplex := engelsmaGridCell_subset_maynardSimplex_of_inner hmPos hj hx
  have hxCube : x ∈ maynardCube 105 := hxSimplex.1
  have hlowerCube := engelsmaGridLowerPoint_mem_cube hmPos
    (Finset.mem_filter.mp hj).1
  have hdist : dist x (engelsmaGridLowerPoint m j) < delta := by
    apply (dist_pi_lt_iff hdelta).mpr
    intro i
    apply lt_trans ?_ hmeshM
    have hxi := (Set.mem_univ_pi.mp hx) i
    have hwidth := fractionalGridUpper_eq_lower_add_inv hmPos j
      (engelsmaIndexEquiv.symm i)
    simp only [engelsmaGridLowerPoint,
      engelsmaGridUpperPoint, Real.dist_eq] at hxi ⊢
    rw [hwidth] at hxi
    have hnonneg : 0 ≤ x i -
        fractionalGridLower m j (engelsmaIndexEquiv.symm i) :=
      sub_nonneg.mpr hxi.1
    have hlt : x i -
        fractionalGridLower m j (engelsmaIndexEquiv.symm i) < 1 / m := by
      linarith [hxi.2]
    rw [abs_of_nonneg hnonneg]
    exact hlt
  have hout := hcontrol _ hxCube _ hlowerCube hdist
  simpa [Real.dist_eq] using hout

set_option maxRecDepth 10000 in
theorem simplexInnerGridQuadraticWeightedSum_sub_integral_bound
    {m : ℕ} (hm : 0 < m) (b c : ℕ) {epsilon : ℝ}
    (_hepsilon : 0 ≤ epsilon)
    (hosc : ∀ j ∈ fractionalSimplexInnerGridIndex
        BoundedGaps.engelsmaTuple m,
      ∀ x ∈ engelsmaGridCell m j,
        |simplexQuadraticIntegrand 105 b c x -
          simplexQuadraticIntegrand 105 b c
            (engelsmaGridLowerPoint m j)| ≤ epsilon) :
    |simplexInnerGridQuadraticWeightedSum m b c -
        ∫ x in engelsmaGridCellUnion
          (fractionalSimplexInnerGridIndex BoundedGaps.engelsmaTuple m) m,
          simplexQuadraticIntegrand 105 b c x| ≤
      epsilon * simplexInnerGridVolume BoundedGaps.engelsmaTuple m := by
  let I := fractionalSimplexInnerGridIndex BoundedGaps.engelsmaTuple m
  have hIGrid : I ⊆ fractionalGridIndex BoundedGaps.engelsmaTuple m := by
    intro j hj
    exact (Finset.mem_filter.mp hj).1
  have hd : (I : Set (BoundedGaps.engelsmaTuple → ℕ)).PairwiseDisjoint
      (engelsmaGridCell m) :=
    Set.Pairwise.mono (by exact_mod_cast hIGrid)
      (pairwiseDisjoint_engelsmaGridCell hm)
  have hcellSubset : ∀ j ∈ I, engelsmaGridCell m j ⊆ maynardSimplex 105 := by
    intro j hj
    exact engelsmaGridCell_subset_maynardSimplex_of_inner hm hj
  have hfCell : ∀ j ∈ I, IntegrableOn
      (simplexQuadraticIntegrand 105 b c) (engelsmaGridCell m j) := by
    intro j hj
    exact (simplexQuadratic_integrableOn 105 b c).mono_set (hcellSubset j hj)
  have hIntegralUnion :
      (∫ x in engelsmaGridCellUnion I m,
        simplexQuadraticIntegrand 105 b c x) =
      ∑ j ∈ I, ∫ x in engelsmaGridCell m j,
        simplexQuadraticIntegrand 105 b c x := by
    unfold engelsmaGridCellUnion
    exact integral_biUnion_finset I
      (fun j hj => measurableSet_engelsmaGridCell m j) hd hfCell
  rw [hIntegralUnion]
  unfold simplexInnerGridQuadraticWeightedSum simplexInnerGridVolume
  change |(∑ j ∈ I, simplexQuadraticIntegrand 105 b c
      (engelsmaGridLowerPoint m j) *
        ∏ h : BoundedGaps.engelsmaTuple,
          (fractionalGridUpper m j h - fractionalGridLower m j h)) -
      ∑ j ∈ I, ∫ x in engelsmaGridCell m j,
        simplexQuadraticIntegrand 105 b c x| ≤
    epsilon * ∑ j ∈ I, ∏ h : BoundedGaps.engelsmaTuple,
      (fractionalGridUpper m j h - fractionalGridLower m j h)
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ I, |simplexQuadraticIntegrand 105 b c
          (engelsmaGridLowerPoint m j) *
            ∏ h : BoundedGaps.engelsmaTuple,
              (fractionalGridUpper m j h - fractionalGridLower m j h) -
          ∫ x in engelsmaGridCell m j,
            simplexQuadraticIntegrand 105 b c x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ I, epsilon *
          ∏ h : BoundedGaps.engelsmaTuple,
            (fractionalGridUpper m j h - fractionalGridLower m j h) := by
      apply Finset.sum_le_sum
      intro j hj
      have hfinite : volume (engelsmaGridCell m j) ≠ ⊤ := by
        rw [engelsmaGridCell, Real.volume_pi_Ico]
        apply ENNReal.prod_ne_top
        intro i hi
        exact ENNReal.ofReal_ne_top
      have hconst : IntegrableOn
          (fun _x : Fin 105 → ℝ =>
            simplexQuadraticIntegrand 105 b c (engelsmaGridLowerPoint m j))
          (engelsmaGridCell m j) :=
        integrableOn_const hfinite (hC := by simp)
      have hdiff :
          (∫ x in engelsmaGridCell m j,
              (simplexQuadraticIntegrand 105 b c (engelsmaGridLowerPoint m j) -
                simplexQuadraticIntegrand 105 b c x)) =
            simplexQuadraticIntegrand 105 b c (engelsmaGridLowerPoint m j) *
                ∏ h : BoundedGaps.engelsmaTuple,
                  (fractionalGridUpper m j h - fractionalGridLower m j h) -
              ∫ x in engelsmaGridCell m j,
                simplexQuadraticIntegrand 105 b c x := by
        rw [integral_sub hconst (hfCell j hj), setIntegral_const,
          MeasureTheory.measureReal_def, volume_engelsmaGridCell_toReal hm]
        simp only [smul_eq_mul]
        ring
      rw [← hdiff]
      have hbound := norm_setIntegral_le_of_norm_le_const
        (f := fun x : Fin 105 → ℝ =>
          simplexQuadraticIntegrand 105 b c (engelsmaGridLowerPoint m j) -
            simplexQuadraticIntegrand 105 b c x)
        (C := epsilon)
        (show volume (engelsmaGridCell m j) < ⊤ from lt_top_iff_ne_top.mpr hfinite)
        (fun x hx => by
          simpa only [Real.norm_eq_abs, abs_sub_comm] using hosc j hj x hx)
      rw [MeasureTheory.measureReal_def, volume_engelsmaGridCell_toReal hm] at hbound
      simpa only [Real.norm_eq_abs] using hbound
    _ = _ := by rw [Finset.mul_sum]

set_option maxRecDepth 10000 in
theorem engelsmaGridCell_subset_cube_of_grid
    {m : ℕ} (hm : 0 < m)
    {j : BoundedGaps.engelsmaTuple → ℕ}
    (hj : j ∈ fractionalGridIndex BoundedGaps.engelsmaTuple m) :
    engelsmaGridCell m j ⊆ maynardCube 105 := by
  intro x hx
  rw [maynardCube, maynardCubeOf, Set.mem_pi]
  intro i hi
  have hxi := (Set.mem_univ_pi.mp hx) i
  have hend := fractionalGridEndpoints_mem_Icc hm hj
    (engelsmaIndexEquiv.symm i)
  exact ⟨hend.1.1.trans hxi.1, hxi.2.le.trans hend.2.1.2⟩

set_option maxRecDepth 10000 in
theorem engelsmaBoundaryGridCellUnion_subset_cube
    {m : ℕ} (hm : 0 < m) :
    engelsmaGridCellUnion
        (fractionalSimplexBoundaryGridIndex BoundedGaps.engelsmaTuple m) m ⊆
      maynardCube 105 := by
  intro x hx
  rw [engelsmaGridCellUnion, Set.mem_iUnion] at hx
  obtain ⟨j, hxj⟩ := hx
  rw [Set.mem_iUnion] at hxj
  obtain ⟨hj, hxCell⟩ := hxj
  exact engelsmaGridCell_subset_cube_of_grid hm
    (Finset.mem_filter.mp hj).1 hxCell

set_option maxRecDepth 10000 in
theorem simplexInnerGridVolume_le_one {m : ℕ} (hm : 0 < m) :
    simplexInnerGridVolume BoundedGaps.engelsmaTuple m ≤ 1 := by
  let I := fractionalSimplexInnerGridIndex BoundedGaps.engelsmaTuple m
  have hIGrid : I ⊆ fractionalGridIndex BoundedGaps.engelsmaTuple m := by
    intro j hj
    exact (Finset.mem_filter.mp hj).1
  have hvolume := volume_engelsmaGridCellUnion_toReal hm hIGrid
  have hsubset := engelsmaInnerGridCellUnion_subset_maynardSimplex hm
  have hcube : maynardSimplex 105 ⊆ maynardCube 105 := fun x hx => hx.1
  have hmono : (volume (engelsmaGridCellUnion I m)).toReal ≤
      (volume (maynardCube 105)).toReal := by
    exact measureReal_mono (hsubset.trans hcube)
      (maynardCube_measure_lt_top 105).ne
  have hcubeVolume : (volume (maynardCube 105)).toReal = 1 := by
    unfold maynardCube maynardCubeOf
    rw [MeasureTheory.volume_pi_pi]
    simp [Real.volume_Icc]
  rw [hvolume, hcubeVolume] at hmono
  simpa [I, simplexInnerGridVolume] using hmono

set_option maxRecDepth 10000 in
theorem simplexQuadratic_remainder_integral_bound
    {m : ℕ} (hm : 0 < m) (b c : ℕ) :
    |∫ x in maynardSimplex 105 \
        engelsmaGridCellUnion
          (fractionalSimplexInnerGridIndex BoundedGaps.engelsmaTuple m) m,
        simplexQuadraticIntegrand 105 b c x| ≤
      simplexBoundaryGridVolume BoundedGaps.engelsmaTuple m := by
  let A := engelsmaGridCellUnion
    (fractionalSimplexInnerGridIndex BoundedGaps.engelsmaTuple m) m
  let B := engelsmaGridCellUnion
    (fractionalSimplexBoundaryGridIndex BoundedGaps.engelsmaTuple m) m
  let E := engelsmaCoordinateOneFaces ∩ maynardSimplex 105
  let R := maynardSimplex 105 \ A
  have hRsubset : R ⊆ B ∪ E := by
    intro x hx
    have hcover := maynardSimplex_subset_inner_boundary_faces m hm hx.1
    rcases hcover with hxAB | hxFace
    · rcases hxAB with hxA | hxB
      · exact False.elim (hx.2 hxA)
      · exact Or.inl hxB
    · exact Or.inr ⟨hxFace, hx.1⟩
  have hBsubset : B ⊆ maynardCube 105 :=
    engelsmaBoundaryGridCellUnion_subset_cube hm
  have hEsubset : E ⊆ maynardCube 105 := fun x hx => hx.2.1
  have hUsubset : B ∪ E ⊆ maynardCube 105 :=
    Set.union_subset hBsubset hEsubset
  have hRfinite : volume R < ⊤ :=
    lt_of_le_of_lt (measure_mono (hRsubset.trans hUsubset))
      (maynardCube_measure_lt_top 105)
  have hnorm : |∫ x in R, simplexQuadraticIntegrand 105 b c x| ≤
      (volume R).toReal := by
    have hbound := norm_setIntegral_le_of_norm_le_const
      (f := simplexQuadraticIntegrand 105 b c) (C := (1 : ℝ))
      hRfinite (fun x hx => by
        rw [Real.norm_eq_abs]
        exact abs_simplexQuadraticIntegrand_le_one hx.1)
    simpa only [Real.norm_eq_abs, one_mul, MeasureTheory.measureReal_def] using hbound
  have hUfinite : volume (B ∪ E) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono hUsubset)
      (maynardCube_measure_lt_top 105))
  have hmeasureMono : (volume R).toReal ≤ (volume (B ∪ E)).toReal := by
    exact measureReal_mono hRsubset hUfinite
  have hEzero : volume E = 0 :=
    measure_mono_null Set.inter_subset_left volume_engelsmaCoordinateOneFaces
  have hUnionBound : (volume (B ∪ E)).toReal ≤ (volume B).toReal := by
    rw [← MeasureTheory.measureReal_def, ← MeasureTheory.measureReal_def]
    calc
      volume.real (B ∪ E) ≤ volume.real B + volume.real E :=
        measureReal_union_le B E
      _ = volume.real B := by simp [MeasureTheory.measureReal_def, hEzero]
  have hBGrid : fractionalSimplexBoundaryGridIndex
      BoundedGaps.engelsmaTuple m ⊆
      fractionalGridIndex BoundedGaps.engelsmaTuple m := by
    intro j hj
    exact (Finset.mem_filter.mp hj).1
  have hBvolume := volume_engelsmaGridCellUnion_toReal hm hBGrid
  change |∫ x in R, simplexQuadraticIntegrand 105 b c x| ≤ _
  calc
    _ ≤ (volume R).toReal := hnorm
    _ ≤ (volume (B ∪ E)).toReal := hmeasureMono
    _ ≤ (volume B).toReal := hUnionBound
    _ = _ := by simpa [B, simplexBoundaryGridVolume] using hBvolume

set_option maxRecDepth 10000 in
theorem tendsto_simplexInnerGridQuadraticWeightedSum (b c : ℕ) :
    Tendsto (fun m : ℕ => simplexInnerGridQuadraticWeightedSum m b c)
      atTop (nhds (∫ x in maynardSimplex 105,
        simplexQuadraticIntegrand 105 b c x)) := by
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  have hhalf : 0 < epsilon / 2 := by linarith
  have hosc := eventually_innerGridCell_quadratic_oscillation b c hhalf
  let h0 : BoundedGaps.engelsmaTuple :=
    ⟨0, BoundedGaps.engelsmaTuple_mem_zero⟩
  have hboundaryT := tendsto_simplexBoundaryGridVolume_zero h0
  have hboundary := hboundaryT.eventually (Iio_mem_nhds hhalf)
  filter_upwards [hosc, hboundary, eventually_ge_atTop 1] with
      m hoscM hboundaryM hm
  have hmPos : 0 < m := by omega
  let A := engelsmaGridCellUnion
    (fractionalSimplexInnerGridIndex BoundedGaps.engelsmaTuple m) m
  have hinner := simplexInnerGridQuadraticWeightedSum_sub_integral_bound
    hmPos b c hhalf.le (fun j hj x hx => (hoscM j hj x hx).le)
  have hvolume := simplexInnerGridVolume_le_one hmPos
  have hinnerHalf : |simplexInnerGridQuadraticWeightedSum m b c -
      ∫ x in A, simplexQuadraticIntegrand 105 b c x| ≤ epsilon / 2 := by
    exact hinner.trans (mul_le_of_le_one_right hhalf.le hvolume)
  have hrem := simplexQuadratic_remainder_integral_bound hmPos b c
  have hremHalf : |∫ x in maynardSimplex 105 \ A,
      simplexQuadraticIntegrand 105 b c x| < epsilon / 2 :=
    lt_of_le_of_lt hrem hboundaryM
  have hAmeas : MeasurableSet A :=
    measurableSet_engelsmaGridCellUnion _ _
  have hAsub : A ⊆ maynardSimplex 105 :=
    engelsmaInnerGridCellUnion_subset_maynardSimplex hmPos
  have hsplit := setIntegral_sdiff hAmeas
    (simplexQuadratic_integrableOn 105 b c) hAsub
  rw [Real.dist_eq]
  calc
    |simplexInnerGridQuadraticWeightedSum m b c -
        ∫ x in maynardSimplex 105, simplexQuadraticIntegrand 105 b c x| =
      |(simplexInnerGridQuadraticWeightedSum m b c -
          ∫ x in A, simplexQuadraticIntegrand 105 b c x) -
        ∫ x in maynardSimplex 105 \ A,
          simplexQuadraticIntegrand 105 b c x| := by rw [hsplit]; ring_nf
    _ ≤ |simplexInnerGridQuadraticWeightedSum m b c -
          ∫ x in A, simplexQuadraticIntegrand 105 b c x| +
        |∫ x in maynardSimplex 105 \ A,
          simplexQuadraticIntegrand 105 b c x| := abs_sub _ _
    _ < epsilon := by linarith

end BoundedGaps.Maynard
