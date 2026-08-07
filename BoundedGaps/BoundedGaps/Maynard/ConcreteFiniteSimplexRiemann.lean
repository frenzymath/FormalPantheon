import BoundedGaps.Maynard.ConcreteFiniteSimplexGeometricGrid

noncomputable section

namespace BoundedGaps.Maynard

open Filter MeasureTheory Set
open scoped BigOperators

def finiteSimplexInnerGridWeightedSum {H : Finset ℕ}
    (f : (H → ℝ) → ℝ) (mesh : ℕ) : ℝ :=
  ∑ j ∈ fractionalSimplexInnerGridIndex H mesh,
    f (fractionalGridLower mesh j) *
      ∏ h : H, (fractionalGridUpper mesh j h -
        fractionalGridLower mesh j h)

theorem isCompact_finiteSimplexOf (H : Finset ℕ) :
    IsCompact (finiteSimplexOf H) := by
  have hcube : IsCompact (maynardCubeOf H) := by
    unfold maynardCubeOf
    exact isCompact_univ_pi (fun _ => isCompact_Icc)
  have hsum : Continuous (fun t : H → ℝ => ∑ h : H, t h) := by
    fun_prop
  have hclosed : IsClosed {t : H → ℝ | ∑ h : H, t h ≤ 1} :=
    isClosed_le hsum continuous_const
  change IsCompact (maynardCubeOf H ∩ {t : H → ℝ | ∑ h : H, t h ≤ 1})
  exact hcube.inter_right hclosed

theorem volume_maynardCubeOf (H : Finset ℕ) :
    volume (maynardCubeOf H) = 1 := by
  unfold maynardCubeOf
  rw [MeasureTheory.volume_pi_pi]
  simp [Real.volume_Icc]

set_option maxRecDepth 8000 in
theorem eventually_fractionalGridCell_oscillation
    {H : Finset ℕ} {f : (H → ℝ) → ℝ} (hf : Continuous f)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ mesh : ℕ in atTop,
      ∀ j ∈ fractionalSimplexInnerGridIndex H mesh,
      ∀ x ∈ fractionalGridCell mesh j,
        |f x - f (fractionalGridLower mesh j)| < epsilon := by
  have hcompact : IsCompact (maynardCubeOf H) := by
    unfold maynardCubeOf
    exact isCompact_univ_pi (fun _ => isCompact_Icc)
  have huc : UniformContinuousOn f (maynardCubeOf H) :=
    hcompact.uniformContinuousOn_of_continuous hf.continuousOn
  obtain ⟨delta, hdelta, hcontrol⟩ :=
    (Metric.uniformContinuousOn_iff.mp huc) epsilon hepsilon
  have hmeshT : Tendsto (fun mesh : ℕ => (1 : ℝ) / mesh)
      atTop (nhds 0) := tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
  have hmesh := hmeshT.eventually (Iio_mem_nhds hdelta)
  filter_upwards [hmesh, eventually_ge_atTop 1] with
      mesh hmeshN hmeshOne j hj x hx
  have hmeshPos : 0 < mesh := by omega
  have hxSimplex := fractionalGridCell_subset_finiteSimplexOf_inner
    hmeshPos hj hx
  have hlowerCube : fractionalGridLower mesh j ∈ maynardCubeOf H := by
    rw [maynardCubeOf, Set.mem_pi]
    intro h hh
    exact (fractionalSimplexInnerGridIndex_data hmeshPos hj).1 h |>.1
  have hdist : dist x (fractionalGridLower mesh j) < delta := by
    apply (dist_pi_lt_iff hdelta).mpr
    intro h
    apply lt_trans ?_ hmeshN
    have hxh := (Set.mem_univ_pi.mp hx) h
    have hwidth := fractionalGridUpper_eq_lower_add_inv hmeshPos j h
    rw [hwidth] at hxh
    simp only [Real.dist_eq]
    have hnonneg : 0 ≤ x h - fractionalGridLower mesh j h :=
      sub_nonneg.mpr hxh.1
    rw [abs_of_nonneg hnonneg]
    linarith [hxh.2]
  have hout := hcontrol _ hxSimplex.1 _ hlowerCube hdist
  simpa [Real.dist_eq] using hout

set_option maxRecDepth 8000 in
theorem finiteSimplexInnerGridWeightedSum_sub_integral_bound
    {H : Finset ℕ} {f : (H → ℝ) → ℝ} (hf : Continuous f)
    {mesh : ℕ} (hmesh : 0 < mesh) {epsilon : ℝ}
    (_hepsilon : 0 ≤ epsilon)
    (hosc : ∀ j ∈ fractionalSimplexInnerGridIndex H mesh,
      ∀ x ∈ fractionalGridCell mesh j,
        |f x - f (fractionalGridLower mesh j)| ≤ epsilon) :
    |finiteSimplexInnerGridWeightedSum f mesh -
        ∫ x in fractionalGridCellUnion
          (fractionalSimplexInnerGridIndex H mesh) mesh, f x| ≤
      epsilon * simplexInnerGridVolume H mesh := by
  let I := fractionalSimplexInnerGridIndex H mesh
  have hIGrid : I ⊆ fractionalGridIndex H mesh := by
    intro j hj
    exact (Finset.mem_filter.mp hj).1
  have hd : (I : Set (H → ℕ)).PairwiseDisjoint
      (fractionalGridCell mesh) :=
    Set.Pairwise.mono (by exact_mod_cast hIGrid)
      (pairwiseDisjoint_fractionalGridCell hmesh)
  have hcellSubset : ∀ j ∈ I,
      fractionalGridCell mesh j ⊆ finiteSimplexOf H := by
    intro j hj
    exact fractionalGridCell_subset_finiteSimplexOf_inner hmesh hj
  have hfCell : ∀ j ∈ I, IntegrableOn f (fractionalGridCell mesh j) := by
    intro j hj
    exact (hf.continuousOn.integrableOn_compact
      (isCompact_finiteSimplexOf H)).mono_set (hcellSubset j hj)
  have hIntegralUnion :
      (∫ x in fractionalGridCellUnion I mesh, f x) =
        ∑ j ∈ I, ∫ x in fractionalGridCell mesh j, f x := by
    unfold fractionalGridCellUnion
    exact integral_biUnion_finset I
      (fun j hj => measurableSet_fractionalGridCell mesh j) hd hfCell
  rw [hIntegralUnion]
  unfold finiteSimplexInnerGridWeightedSum simplexInnerGridVolume
  change |(∑ j ∈ I, f (fractionalGridLower mesh j) *
      ∏ h : H, (fractionalGridUpper mesh j h -
        fractionalGridLower mesh j h)) -
      ∑ j ∈ I, ∫ x in fractionalGridCell mesh j, f x| ≤
    epsilon * ∑ j ∈ I, ∏ h : H,
      (fractionalGridUpper mesh j h - fractionalGridLower mesh j h)
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ I, |f (fractionalGridLower mesh j) *
          ∏ h : H, (fractionalGridUpper mesh j h -
            fractionalGridLower mesh j h) -
        ∫ x in fractionalGridCell mesh j, f x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ I, epsilon * ∏ h : H,
          (fractionalGridUpper mesh j h -
            fractionalGridLower mesh j h) := by
      apply Finset.sum_le_sum
      intro j hj
      have hfinite : volume (fractionalGridCell mesh j) ≠ ⊤ := by
        rw [fractionalGridCell, Real.volume_pi_Ico]
        apply ENNReal.prod_ne_top
        intro h hh
        exact ENNReal.ofReal_ne_top
      have hconst : IntegrableOn
          (fun _x : H → ℝ => f (fractionalGridLower mesh j))
          (fractionalGridCell mesh j) :=
        integrableOn_const hfinite (hC := by simp)
      have hdiff :
          (∫ x in fractionalGridCell mesh j,
              (f (fractionalGridLower mesh j) - f x)) =
            f (fractionalGridLower mesh j) *
                ∏ h : H, (fractionalGridUpper mesh j h -
                  fractionalGridLower mesh j h) -
              ∫ x in fractionalGridCell mesh j, f x := by
        rw [integral_sub hconst (hfCell j hj), setIntegral_const,
          MeasureTheory.measureReal_def,
          volume_fractionalGridCell_toReal hmesh]
        simp only [smul_eq_mul]
        ring
      rw [← hdiff]
      have hbound := norm_setIntegral_le_of_norm_le_const
        (f := fun x : H → ℝ => f (fractionalGridLower mesh j) - f x)
        (C := epsilon)
        (show volume (fractionalGridCell mesh j) < ⊤ from
          lt_top_iff_ne_top.mpr hfinite)
        (fun x hx => by
          simpa only [Real.norm_eq_abs, abs_sub_comm] using hosc j hj x hx)
      rw [MeasureTheory.measureReal_def,
        volume_fractionalGridCell_toReal hmesh] at hbound
      simpa only [Real.norm_eq_abs] using hbound
    _ = _ := by rw [Finset.mul_sum]

theorem simplexInnerGridVolume_le_one_finite
    {H : Finset ℕ} {mesh : ℕ} (hmesh : 0 < mesh) :
    simplexInnerGridVolume H mesh ≤ 1 := by
  let I := fractionalSimplexInnerGridIndex H mesh
  have hIGrid : I ⊆ fractionalGridIndex H mesh := by
    intro j hj
    exact (Finset.mem_filter.mp hj).1
  have hvolume := volume_fractionalGridCellUnion_toReal hmesh hIGrid
  have hsubset : fractionalGridCellUnion I mesh ⊆ finiteSimplexOf H := by
    intro x hx
    rw [fractionalGridCellUnion, Set.mem_iUnion] at hx
    obtain ⟨j, hxj⟩ := hx
    rw [Set.mem_iUnion] at hxj
    obtain ⟨hj, hxCell⟩ := hxj
    exact fractionalGridCell_subset_finiteSimplexOf_inner hmesh hj hxCell
  have hmono : (volume (fractionalGridCellUnion I mesh)).toReal ≤ 1 := by
    calc
      _ ≤ (volume (maynardCubeOf H)).toReal :=
        measureReal_mono (hsubset.trans (fun x hx => hx.1))
          (maynardCubeOf_measure_lt_top H).ne
      _ = 1 := by rw [volume_maynardCubeOf]; simp
  rw [hvolume] at hmono
  simpa [I, simplexInnerGridVolume] using hmono

set_option maxRecDepth 8000 in
theorem finiteSimplex_remainder_integral_bound
    {H : Finset ℕ} {f : (H → ℝ) → ℝ}
    {mesh : ℕ} (hmesh : 0 < mesh)
    (hbound : ∀ x ∈ finiteSimplexOf H, |f x| ≤ 1) :
    |∫ x in finiteSimplexOf H \
        fractionalGridCellUnion
          (fractionalSimplexInnerGridIndex H mesh) mesh, f x| ≤
      simplexBoundaryGridVolume H mesh := by
  let A := fractionalGridCellUnion
    (fractionalSimplexInnerGridIndex H mesh) mesh
  let B := fractionalGridCellUnion
    (fractionalSimplexBoundaryGridIndex H mesh) mesh
  let E := fractionalCoordinateOneFaces H ∩ finiteSimplexOf H
  let R := finiteSimplexOf H \ A
  have hRsubset : R ⊆ B ∪ E := by
    intro x hx
    have hcover := finiteSimplexOf_subset_inner_boundary_faces mesh hmesh hx.1
    rcases hcover with hxAB | hxFace
    · rcases hxAB with hxA | hxB
      · exact False.elim (hx.2 hxA)
      · exact Or.inl hxB
    · exact Or.inr ⟨hxFace, hx.1⟩
  have hBsubset : B ⊆ maynardCubeOf H := by
    intro x hx
    dsimp [B] at hx
    rw [fractionalGridCellUnion, Set.mem_iUnion] at hx
    obtain ⟨j, hxj⟩ := hx
    rw [Set.mem_iUnion] at hxj
    obtain ⟨hj, hxCell⟩ := hxj
    have hjGrid := (Finset.mem_filter.mp hj).1
    rw [maynardCubeOf, Set.mem_pi]
    intro h hh
    have hxh := (Set.mem_univ_pi.mp hxCell) h
    have hend := fractionalGridEndpoints_mem_Icc hmesh hjGrid h
    exact ⟨hend.1.1.trans hxh.1, hxh.2.le.trans hend.2.1.2⟩
  have hEsubset : E ⊆ maynardCubeOf H := fun x hx => hx.2.1
  have hUsubset : B ∪ E ⊆ maynardCubeOf H :=
    Set.union_subset hBsubset hEsubset
  have hRfinite : volume R < ⊤ :=
    lt_of_le_of_lt (measure_mono (hRsubset.trans hUsubset))
      (maynardCubeOf_measure_lt_top H)
  have hnorm : |∫ x in R, f x| ≤ (volume R).toReal := by
    have hb := norm_setIntegral_le_of_norm_le_const
      (f := f) (C := (1 : ℝ)) hRfinite
      (fun x hx => by rw [Real.norm_eq_abs]; exact hbound x hx.1)
    simpa only [Real.norm_eq_abs, one_mul,
      MeasureTheory.measureReal_def] using hb
  have hUfinite : volume (B ∪ E) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono hUsubset)
      (maynardCubeOf_measure_lt_top H))
  have hmeasureMono : (volume R).toReal ≤ (volume (B ∪ E)).toReal :=
    measureReal_mono hRsubset hUfinite
  have hEzero : volume E = 0 :=
    measure_mono_null Set.inter_subset_left
      (volume_fractionalCoordinateOneFaces H)
  have hUnionBound : (volume (B ∪ E)).toReal ≤ (volume B).toReal := by
    rw [← MeasureTheory.measureReal_def, ← MeasureTheory.measureReal_def]
    calc
      volume.real (B ∪ E) ≤ volume.real B + volume.real E :=
        measureReal_union_le B E
      _ = volume.real B := by simp [MeasureTheory.measureReal_def, hEzero]
  have hBGrid : fractionalSimplexBoundaryGridIndex H mesh ⊆
      fractionalGridIndex H mesh := by
    intro j hj
    exact (Finset.mem_filter.mp hj).1
  have hBvolume := volume_fractionalGridCellUnion_toReal hmesh hBGrid
  change |∫ x in R, f x| ≤ _
  calc
    _ ≤ (volume R).toReal := hnorm
    _ ≤ (volume (B ∪ E)).toReal := hmeasureMono
    _ ≤ (volume B).toReal := hUnionBound
    _ = _ := by simpa [B, simplexBoundaryGridVolume] using hBvolume

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1200000 in
theorem tendsto_finiteSimplexInnerGridWeightedSum
    {H : Finset ℕ} (h0 : H) {f : (H → ℝ) → ℝ}
    (hf : Continuous f) (hbound : ∀ x ∈ finiteSimplexOf H, |f x| ≤ 1) :
    Tendsto (fun mesh : ℕ => finiteSimplexInnerGridWeightedSum f mesh)
      atTop (nhds (∫ x in finiteSimplexOf H, f x)) := by
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  have hhalf : 0 < epsilon / 2 := by linarith
  have hosc := eventually_fractionalGridCell_oscillation hf hhalf
  have hboundaryT := tendsto_simplexBoundaryGridVolume_zero h0
  have hboundary := hboundaryT.eventually (Iio_mem_nhds hhalf)
  filter_upwards [hosc, hboundary, eventually_ge_atTop 1] with
      mesh hoscMesh hboundaryMesh hmeshOne
  have hmesh : 0 < mesh := by omega
  let A := fractionalGridCellUnion
    (fractionalSimplexInnerGridIndex H mesh) mesh
  have hinner := finiteSimplexInnerGridWeightedSum_sub_integral_bound
    hf hmesh hhalf.le (fun j hj x hx => (hoscMesh j hj x hx).le)
  have hvolume := simplexInnerGridVolume_le_one_finite
    (H := H) hmesh
  have hinnerHalf : |finiteSimplexInnerGridWeightedSum f mesh -
      ∫ x in A, f x| ≤ epsilon / 2 :=
    hinner.trans (mul_le_of_le_one_right hhalf.le hvolume)
  have hrem := finiteSimplex_remainder_integral_bound
    (H := H) hmesh hbound
  have hremHalf : |∫ x in finiteSimplexOf H \ A, f x| < epsilon / 2 :=
    lt_of_le_of_lt hrem hboundaryMesh
  have hAmeas : MeasurableSet A :=
    measurableSet_fractionalGridCellUnion _ _
  have hAsub : A ⊆ finiteSimplexOf H := by
    intro x hx
    dsimp [A] at hx
    rw [fractionalGridCellUnion, Set.mem_iUnion] at hx
    obtain ⟨j, hxj⟩ := hx
    rw [Set.mem_iUnion] at hxj
    obtain ⟨hj, hxCell⟩ := hxj
    exact fractionalGridCell_subset_finiteSimplexOf_inner hmesh hj hxCell
  have hfInt : IntegrableOn f (finiteSimplexOf H) :=
    hf.continuousOn.integrableOn_compact (isCompact_finiteSimplexOf H)
  have hsplit := setIntegral_sdiff hAmeas hfInt hAsub
  rw [Real.dist_eq]
  calc
    |finiteSimplexInnerGridWeightedSum f mesh -
        ∫ x in finiteSimplexOf H, f x| =
      |(finiteSimplexInnerGridWeightedSum f mesh - ∫ x in A, f x) -
        ∫ x in finiteSimplexOf H \ A, f x| := by rw [hsplit]; ring_nf
    _ ≤ |finiteSimplexInnerGridWeightedSum f mesh - ∫ x in A, f x| +
        |∫ x in finiteSimplexOf H \ A, f x| := abs_sub _ _
    _ < epsilon := by linarith

end BoundedGaps.Maynard
