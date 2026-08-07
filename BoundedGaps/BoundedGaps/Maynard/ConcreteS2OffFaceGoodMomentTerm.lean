import BoundedGaps.Maynard.ConcreteS2OffFaceGoodMomentBounds

noncomputable section

namespace BoundedGaps.Maynard

open Filter Set
open scoped BigOperators

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1200000 in
theorem exists_large_mesh_eventually_engelsmaS2OffFaceGrid_quadratic_oscillation
    {alpha : ℝ} (halpha : 0 < alpha)
    (m : BoundedGaps.engelsmaTuple) (b c M : ℕ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ mesh : ℕ, M ≤ mesh ∧ 0 < mesh ∧
      ∀ᶠ N : ℕ in atTop,
        ∀ j ∈ fractionalSimplexInnerGridIndex
            (engelsmaOffFaceFinset m) mesh,
        ∀ u ∈ engelsmaFractionalTupleShell
            (engelsmaOffFaceFinset m) alpha
              (fractionalGridLower mesh j)
              (fractionalGridUpper mesh j) N,
          |engelsmaS2OffFaceQuadraticIntegrand m b c
              (engelsmaS2OffFaceNormalizedLogPoint alpha N m u) -
            engelsmaS2OffFaceQuadraticIntegrand m b c
              (fractionalGridLower mesh j)| < epsilon := by
  have huc := uniformContinuousOn_engelsmaS2OffFaceQuadraticIntegrand_cube m b c
  obtain ⟨delta, hdelta, hcontrol⟩ :=
    (Metric.uniformContinuousOn_iff.mp huc) epsilon hepsilon
  have hmeshT : Tendsto (fun mesh : ℕ => (2 : ℝ) / mesh)
      atTop (nhds 0) := tendsto_const_div_atTop_nhds_zero_nat 2
  have hmeshEvent := hmeshT.eventually (Iio_mem_nhds hdelta)
  rw [eventually_atTop] at hmeshEvent
  obtain ⟨mesh0, hmesh0⟩ := hmeshEvent
  let mesh := max mesh0 (max M 1)
  have hmesh : 0 < mesh := by dsimp [mesh]; omega
  have hMmesh : M ≤ mesh := by simp [mesh]
  have hcloseMesh : (2 : ℝ) / mesh < delta := by
    exact hmesh0 mesh (by simp [mesh])
  refine ⟨mesh, hMmesh, hmesh, ?_⟩
  have hclose := eventually_fractionalGridShell_normalizedLog_close
    (H := engelsmaOffFaceFinset m) halpha hmesh
  have hsubset := eventually_engelsmaSimplexInnerGridSupport_subset
    (H := engelsmaOffFaceFinset m) halpha hmesh
  have hR := eventually_one_lt_engelsmaMaynardRadius halpha
  filter_upwards [hclose, hsubset, hR] with N hcloseN hsubsetN hRN
      j hj u hu
  have hjGrid := (Finset.mem_filter.mp hj).1
  have huInner : u ∈ engelsmaSimplexInnerGridSupport
      (engelsmaOffFaceFinset m) alpha mesh N := by
    rw [engelsmaSimplexInnerGridSupport, Finset.mem_biUnion]
    exact ⟨j, hj, hu⟩
  have huPre := hsubsetN huInner
  have huBox : u ∈ maynardDivisorTupleBox
      (engelsmaOffFaceFinset m)
      (engelsmaMaynardRadius alpha N) := by
    rw [mem_maynardDivisorTupleBox_iff]
    intro h
    have huh := Fintype.mem_piFinset.mp
      (mem_preSievedSimplexTupleSupport_iff.mp huPre).1 h
    have huhData := Finset.mem_filter.mp huh
    exact ⟨huhData.2.1, Finset.mem_range.mp huhData.1⟩
  have hactualCube :
      engelsmaS2OffFaceNormalizedLogPoint alpha N m u ∈
        maynardCubeOf (engelsmaOffFaceFinset m) := by
    rw [maynardCubeOf, Set.mem_pi]
    intro h hh
    exact normalizedDivisorLogTuple_mem_Icc_of_mem_maynardDivisorTupleBox
      hRN huBox h
  have hlowerCube := engelsmaS2OffFaceGridLowerPoint_mem_cube m hmesh hj
  have hdist : dist
      (engelsmaS2OffFaceNormalizedLogPoint alpha N m u)
      (engelsmaS2OffFaceGridLowerPoint m mesh j) < delta := by
    apply (dist_pi_lt_iff hdelta).mpr
    intro h
    apply lt_trans ?_ hcloseMesh
    have hcoord := hcloseN j hjGrid u hu h
    simpa [engelsmaS2OffFaceNormalizedLogPoint,
      engelsmaS2OffFaceGridLowerPoint,
      normalizedDivisorLogTuple, Real.dist_eq] using hcoord
  have hout := hcontrol _ hactualCube _ hlowerCube hdist
  simpa [Real.dist_eq, engelsmaS2OffFaceGridLowerPoint] using hout

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1600000 in
theorem tendsto_normalizedEngelsmaS2OffFaceGoodQuadraticMoment
    {alpha : ℝ} (halpha : 0 < alpha)
    (m : BoundedGaps.engelsmaTuple) (b c : ℕ) :
    Tendsto (fun N : ℕ =>
      normalizedEngelsmaS2OffFaceGoodQuadraticMoment alpha N m b c)
      atTop (nhds (∫ t in maynardFaceSimplex (engelsmaIndexEquiv m),
        faceQuadraticIntegrand (engelsmaIndexEquiv m) b c t)) := by
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  have he20 : 0 < epsilon / 20 := by linarith
  have he10 : 0 < epsilon / 10 := by linarith
  let L := ∫ t in maynardFaceSimplex (engelsmaIndexEquiv m),
    faceQuadraticIntegrand (engelsmaIndexEquiv m) b c t
  have hgridT := tendsto_engelsmaS2OffFaceRiemannStep m b c
  have hgrid : ∀ᶠ mesh : ℕ in atTop,
      dist (
        ∑ j ∈ fractionalSimplexInnerGridIndex
            (engelsmaOffFaceFinset m) mesh,
          engelsmaS2OffFaceQuadraticIntegrand m b c
              (fractionalGridLower mesh j) *
            ∏ h : engelsmaOffFaceFinset m,
              (fractionalGridUpper mesh j h -
                fractionalGridLower mesh j h)) L < epsilon / 20 := by
    simpa [L] using hgridT.eventually
      (Metric.ball_mem_nhds _ he20)
  have hvolT := tendsto_simplexBoundaryGridVolume_engelsmaS2OffFace_zero m
  have hvol : ∀ᶠ mesh : ℕ in atTop,
      simplexBoundaryGridVolume (engelsmaOffFaceFinset m) mesh < epsilon / 20 := by
    simpa using hvolT.eventually (Iio_mem_nhds he20)
  have hmeshEvent := hgrid.and hvol
  rw [eventually_atTop] at hmeshEvent
  obtain ⟨M, hM⟩ := hmeshEvent
  obtain ⟨mesh, hMmesh, hmesh, hosc⟩ :=
    exists_large_mesh_eventually_engelsmaS2OffFaceGrid_quadratic_oscillation
      halpha m b c M he20
  have hmeshGrid := hM mesh hMmesh
  have hgridClose : dist (
        ∑ j ∈ fractionalSimplexInnerGridIndex
            (engelsmaOffFaceFinset m) mesh,
          engelsmaS2OffFaceQuadraticIntegrand m b c
              (fractionalGridLower mesh j) *
            ∏ h : engelsmaOffFaceFinset m,
              (fractionalGridUpper mesh j h -
                fractionalGridLower mesh j h)) L < epsilon / 20 :=
    hmeshGrid.1
  have hvolSmall : simplexBoundaryGridVolume
      (engelsmaOffFaceFinset m) mesh < epsilon / 20 := hmeshGrid.2
  let I := fractionalSimplexInnerGridIndex
    (engelsmaOffFaceFinset m) mesh
  let innerMass : ℕ → ℝ := fun N =>
    ∑ j ∈ I,
      normalizedMaynardS2OuterSquarefreeTupleShellMass
        (engelsmaOffFaceFinset m) alpha N
        (fun h => engelsmaMaynardRadius
          (alpha * fractionalGridLower mesh j h) N)
        (fun h => engelsmaMaynardRadius
          (alpha * fractionalGridUpper mesh j h) N)
  have hmassT : Tendsto innerMass atTop
      (nhds (simplexInnerGridVolume (engelsmaOffFaceFinset m) mesh)) := by
    have hlim := tendsto_finite_linear_combination_normalizedMaynardS2OuterSquarefreeTupleShellMass
      halpha I (fun _ => (1 : ℝ))
      (fun j => fractionalGridLower mesh j)
      (fun j => fractionalGridUpper mesh j)
      (fun j hj h => (fractionalSimplexInnerGridIndex_data hmesh hj).1 h |>.1)
      (fun j hj h => (fractionalSimplexInnerGridIndex_data hmesh hj).1 h |>.2.1)
      (fun j hj h => (fractionalSimplexInnerGridIndex_data hmesh hj).1 h |>.2.2)
    simpa [innerMass, I, simplexInnerGridVolume] using hlim
  have hvolLe := simplexInnerGridVolume_le_one_finite (H := engelsmaOffFaceFinset m)
    hmesh
  have hmass : ∀ᶠ N : ℕ in atTop, innerMass N < 2 := by
    have : simplexInnerGridVolume (engelsmaOffFaceFinset m) mesh < 2 := by linarith
    exact hmassT.eventually (Iio_mem_nhds this)
  have hmassEq : ∀ N : ℕ,
      innerMass N =
        (∑ j ∈ I,
          maynardS2OuterSquarefreeTupleShellMass
            (engelsmaOffFaceFinset m) (engelsmaMaynardModulus N)
            (fun h => engelsmaMaynardRadius
              (alpha * fractionalGridLower mesh j h) N)
            (fun h => engelsmaMaynardRadius
              (alpha * fractionalGridUpper mesh j h) N)) /
          engelsmaS2OffFaceNaturalScale alpha N m := by
    intro N
    unfold innerMass
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    unfold normalizedMaynardS2OuterSquarefreeTupleShellMass
      engelsmaS2OffFaceNaturalScale
    rfl
  have hboundaryEq := eventually_normalizedEngelsmaS2OffFaceBoundaryGridSupportMass_eq_stepMass
    halpha m hmesh
  have hboundaryT := tendsto_normalizedEngelsmaS2OffFaceBoundaryGridStepMass
    halpha m hmesh
  have hboundary : ∀ᶠ N : ℕ in atTop,
      normalizedEngelsmaS2OffFaceBoundaryGridSupportMass alpha m mesh N <
        epsilon / 10 := by
    filter_upwards [hboundaryEq,
      hboundaryT.eventually (Metric.ball_mem_nhds _ he20)] with
      N hEq hStep
    rw [hEq]
    have hdist : |normalizedEngelsmaS2OffFaceBoundaryGridStepMass
          alpha m mesh N -
        simplexBoundaryGridVolume (engelsmaOffFaceFinset m) mesh| < epsilon / 20 := by
      simpa [Real.dist_eq] using hStep
    have hle := le_abs_self
      (normalizedEngelsmaS2OffFaceBoundaryGridStepMass alpha m mesh N -
        simplexBoundaryGridVolume (engelsmaOffFaceFinset m) mesh)
    linarith
  have hunitT := tendsto_normalizedEngelsmaS2OuterUnitBoundaryBoxUnionMass_zero
    (H := engelsmaOffFaceFinset m) halpha
  have hunit : ∀ᶠ N : ℕ in atTop,
      |normalizedEngelsmaS2OuterUnitBoundaryBoxUnionMass
          (engelsmaOffFaceFinset m) alpha N| < epsilon / 20 :=
    hunitT.eventually (Metric.ball_mem_nhds _ he20) |>.mono (by
      intro N hN
      simpa [Real.dist_eq] using hN)
  have hcollisionT := tendsto_normalizedEngelsmaS2OffFaceCollisionOuterMass_zero
    halpha m
  have hcollision : ∀ᶠ N : ℕ in atTop,
      |normalizedEngelsmaS2OffFaceCollisionOuterMass alpha m N| < epsilon / 20 :=
    hcollisionT.eventually (Metric.ball_mem_nhds _ he20) |>.mono (by
      intro N hN
      simpa [Real.dist_eq] using hN)
  have hstepT := tendsto_engelsmaS2OffFaceGridQuadraticStep
    halpha m hmesh b c
  have hstep : ∀ᶠ N : ℕ in atTop,
      dist (engelsmaS2OffFaceGridQuadraticStep alpha m mesh N b c)
        (∑ j ∈ I,
          engelsmaS2OffFaceQuadraticIntegrand m b c
              (fractionalGridLower mesh j) *
            ∏ h : engelsmaOffFaceFinset m,
              (fractionalGridUpper mesh j h -
                fractionalGridLower mesh j h)) < epsilon / 20 := by
    simpa [I] using hstepT.eventually (Metric.ball_mem_nhds _ he20)
  have hscale := eventually_engelsmaS2OffFaceNaturalScale_pos halpha m
  have hbounds := eventually_engelsmaS2OffFaceGoodQuadraticMoment_sub_inner_bounds
    halpha m hmesh b c
  filter_upwards [hosc, hmass, hboundary, hunit, hcollision, hstep,
      hscale, hbounds] with N hoscN hmassN hboundaryN hunitN hcollisionN
      hstepN hscaleN hboundsN
  have hcellRaw := engelsmaS2OffFaceInnerGridCell_sub_step_le
    (alpha := alpha) (m := m) (mesh := mesh) (N := N)
    (b := b) (c := c) (epsilon := epsilon / 20) (by linarith)
    (fun j hj u hu => (hoscN j hj u hu).le)
  have hcellNorm :
      |normalizedEngelsmaS2OffFaceInnerGridQuadraticCellSum alpha m mesh N b c -
          engelsmaS2OffFaceGridQuadraticStep alpha m mesh N b c| < epsilon / 5 := by
    rw [engelsmaS2OffFaceGridQuadraticStep_eq_div]
    unfold normalizedEngelsmaS2OffFaceInnerGridQuadraticCellSum
    rw [← sub_div, abs_div, abs_of_pos hscaleN]
    have hrawMass := hmassEq N
    have hscalePos := hscaleN
    calc
      |engelsmaS2OffFaceInnerGridQuadraticCellSum alpha m mesh N b c -
          engelsmaS2OffFaceInnerGridQuadraticStepSum alpha m mesh N b c| /
          engelsmaS2OffFaceNaturalScale alpha N m ≤
          (epsilon / 20) *
            (∑ j ∈ I,
              maynardS2OuterSquarefreeTupleShellMass
                (engelsmaOffFaceFinset m) (engelsmaMaynardModulus N)
                (fun h => engelsmaMaynardRadius
                  (alpha * fractionalGridLower mesh j h) N)
                (fun h => engelsmaMaynardRadius
                  (alpha * fractionalGridUpper mesh j h) N)) /
            engelsmaS2OffFaceNaturalScale alpha N m := by
            exact div_le_div_of_nonneg_right hcellRaw hscalePos.le
      _ = (epsilon / 20) * innerMass N := by
        rw [hrawMass]
        ring
      _ < epsilon / 10 := by nlinarith [hmassN]
      _ < epsilon / 5 := by linarith
  have hgoodCell :
      |normalizedEngelsmaS2OffFaceGoodQuadraticMoment alpha N m b c -
          normalizedEngelsmaS2OffFaceInnerGridQuadraticCellSum alpha m mesh N b c| <
        epsilon / 5 := by
    have hlow := hboundsN.1
    have hupp := hboundsN.2
    have hc : |normalizedEngelsmaS2OffFaceCollisionOuterMass alpha m N| <
        epsilon / 20 := hcollisionN
    have hb : normalizedEngelsmaS2OffFaceBoundaryGridSupportMass alpha m mesh N <
        epsilon / 10 := hboundaryN
    have hu : |normalizedEngelsmaS2OuterUnitBoundaryBoxUnionMass
        (engelsmaOffFaceFinset m) alpha N| < epsilon / 20 := hunitN
    rw [abs_lt]
    constructor
    · have hcLe : normalizedEngelsmaS2OffFaceCollisionOuterMass alpha m N <
          epsilon / 20 := (le_abs_self _).trans_lt hc
      linarith
    · have huLe : normalizedEngelsmaS2OuterUnitBoundaryBoxUnionMass
          (engelsmaOffFaceFinset m) alpha N < epsilon / 20 :=
        (le_abs_self _).trans_lt hu
      linarith
  have hstepGrid :
      |engelsmaS2OffFaceGridQuadraticStep alpha m mesh N b c - L| <
        epsilon / 10 := by
    have h1 : |engelsmaS2OffFaceGridQuadraticStep alpha m mesh N b c -
        (∑ j ∈ I,
          engelsmaS2OffFaceQuadraticIntegrand m b c
              (fractionalGridLower mesh j) *
            ∏ h : engelsmaOffFaceFinset m,
              (fractionalGridUpper mesh j h -
                fractionalGridLower mesh j h))| < epsilon / 20 := by
      simpa [Real.dist_eq] using hstepN
    have h2 : |(∑ j ∈ I,
          engelsmaS2OffFaceQuadraticIntegrand m b c
              (fractionalGridLower mesh j) *
            ∏ h : engelsmaOffFaceFinset m,
              (fractionalGridUpper mesh j h -
                fractionalGridLower mesh j h)) - L| < epsilon / 20 := by
      simpa [Real.dist_eq] using hgridClose
    calc
      |engelsmaS2OffFaceGridQuadraticStep alpha m mesh N b c - L| =
          |(engelsmaS2OffFaceGridQuadraticStep alpha m mesh N b c -
          (∑ j ∈ I,
            engelsmaS2OffFaceQuadraticIntegrand m b c
                (fractionalGridLower mesh j) *
              ∏ h : engelsmaOffFaceFinset m,
                (fractionalGridUpper mesh j h -
                  fractionalGridLower mesh j h))) +
            ((∑ j ∈ I,
              engelsmaS2OffFaceQuadraticIntegrand m b c
                  (fractionalGridLower mesh j) *
                ∏ h : engelsmaOffFaceFinset m,
                  (fractionalGridUpper mesh j h -
                    fractionalGridLower mesh j h)) - L)| := by ring_nf
      _ ≤ |engelsmaS2OffFaceGridQuadraticStep alpha m mesh N b c -
          (∑ j ∈ I,
            engelsmaS2OffFaceQuadraticIntegrand m b c
                (fractionalGridLower mesh j) *
              ∏ h : engelsmaOffFaceFinset m,
                (fractionalGridUpper mesh j h -
                  fractionalGridLower mesh j h))| +
          |(∑ j ∈ I,
            engelsmaS2OffFaceQuadraticIntegrand m b c
                (fractionalGridLower mesh j) *
              ∏ h : engelsmaOffFaceFinset m,
                (fractionalGridUpper mesh j h -
                  fractionalGridLower mesh j h)) - L| := abs_add_le _ _
      _ < epsilon / 10 := by linarith
  have hgoodLimit : |normalizedEngelsmaS2OffFaceGoodQuadraticMoment
      alpha N m b c - L| < epsilon := by
    have hdecomp :
        normalizedEngelsmaS2OffFaceGoodQuadraticMoment alpha N m b c - L =
          (normalizedEngelsmaS2OffFaceGoodQuadraticMoment alpha N m b c -
            normalizedEngelsmaS2OffFaceInnerGridQuadraticCellSum
              alpha m mesh N b c) +
          (normalizedEngelsmaS2OffFaceInnerGridQuadraticCellSum
              alpha m mesh N b c -
            engelsmaS2OffFaceGridQuadraticStep alpha m mesh N b c) +
          (engelsmaS2OffFaceGridQuadraticStep alpha m mesh N b c - L) := by
      ring
    rw [hdecomp]
    calc
      |(normalizedEngelsmaS2OffFaceGoodQuadraticMoment alpha N m b c -
            normalizedEngelsmaS2OffFaceInnerGridQuadraticCellSum
              alpha m mesh N b c) +
          (normalizedEngelsmaS2OffFaceInnerGridQuadraticCellSum
              alpha m mesh N b c -
            engelsmaS2OffFaceGridQuadraticStep alpha m mesh N b c) +
          (engelsmaS2OffFaceGridQuadraticStep alpha m mesh N b c - L)| ≤
        |(normalizedEngelsmaS2OffFaceGoodQuadraticMoment alpha N m b c -
            normalizedEngelsmaS2OffFaceInnerGridQuadraticCellSum
              alpha m mesh N b c) +
          (normalizedEngelsmaS2OffFaceInnerGridQuadraticCellSum
              alpha m mesh N b c -
            engelsmaS2OffFaceGridQuadraticStep alpha m mesh N b c)| +
          |engelsmaS2OffFaceGridQuadraticStep alpha m mesh N b c - L| :=
        abs_add_le _ _
      _ ≤ |normalizedEngelsmaS2OffFaceGoodQuadraticMoment alpha N m b c -
            normalizedEngelsmaS2OffFaceInnerGridQuadraticCellSum
              alpha m mesh N b c| +
          |normalizedEngelsmaS2OffFaceInnerGridQuadraticCellSum
              alpha m mesh N b c -
            engelsmaS2OffFaceGridQuadraticStep alpha m mesh N b c| +
          |engelsmaS2OffFaceGridQuadraticStep alpha m mesh N b c - L| :=
        by gcongr; exact abs_add_le _ _
      _ < epsilon := by linarith [hgoodCell, hcellNorm, hstepGrid]
  simpa [L, Real.dist_eq] using hgoodLimit


end BoundedGaps.Maynard
