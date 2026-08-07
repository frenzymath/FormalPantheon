import BoundedGaps.Maynard.ConcreteS2OffFaceGridStep
import BoundedGaps.Maynard.ConcreteSimplexGridOscillation

noncomputable section

namespace BoundedGaps.Maynard

open Filter Set
open scoped BigOperators

def engelsmaS2OffFaceGridLowerPoint
    (m : BoundedGaps.engelsmaTuple)
    (mesh : ℕ) (j : engelsmaOffFaceFinset m → ℕ) :
    engelsmaOffFaceFinset m → ℝ :=
  fractionalGridLower mesh j

def engelsmaS2OffFaceNormalizedLogPoint
    (alpha : ℝ) (N : ℕ) (m : BoundedGaps.engelsmaTuple)
    (u : engelsmaOffFaceFinset m → ℕ) :
    engelsmaOffFaceFinset m → ℝ :=
  normalizedDivisorLogTuple (engelsmaOffFaceFinset m)
    (engelsmaMaynardRadius alpha N) u

theorem continuous_engelsmaS2OffFaceQuadraticIntegrand
    (m : BoundedGaps.engelsmaTuple) (b c : ℕ) :
    Continuous (engelsmaS2OffFaceQuadraticIntegrand m b c) := by
  unfold engelsmaS2OffFaceQuadraticIntegrand faceQuadraticIntegrand
  fun_prop

theorem isCompact_engelsmaS2OffFaceCube
    (m : BoundedGaps.engelsmaTuple) :
    IsCompact (maynardCubeOf (engelsmaOffFaceFinset m)) := by
  unfold maynardCubeOf
  exact isCompact_univ_pi (fun _ => isCompact_Icc)

theorem uniformContinuousOn_engelsmaS2OffFaceQuadraticIntegrand_cube
    (m : BoundedGaps.engelsmaTuple) (b c : ℕ) :
    UniformContinuousOn (engelsmaS2OffFaceQuadraticIntegrand m b c)
      (maynardCubeOf (engelsmaOffFaceFinset m)) :=
  (isCompact_engelsmaS2OffFaceCube m).uniformContinuousOn_of_continuous
    (continuous_engelsmaS2OffFaceQuadraticIntegrand m b c).continuousOn

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
theorem engelsmaS2OffFaceGridLowerPoint_mem_cube
    (m : BoundedGaps.engelsmaTuple)
    {mesh : ℕ} (hmesh : 0 < mesh)
    {j : engelsmaOffFaceFinset m → ℕ}
    (hj : j ∈ fractionalSimplexInnerGridIndex
      (engelsmaOffFaceFinset m) mesh) :
    engelsmaS2OffFaceGridLowerPoint m mesh j ∈
      maynardCubeOf (engelsmaOffFaceFinset m) := by
  rw [maynardCubeOf, Set.mem_pi]
  intro h hh
  exact (fractionalSimplexInnerGridIndex_data hmesh hj).1 h |>.1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1200000 in
theorem exists_mesh_eventually_engelsmaS2OffFaceGrid_quadratic_oscillation
    {alpha : ℝ} (halpha : 0 < alpha)
    (m : BoundedGaps.engelsmaTuple) (b c : ℕ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ mesh : ℕ, 0 < mesh ∧
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
              (engelsmaS2OffFaceGridLowerPoint m mesh j)| < epsilon := by
  have huc :=
    uniformContinuousOn_engelsmaS2OffFaceQuadraticIntegrand_cube m b c
  obtain ⟨delta, hdelta, hcontrol⟩ :=
    (Metric.uniformContinuousOn_iff.mp huc) epsilon hepsilon
  have hmeshT : Tendsto (fun mesh : ℕ => (2 : ℝ) / mesh)
      atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)
  have hmeshEvent := hmeshT.eventually (Iio_mem_nhds hdelta)
  rw [eventually_atTop] at hmeshEvent
  obtain ⟨mesh0, hmesh0⟩ := hmeshEvent
  let mesh := max mesh0 1
  have hmesh : 0 < mesh := by dsimp [mesh]; omega
  have hcloseMesh : (2 : ℝ) / mesh < delta := by
    exact hmesh0 mesh (by simp [mesh])
  refine ⟨mesh, hmesh, ?_⟩
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
    have huCommon := (mem_preSievedSimplexTupleSupport_iff.mp huPre).1
    have huh := Fintype.mem_piFinset.mp huCommon h
    have huhData := Finset.mem_filter.mp huh
    exact ⟨huhData.2.1, Finset.mem_range.mp huhData.1⟩
  have hactualCube :
      engelsmaS2OffFaceNormalizedLogPoint alpha N m u ∈
        maynardCubeOf (engelsmaOffFaceFinset m) := by
    rw [maynardCubeOf, Set.mem_pi]
    intro h hh
    exact normalizedDivisorLogTuple_mem_Icc_of_mem_maynardDivisorTupleBox
      hRN huBox h
  have hlowerCube := engelsmaS2OffFaceGridLowerPoint_mem_cube
    m hmesh hj
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
  simpa [Real.dist_eq] using hout

end BoundedGaps.Maynard
