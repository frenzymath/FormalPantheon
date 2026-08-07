import BoundedGaps.Maynard.ConcreteIndependentMomentFixedMesh
import BoundedGaps.Maynard.ConcreteRadiusLogAsymptotics

noncomputable section
namespace BoundedGaps.Maynard

open Filter Set
open scoped BigOperators

set_option maxRecDepth 10000 in
theorem exists_large_mesh_eventually_innerGridShell_quadratic_oscillation
    {alpha : ℝ} (halpha : 0 < alpha) (b c M : ℕ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ m : ℕ, M ≤ m ∧ 0 < m ∧
      ∀ᶠ N : ℕ in atTop,
        ∀ j ∈ fractionalSimplexInnerGridIndex BoundedGaps.engelsmaTuple m,
        ∀ u ∈ engelsmaFractionalTupleShell BoundedGaps.engelsmaTuple alpha
          (fractionalGridLower m j) (fractionalGridUpper m j) N,
          |simplexQuadraticIntegrand 105 b c
              (engelsmaNormalizedLogPoint alpha N u) -
            simplexQuadraticIntegrand 105 b c
              (engelsmaGridLowerPoint m j)| < epsilon := by
  have huc := uniformContinuousOn_simplexQuadraticIntegrand_cube 105 b c
  obtain ⟨delta, hdelta, hcontrol⟩ :=
    (Metric.uniformContinuousOn_iff.mp huc) epsilon hepsilon
  have hmeshT : Tendsto (fun m : ℕ => (2 : ℝ) / m) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)
  have hmeshEvent := hmeshT.eventually (Iio_mem_nhds hdelta)
  rw [eventually_atTop] at hmeshEvent
  obtain ⟨m0, hm0⟩ := hmeshEvent
  let m := max m0 (max M 1)
  have hm0m : m0 ≤ m := by simp [m]
  have hMm : M ≤ m := by simp [m]
  have hm : 0 < m := by dsimp [m]; omega
  have hmesh : (2 : ℝ) / m < delta := hm0 m hm0m
  refine ⟨m, hMm, hm, ?_⟩
  have hclose := eventually_fractionalGridShell_normalizedLog_close
    (H := BoundedGaps.engelsmaTuple) halpha hm
  have hsubset := eventually_engelsmaSimplexInnerGridSupport_subset
    (H := BoundedGaps.engelsmaTuple) halpha hm
  have hR := eventually_one_lt_engelsmaMaynardRadius halpha
  filter_upwards [hclose, hsubset, hR] with N hcloseN hsubsetN hRN
      j hj u hu
  have hjGrid := (Finset.mem_filter.mp hj).1
  have huInner : u ∈ engelsmaSimplexInnerGridSupport
      BoundedGaps.engelsmaTuple alpha m N := by
    rw [engelsmaSimplexInnerGridSupport, Finset.mem_biUnion]
    exact ⟨j, hj, hu⟩
  have huSimplex := hsubsetN huInner
  have hlogSimplex := normalizedEngelsmaLogTuple_mem_simplex_of_independent
    hRN huSimplex
  have hlogCube : engelsmaNormalizedLogPoint alpha N u ∈ maynardCube 105 :=
    hlogSimplex.1
  have hlowerCube := engelsmaGridLowerPoint_mem_cube hm hjGrid
  have hdist : dist (engelsmaNormalizedLogPoint alpha N u)
      (engelsmaGridLowerPoint m j) < delta := by
    apply (dist_pi_lt_iff hdelta).mpr
    intro i
    apply lt_trans ?_ hmesh
    have hcoord := hcloseN j hjGrid u hu (engelsmaIndexEquiv.symm i)
    simpa [engelsmaNormalizedLogPoint, engelsmaGridLowerPoint,
      normalizedDivisorLogTuple, Real.dist_eq] using hcoord
  have hout := hcontrol _ hlogCube _ hlowerCube hdist
  simpa [Real.dist_eq] using hout

set_option maxRecDepth 10000 in
theorem tendsto_normalizedEngelsmaIndependentQuadraticNatural
    {alpha : ℝ} (halpha : 0 < alpha) (b c : ℕ) :
    Tendsto (fun N : ℕ =>
      normalizedEngelsmaIndependentQuadraticNatural alpha N b c)
      atTop (nhds (∫ x in maynardSimplex 105,
        simplexQuadraticIntegrand 105 b c x)) := by
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  let L := ∫ x in maynardSimplex 105, simplexQuadraticIntegrand 105 b c x
  have he10 : 0 < epsilon / 10 := by linarith
  have he20 : 0 < epsilon / 20 := by linarith
  have hRiemT := tendsto_simplexInnerGridQuadraticWeightedSum b c
  have hRiem : ∀ᶠ m : ℕ in atTop,
      dist (simplexInnerGridQuadraticWeightedSum m b c) L < epsilon / 10 :=
    hRiemT.eventually (Metric.ball_mem_nhds _ he10)
  let h0 : BoundedGaps.engelsmaTuple :=
    ⟨0, BoundedGaps.engelsmaTuple_mem_zero⟩
  have hboundaryT := tendsto_simplexBoundaryGridVolume_zero h0
  have hboundary : ∀ᶠ m : ℕ in atTop,
      simplexBoundaryGridVolume BoundedGaps.engelsmaTuple m < epsilon / 20 :=
    hboundaryT.eventually (Iio_mem_nhds he20)
  have hmeshEvent := hRiem.and hboundary
  rw [eventually_atTop] at hmeshEvent
  obtain ⟨M, hM⟩ := hmeshEvent
  obtain ⟨m, hMm, hm, hosc⟩ :=
    exists_large_mesh_eventually_innerGridShell_quadratic_oscillation
      halpha b c M he20
  have hmeshData := hM m hMm
  have hgridClose := hmeshData.1
  have hboundaryVolume := hmeshData.2
  have hstepT := tendsto_normalizedEngelsmaInnerGridQuadraticStep
    halpha hm b c
  have hstep : ∀ᶠ N : ℕ in atTop,
      dist (normalizedEngelsmaInnerGridQuadraticStep alpha m N b c)
        (simplexInnerGridQuadraticWeightedSum m b c) < epsilon / 10 :=
    hstepT.eventually (Metric.ball_mem_nhds _ he10)
  have hmassT := tendsto_normalizedEngelsmaSimplexInnerGridStepMass
    (H := BoundedGaps.engelsmaTuple) halpha hm
  have hvolumeLe := simplexInnerGridVolume_le_one hm
  have hvolumeLt : simplexInnerGridVolume BoundedGaps.engelsmaTuple m < 2 := by
    linarith
  have hmass : ∀ᶠ N : ℕ in atTop,
      normalizedEngelsmaSimplexInnerGridStepMass
        BoundedGaps.engelsmaTuple alpha m N < 2 :=
    hmassT.eventually (Iio_mem_nhds hvolumeLt)
  have hboundaryStepT := tendsto_normalizedEngelsmaSimplexBoundaryGridStepMass
    (H := BoundedGaps.engelsmaTuple) halpha hm
  have hboundaryStep : ∀ᶠ N : ℕ in atTop,
      dist (normalizedEngelsmaSimplexBoundaryGridStepMass
          BoundedGaps.engelsmaTuple alpha m N)
        (simplexBoundaryGridVolume BoundedGaps.engelsmaTuple m) < epsilon / 20 :=
    hboundaryStepT.eventually (Metric.ball_mem_nhds _ he20)
  have hboundaryEq :=
    eventually_normalizedBoundaryGridSupportMassNatural_eq_stepMass halpha hm
  have hunitT := tendsto_normalizedEngelsmaUnitBoundaryBoxUnionMass_zero
    (H := BoundedGaps.engelsmaTuple) halpha
  have hunit : ∀ᶠ N : ℕ in atTop,
      dist (normalizedEngelsmaUnitBoundaryBoxUnionMass
        BoundedGaps.engelsmaTuple alpha N) 0 < epsilon / 10 :=
    hunitT.eventually (Metric.ball_mem_nhds _ he10)
  have hinnerEq :=
    eventually_normalizedInnerGridQuadraticNatural_eq_cellNatural
      halpha hm b c
  have henvelope := eventually_independentNatural_sub_inner_le_boundary
    halpha hm b c
  have hscale := eventually_engelsmaNaturalQuadraticScale_pos halpha
  filter_upwards [hosc, hstep, hmass, hboundaryStep, hboundaryEq,
      hunit, hinnerEq, henvelope, hscale] with N hoscN hstepN hmassN
      hboundaryStepN hboundaryEqN hunitN hinnerEqN henvelopeN hscaleN
  let full := normalizedEngelsmaIndependentQuadraticNatural alpha N b c
  let inner := normalizedEngelsmaInnerGridQuadraticNatural alpha m N b c
  let cell := normalizedEngelsmaInnerGridQuadraticCellNatural alpha m N b c
  let step := normalizedEngelsmaInnerGridQuadraticStep alpha m N b c
  let grid := simplexInnerGridQuadraticWeightedSum m b c
  let boundary := normalizedEngelsmaSimplexBoundaryGridSupportMassNatural
    alpha m N
  let unit := normalizedEngelsmaUnitBoundaryBoxUnionMass
    BoundedGaps.engelsmaTuple alpha N
  have hmassNonneg : 0 ≤ normalizedEngelsmaSimplexInnerGridStepMass
      BoundedGaps.engelsmaTuple alpha m N := by
    rw [normalizedEngelsmaSimplexInnerGridStepMass_eq_div]
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro j hj
      unfold engelsmaFractionalTupleShellMass
      apply Finset.sum_nonneg
      intro u hu
      unfold reciprocalTotientTupleWeight
      positivity
    · exact hscaleN.le
  have hcellStepRaw := innerGridQuadraticCellNatural_sub_step_le
    hscaleN he20.le (fun j hj u hu => (hoscN j hj u hu).le)
  have hcellStep : |cell - step| < epsilon / 10 := by
    dsimp [cell, step]
    apply lt_of_le_of_lt hcellStepRaw
    nlinarith
  have hinnerStep : |inner - step| < epsilon / 10 := by
    simpa [inner, cell, step, hinnerEqN] using hcellStep
  have hstepGrid : |step - grid| < epsilon / 10 := by
    simpa [step, grid, Real.dist_eq] using hstepN
  have hgridL : |grid - L| < epsilon / 10 := by
    simpa [grid, Real.dist_eq] using hgridClose
  have hboundarySmall : boundary < epsilon / 10 := by
    dsimp [boundary]
    rw [hboundaryEqN]
    have habs : |normalizedEngelsmaSimplexBoundaryGridStepMass
          BoundedGaps.engelsmaTuple alpha m N -
        simplexBoundaryGridVolume BoundedGaps.engelsmaTuple m| < epsilon / 20 := by
      simpa [Real.dist_eq] using hboundaryStepN
    linarith [le_abs_self
      (normalizedEngelsmaSimplexBoundaryGridStepMass
        BoundedGaps.engelsmaTuple alpha m N -
          simplexBoundaryGridVolume BoundedGaps.engelsmaTuple m)]
  have hunitSmall : unit < epsilon / 10 := by
    have habs : |unit| < epsilon / 10 := by
      simpa [unit, Real.dist_eq] using hunitN
    exact (le_abs_self unit).trans_lt habs
  have hfullInnerNonneg : 0 ≤ full - inner := henvelopeN.1
  have hfullInner : |full - inner| < epsilon / 5 := by
    rw [abs_of_nonneg hfullInnerNonneg]
    exact henvelopeN.2.trans_lt (by
      dsimp [boundary, unit] at hboundarySmall hunitSmall ⊢
      linarith)
  rw [Real.dist_eq]
  change |full - L| < epsilon
  calc
    |full - L| = |(full - inner) + (inner - step) +
        (step - grid) + (grid - L)| := by ring_nf
    _ ≤ |full - inner| + |inner - step| +
        |step - grid| + |grid - L| := by
      calc
        _ ≤ |(full - inner) + (inner - step) + (step - grid)| +
            |grid - L| := abs_add_le _ _
        _ ≤ (|(full - inner) + (inner - step)| + |step - grid|) +
            |grid - L| := by gcongr; exact abs_add_le _ _
        _ ≤ ((|full - inner| + |inner - step|) + |step - grid|) +
            |grid - L| := by gcongr; exact abs_add_le _ _
    _ < epsilon := by linarith

set_option maxRecDepth 10000 in
theorem eventually_normalizedIndependent_eq_natural_mul_logRatio
    {alpha : ℝ} (halpha : 0 < alpha) (b c : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      normalizedEngelsmaIndependentQuadraticMoment alpha N b c =
        normalizedEngelsmaIndependentQuadraticNatural alpha N b c *
          (Real.log (engelsmaMaynardRadius alpha N) /
            Real.log (engelsmaMaynardRealRadius alpha N)) ^ 105 := by
  have hR := eventually_one_lt_engelsmaMaynardRadius halpha
  filter_upwards [hR, eventually_ge_atTop 3] with N hRN hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hW : (0 : ℝ) < engelsmaMaynardModulus N := by
    exact_mod_cast primorial_pos (tripleLogCutoff (N - 1))
  have hphi : (0 : ℝ) < Nat.totient (engelsmaMaynardModulus N) := by
    exact_mod_cast Nat.totient_pos.mpr
      (primorial_pos (tripleLogCutoff (N - 1)))
  have hLnat : 0 < Real.log (engelsmaMaynardRadius alpha N) :=
    Real.log_pos (by exact_mod_cast hRN)
  have hRreal : 1 < engelsmaMaynardRealRadius alpha N := by
    unfold engelsmaMaynardRealRadius maynardRealCutoff
    apply Real.one_lt_rpow
    · exact_mod_cast (show 1 < N - 1 by omega)
    · exact halpha
  have hLreal : 0 < Real.log (engelsmaMaynardRealRadius alpha N) :=
    Real.log_pos hRreal
  unfold normalizedEngelsmaIndependentQuadraticMoment
    normalizedEngelsmaIndependentQuadraticNatural
  rw [engelsmaIndependentQuadraticWeightSum_eq_momentSum]
  unfold engelsmaNaturalQuadraticScale engelsmaMaynardScale
    maynardSieveScale
  rw [preSieveSingularSeries_eq_totient_div]
  unfold engelsmaMaynardModulus
  have hWprim : (0 : ℝ) < primorial (tripleLogCutoff (N - 1)) := by
    exact_mod_cast primorial_pos (tripleLogCutoff (N - 1))
  have hphiprim : (0 : ℝ) <
      Nat.totient (primorial (tripleLogCutoff (N - 1))) := by
    exact_mod_cast Nat.totient_pos.mpr
      (primorial_pos (tripleLogCutoff (N - 1)))
  field_simp [hNpos.ne', hW.ne', hphi.ne', hWprim.ne', hphiprim.ne',
    hLnat.ne', hLreal.ne']
  ring_nf

set_option maxRecDepth 10000 in
theorem tendsto_normalizedEngelsmaIndependentQuadraticMoment
    {alpha : ℝ} (halpha : 0 < alpha) (b c : ℕ) :
    Tendsto (fun N : ℕ =>
      normalizedEngelsmaIndependentQuadraticMoment alpha N b c)
      atTop (nhds (∫ x in maynardSimplex 105,
        simplexQuadraticIntegrand 105 b c x)) := by
  have hnatural := tendsto_normalizedEngelsmaIndependentQuadraticNatural
    halpha b c
  have hratio := (tendsto_log_engelsmaMaynardRadius_div_realRadius halpha).pow 105
  have hmul := hnatural.mul hratio
  have htarget : Tendsto (fun N : ℕ =>
      normalizedEngelsmaIndependentQuadraticNatural alpha N b c *
        (Real.log (engelsmaMaynardRadius alpha N) /
          Real.log (engelsmaMaynardRealRadius alpha N)) ^ 105)
      atTop (nhds (∫ x in maynardSimplex 105,
        simplexQuadraticIntegrand 105 b c x)) := by
    simpa using hmul
  apply htarget.congr'
  filter_upwards [eventually_normalizedIndependent_eq_natural_mul_logRatio
      halpha b c] with N hN
  exact hN.symm

end BoundedGaps.Maynard
