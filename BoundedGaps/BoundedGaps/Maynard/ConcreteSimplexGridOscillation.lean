import BoundedGaps.Maynard.ConcreteSimplexBoundaryMesh
import BoundedGaps.Maynard.MaynardYDiagonalCollisionWeight

noncomputable section
namespace BoundedGaps.Maynard
open Filter Set
open scoped BigOperators

theorem eventually_coordinateShell_normalizedLog_mem
    {alpha beta gamma delta : ℝ} (halpha : 0 < alpha)
    (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma) (hdelta : 0 < delta) :
    ∀ᶠ N : ℕ in atTop, ∀ n : ℕ,
      n ∈ squarefreeCoprimeCoordinateShell
          (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius (alpha * beta) N)
          (engelsmaMaynardRadius (alpha * gamma) N) →
      beta - delta < Real.log n /
          Real.log (engelsmaMaynardRadius alpha N) ∧
        Real.log n / Real.log (engelsmaMaynardRadius alpha N) <
          gamma + delta := by
  have hupper := eventually_log_ratio_lt_of_nat_le_engelsmaMaynardRadius
    halpha hgamma (lt_add_of_pos_right gamma hdelta)
  have hR := eventually_one_lt_engelsmaMaynardRadius halpha
  by_cases hbeta0 : beta = 0
  · filter_upwards [hupper, hR] with N hupperN hRN n hn
    have hnUpper := Finset.mem_sdiff.mp hn |>.1
    have hnUpperData := Finset.mem_filter.mp hnUpper
    have hnIcc := Finset.mem_Icc.mp hnUpperData.1
    have hnPos : 0 < n := zero_lt_one.trans_le hnIcc.1
    have hnLe : n ≤ engelsmaMaynardRadius (alpha * gamma) N := hnIcc.2
    have hlogNonneg : 0 ≤ Real.log n :=
      Real.log_nonneg (by exact_mod_cast hnIcc.1)
    have hden : 0 < Real.log (engelsmaMaynardRadius alpha N) :=
      Real.log_pos (by exact_mod_cast hRN)
    constructor
    · rw [hbeta0]
      have hratioNonneg : 0 ≤ Real.log n /
          Real.log (engelsmaMaynardRadius alpha N) :=
        div_nonneg hlogNonneg hden.le
      linarith
    · exact hupperN n hnPos hnLe
  · have hbetaPos : 0 < beta := lt_of_le_of_ne hbeta (Ne.symm hbeta0)
    let beta' : ℝ := max 0 (beta - delta)
    have hbeta' : 0 ≤ beta' := le_max_left _ _
    have hbeta'Lt : beta' < beta := by
      dsimp [beta']
      exact max_lt hbetaPos (sub_lt_self beta hdelta)
    have hlower := eventually_nat_le_engelsmaMaynardRadius_of_log_ratio_le
      halpha hbeta' hbeta'Lt
    filter_upwards [hlower, hupper, hR] with N hlowerN hupperN hRN n hn
    have hnData := Finset.mem_sdiff.mp hn
    have hnUpperData := Finset.mem_filter.mp hnData.1
    have hnIcc := Finset.mem_Icc.mp hnUpperData.1
    have hnPos : 0 < n := zero_lt_one.trans_le hnIcc.1
    have hnLe : n ≤ engelsmaMaynardRadius (alpha * gamma) N := hnIcc.2
    have hnGt : engelsmaMaynardRadius (alpha * beta) N < n := by
      by_contra hnot
      apply hnData.2
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_Icc.mpr ⟨hnIcc.1, Nat.le_of_not_gt hnot⟩,
        hnUpperData.2⟩
    have hratioLower : beta' < Real.log n /
        Real.log (engelsmaMaynardRadius alpha N) := by
      by_contra hnot
      have := hlowerN n hnPos (le_of_not_gt hnot)
      omega
    constructor
    · exact lt_of_le_of_lt (le_max_right 0 (beta - delta)) hratioLower
    · exact hupperN n hnPos hnLe

theorem fractionalGridUpper_eq_lower_add_inv
    {H : Finset ℕ} {m : ℕ} (hm : 0 < m) (j : H → ℕ) (h : H) :
    fractionalGridUpper m j h =
      fractionalGridLower m j h + (1 : ℝ) / m := by
  unfold fractionalGridUpper fractionalGridLower
  have hmReal : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp [hmReal]
  push_cast
  ring

theorem eventually_fractionalGridShell_normalizedLog_close
    {H : Finset ℕ} {alpha : ℝ} {m : ℕ}
    (halpha : 0 < alpha) (hm : 0 < m) :
    ∀ᶠ N : ℕ in atTop, ∀ j ∈ fractionalGridIndex H m,
      ∀ u ∈ engelsmaFractionalTupleShell H alpha
        (fractionalGridLower m j) (fractionalGridUpper m j) N,
      ∀ h : H,
        |Real.log (u h) / Real.log (engelsmaMaynardRadius alpha N) -
            fractionalGridLower m j h| < (2 : ℝ) / m := by
  let I := fractionalGridIndex H m
  have hcell : ∀ j ∈ I, ∀ h : H,
      ∀ᶠ N : ℕ in atTop, ∀ n : ℕ,
        n ∈ squarefreeCoprimeCoordinateShell
          (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius
            (alpha * fractionalGridLower m j h) N)
          (engelsmaMaynardRadius
            (alpha * fractionalGridUpper m j h) N) →
        fractionalGridLower m j h - (1 : ℝ) / m <
            Real.log n / Real.log (engelsmaMaynardRadius alpha N) ∧
          Real.log n / Real.log (engelsmaMaynardRadius alpha N) <
            fractionalGridUpper m j h + (1 : ℝ) / m := by
    intro j hj h
    have hendpoints := fractionalGridEndpoints_mem_Icc hm hj h
    exact eventually_coordinateShell_normalizedLog_mem halpha
      hendpoints.1.1 hendpoints.2.1.1 (by positivity)
  have hcells : ∀ᶠ N : ℕ in atTop, ∀ j ∈ I, ∀ h : H, ∀ n : ℕ,
      n ∈ squarefreeCoprimeCoordinateShell
          (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius
            (alpha * fractionalGridLower m j h) N)
          (engelsmaMaynardRadius
            (alpha * fractionalGridUpper m j h) N) →
        fractionalGridLower m j h - (1 : ℝ) / m <
            Real.log n / Real.log (engelsmaMaynardRadius alpha N) ∧
          Real.log n / Real.log (engelsmaMaynardRadius alpha N) <
            fractionalGridUpper m j h + (1 : ℝ) / m := by
    have hjAll := I.eventually_all.mpr fun j hj =>
      (Finset.univ : Finset H).eventually_all.mpr fun h hh => hcell j hj h
    filter_upwards [hjAll] with N hN j hj h n hn
    exact hN j hj h (Finset.mem_univ h) n hn
  filter_upwards [hcells] with N hN j hj u hu h
  have huShell : u ∈ squarefreeCoprimeTupleShell H
      (engelsmaMaynardModulus N)
      (fun h => engelsmaMaynardRadius
        (alpha * fractionalGridLower m j h) N)
      (fun h => engelsmaMaynardRadius
        (alpha * fractionalGridUpper m j h) N) := by
    simpa [engelsmaFractionalTupleShell] using hu
  have hcoord := Fintype.mem_piFinset.mp huShell h
  have hbounds := hN j hj h (u h) hcoord
  have hwidth := fractionalGridUpper_eq_lower_add_inv hm j h
  rw [hwidth] at hbounds
  have htwo : (2 : ℝ) / m = (1 : ℝ) / m + 1 / m := by ring
  rw [htwo]
  apply abs_lt.mpr
  constructor <;> linarith [show (0 : ℝ) < 1 / m by positivity]

theorem continuous_simplexQuadraticIntegrand (k b c : ℕ) :
    Continuous (simplexQuadraticIntegrand k b c) := by
  unfold simplexQuadraticIntegrand
  fun_prop

theorem isCompact_maynardCube (k : ℕ) : IsCompact (maynardCube k) := by
  unfold maynardCube maynardCubeOf
  exact isCompact_univ_pi fun _ => isCompact_Icc

theorem uniformContinuousOn_simplexQuadraticIntegrand_cube (k b c : ℕ) :
    UniformContinuousOn (simplexQuadraticIntegrand k b c) (maynardCube k) :=
  (isCompact_maynardCube k).uniformContinuousOn_of_continuous
    (continuous_simplexQuadraticIntegrand k b c).continuousOn

def engelsmaGridLowerPoint
    (m : ℕ) (j : BoundedGaps.engelsmaTuple → ℕ) : Fin 105 → ℝ :=
  fun i => fractionalGridLower m j (engelsmaIndexEquiv.symm i)

def engelsmaNormalizedLogPoint
    (alpha : ℝ) (N : ℕ) (u : BoundedGaps.engelsmaTuple → ℕ) :
    Fin 105 → ℝ :=
  fun i => normalizedDivisorLogTuple BoundedGaps.engelsmaTuple
    (engelsmaMaynardRadius alpha N) u (engelsmaIndexEquiv.symm i)

set_option maxRecDepth 10000 in
theorem engelsmaGridLowerPoint_mem_cube
    {m : ℕ} (hm : 0 < m)
    {j : BoundedGaps.engelsmaTuple → ℕ}
    (hj : j ∈ fractionalGridIndex BoundedGaps.engelsmaTuple m) :
    engelsmaGridLowerPoint m j ∈ maynardCube 105 := by
  rw [maynardCube, maynardCubeOf, Set.mem_pi]
  intro i hi
  exact (fractionalGridEndpoints_mem_Icc hm hj
    (engelsmaIndexEquiv.symm i)).1

set_option maxRecDepth 10000 in
theorem exists_mesh_eventually_innerGridShell_quadratic_oscillation
    {alpha : ℝ} (halpha : 0 < alpha) (b c : ℕ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ m : ℕ, 0 < m ∧
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
  let m := max m0 1
  have hm : 0 < m := by dsimp [m]; omega
  have hmesh : (2 : ℝ) / m < delta := hm0 m (by simp [m])
  refine ⟨m, hm, ?_⟩
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

end BoundedGaps.Maynard
