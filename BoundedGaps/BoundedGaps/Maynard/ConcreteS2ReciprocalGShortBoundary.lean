import BoundedGaps.Maynard.ConcreteS2ReciprocalGBoundaryMass
import BoundedGaps.Maynard.ConcreteS2CoordinateOneEndpointSplit
import BoundedGaps.Maynard.MaynardS2CoordinateFiberShortEndpoint
import BoundedGaps.Maynard.ConcreteS2GoodSupportSumReindex
import BoundedGaps.Maynard.ConcreteS2OffFaceGoodEndpointShell
import BoundedGaps.Maynard.MaynardS2GPositivity

noncomputable section

namespace BoundedGaps.Maynard

open Filter Set
open scoped BigOperators

def engelsmaS2OffFaceShortSupport
    (R D : ℕ) (m : BoundedGaps.engelsmaTuple) :
    Finset (engelsmaOffFaceFinset m → ℕ) :=
  (maynardDivisorTupleSupport
      (engelsmaOffFaceFinset m) R (primorial D)).filter fun u =>
    ¬1 < maynardS2CoordinateFiberEndpoint R
      (divisorTupleProduct (engelsmaOffFaceFinset m) u)

def engelsmaS2OffFaceShortReciprocalGMass
    (R D : ℕ) (m : BoundedGaps.engelsmaTuple) : ℝ :=
  ∑ u ∈ engelsmaS2OffFaceShortSupport R D m,
    ∏ h : engelsmaOffFaceFinset m,
      maynardS2ReciprocalGSquarefreeAF (primorial D) (u h)

theorem mem_engelsmaS2OffFaceShortSupport_iff
    {R D : ℕ} {m : BoundedGaps.engelsmaTuple}
    {u : engelsmaOffFaceFinset m → ℕ} :
    u ∈ engelsmaS2OffFaceShortSupport R D m ↔
      u ∈ maynardDivisorTupleSupport
          (engelsmaOffFaceFinset m) R (primorial D) ∧
        ¬1 < maynardS2CoordinateFiberEndpoint R
          (divisorTupleProduct (engelsmaOffFaceFinset m) u) := by
  exact Finset.mem_filter

set_option maxRecDepth 6000 in
theorem sum_engelsmaS2CoordinateFiberShortSupport_eq_offFace
    (R D : ℕ) (m : BoundedGaps.engelsmaTuple)
    (F : (BoundedGaps.engelsmaTuple → ℕ) → ℝ) :
    (∑ r ∈ engelsmaS2CoordinateFiberShortSupport R D m, F r) =
      ∑ u ∈ engelsmaS2OffFaceShortSupport R D m,
        F (engelsmaOffFaceExtension m u) := by
  apply Finset.sum_bij (fun r _ => engelsmaOffFaceRestriction m r)
  · intro r hr
    have hrData := Finset.mem_filter.mp hr
    have hrm : r m = 1 := hrData.2.1
    apply mem_engelsmaS2OffFaceShortSupport_iff.mpr
    have hext := engelsmaOffFaceExtension_restriction m r hrm
    have hoff0 := maynardS2OffCoordinateProduct_engelsmaOffFaceExtension_eq m
      (engelsmaOffFaceRestriction m r)
    have hoff : maynardS2OffCoordinateProduct BoundedGaps.engelsmaTuple m r =
        divisorTupleProduct (engelsmaOffFaceFinset m)
          (engelsmaOffFaceRestriction m r) := by
      simpa only [hext] using hoff0
    constructor
    · exact (engelsmaOffFaceExtension_mem_maynardDivisorTupleSupport_iff
        R (primorial D) m (engelsmaOffFaceRestriction m r)).mp
        (by simpa [hext] using hrData.1)
    · have hshort := hrData.2.2
      rw [hoff] at hshort
      exact hshort
  · intro r hr s hs hEq
    calc
      r = engelsmaOffFaceExtension m (engelsmaOffFaceRestriction m r) :=
        (engelsmaOffFaceExtension_restriction m r
          (Finset.mem_filter.mp hr).2.1).symm
      _ = engelsmaOffFaceExtension m (engelsmaOffFaceRestriction m s) := by
        rw [hEq]
      _ = s := engelsmaOffFaceExtension_restriction m s
        (Finset.mem_filter.mp hs).2.1
  · intro u hu
    let r := engelsmaOffFaceExtension m u
    have hr : r ∈ engelsmaS2CoordinateFiberShortSupport R D m := by
      rw [engelsmaS2CoordinateFiberShortSupport]
      apply Finset.mem_filter.mpr
      refine ⟨(engelsmaOffFaceExtension_mem_maynardDivisorTupleSupport_iff
        R (primorial D) m u).mpr (Finset.mem_filter.mp hu).1, ?_, ?_⟩
      · exact engelsmaOffFaceExtension_at m u
      · exact maynardS2OffCoordinateProduct_engelsmaOffFaceExtension_eq m u ▸
          (Finset.mem_filter.mp hu).2
    refine ⟨r, hr, ?_⟩
    exact engelsmaOffFaceRestriction_extension m u
  · intro r hr
    exact congrArg F (engelsmaOffFaceExtension_restriction m r
      (Finset.mem_filter.mp hr).2.1).symm

set_option maxRecDepth 8000 in
set_option maxHeartbeats 800000 in
theorem reciprocalG_full_weight_eq_offFace_product
    {R D : ℕ} (m : BoundedGaps.engelsmaTuple)
    {u : engelsmaOffFaceFinset m → ℕ}
    (hu : u ∈ maynardDivisorTupleSupport
      (engelsmaOffFaceFinset m) R (primorial D)) :
    1 / |∏ h : BoundedGaps.engelsmaTuple,
        (maynardS2G (engelsmaOffFaceExtension m u h) : ℝ)| =
      ∏ h : engelsmaOffFaceFinset m,
        maynardS2ReciprocalGSquarefreeAF (primorial D) (u h) := by
  have hrOff := isMaynardDivisorTuple_of_mem_support hu
  have hrFull : IsMaynardDivisorTuple BoundedGaps.engelsmaTuple R
      (primorial D) (engelsmaOffFaceExtension m u) :=
    (isMaynardDivisorTuple_engelsmaOffFaceExtension_iff R
      (primorial D) m u).mpr hrOff
  have hgFull := maynardS2G_divisorTupleProduct_eq_prod hrFull
  have hgOff := maynardS2G_divisorTupleProduct_eq_prod hrOff
  have hprod : (∏ h : BoundedGaps.engelsmaTuple,
      (maynardS2G (engelsmaOffFaceExtension m u h) : ℝ)) =
      ∏ h : engelsmaOffFaceFinset m, (maynardS2G (u h) : ℝ) := by
    calc
      (∏ h : BoundedGaps.engelsmaTuple,
          (maynardS2G (engelsmaOffFaceExtension m u h) : ℝ)) =
          (maynardS2G (divisorTupleProduct BoundedGaps.engelsmaTuple
            (engelsmaOffFaceExtension m u)) : ℝ) := by
            exact_mod_cast hgFull.symm
      _ = (maynardS2G (divisorTupleProduct
          (engelsmaOffFaceFinset m) u) : ℝ) := by
            rw [divisorTupleProduct_engelsmaOffFaceExtension_eq]
      _ = ∏ h : engelsmaOffFaceFinset m, (maynardS2G (u h) : ℝ) := by
            exact_mod_cast hgOff
  have hfactor : ∀ h : engelsmaOffFaceFinset m,
      maynardS2ReciprocalGSquarefreeAF (primorial D) (u h) =
        1 / (maynardS2G (u h) : ℝ) := by
    intro h
    exact maynardS2ReciprocalGSquarefreeAF_apply_squarefree_of_coprime
      (hrOff.coordinate_squarefree h) (hrOff.coordinate_coprime_W h)
  have hprodNonneg : 0 ≤ ∏ h : engelsmaOffFaceFinset m,
      (maynardS2G (u h) : ℝ) := by
    apply Finset.prod_nonneg
    intro h hh
    exact_mod_cast Nat.zero_le (maynardS2G (u h))
  rw [hprod, abs_of_nonneg hprodNonneg]
  rw [show (∏ h : engelsmaOffFaceFinset m,
      maynardS2ReciprocalGSquarefreeAF (primorial D) (u h)) =
      ∏ h : engelsmaOffFaceFinset m, (1 / (maynardS2G (u h) : ℝ)) by
        apply Finset.prod_congr rfl
        intro h hh
        exact hfactor h]
  rw [Finset.prod_div_distrib]
  simp

set_option maxRecDepth 8000 in
theorem engelsmaS2CoordinateFiberShortReciprocalGMass_eq_offFace
    (R D : ℕ) (m : BoundedGaps.engelsmaTuple) :
    engelsmaS2CoordinateFiberShortReciprocalGMass R D m =
      engelsmaS2OffFaceShortReciprocalGMass R D m := by
  unfold engelsmaS2CoordinateFiberShortReciprocalGMass
    engelsmaS2OffFaceShortReciprocalGMass
  rw [sum_engelsmaS2CoordinateFiberShortSupport_eq_offFace]
  apply Finset.sum_congr rfl
  intro u hu
  exact reciprocalG_full_weight_eq_offFace_product m
    (Finset.mem_filter.mp hu).1

set_option maxRecDepth 10000 in
theorem eventually_engelsmaS2OffFaceShortSupport_subset_boundary_or_unit
    {alpha : ℝ} (halpha : 0 < alpha)
    (m : BoundedGaps.engelsmaTuple) {mesh : ℕ} (hmesh : 0 < mesh) :
    ∀ᶠ N : ℕ in atTop,
      engelsmaS2OffFaceShortSupport
          (engelsmaMaynardRadius alpha N)
          (tripleLogCutoff (N - 1)) m ⊆
        engelsmaSimplexBoundaryGridShellUnion
          (engelsmaOffFaceFinset m) alpha mesh N ∪
          engelsmaUnitBoundaryBoxUnion
            (engelsmaOffFaceFinset m) alpha N := by
  let H := engelsmaOffFaceFinset m
  have hcover := eventually_preSievedSimplexTupleSupport_mem_inner_or_boundaryShell
    (H := H) halpha hmesh
  have hgood := eventually_engelsmaS2OffFaceInnerShell_endpoint_good
    halpha m hmesh
  filter_upwards [hcover, hgood] with N hcoverN hgoodN u huShort
  have huSupport := (Finset.mem_filter.mp huShort).1
  have huPre : u ∈ preSievedSimplexTupleSupport H
      (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N) := by
    have huSupport' : u ∈
        (preSievedSimplexTupleSupport H
          (engelsmaMaynardRadius alpha N)
          (primorial (tripleLogCutoff (N - 1)))).filter fun v =>
            Squarefree (divisorTupleProduct H v) := by
      simpa only [← maynardDivisorTupleSupport_eq_preSievedSimplex_filter]
        using huSupport
    have huPre' := (Finset.mem_filter.mp huSupport').1
    simpa [H, engelsmaMaynardModulus] using huPre'
  by_cases hunit : ∃ h : H, u h = 1
  · exact Finset.mem_union.mpr (Or.inr
      (preSievedSimplexUnitBoundary_subset_boxUnion huPre hunit))
  · have hnoUnit : ∀ h : H, u h ≠ 1 := not_exists.mp hunit
    rcases hcoverN u huPre hnoUnit with huInner | huBoundary
    · exfalso
      rw [engelsmaSimplexInnerGridSupport] at huInner
      obtain ⟨j, hj, huShell⟩ := Finset.mem_biUnion.mp huInner
      have hEnd := hgoodN j hj u huShell
      exact (Finset.mem_filter.mp huShort).2 hEnd
    · exact Finset.mem_union.mpr (Or.inl huBoundary)

set_option maxRecDepth 8000 in
theorem engelsmaS2OffFaceShortReciprocalGMass_le_boundary_unit
    {alpha : ℝ} (halpha : 0 < alpha)
    (m : BoundedGaps.engelsmaTuple) {mesh : ℕ} (hmesh : 0 < mesh) :
    ∀ᶠ N : ℕ in atTop,
      engelsmaS2OffFaceShortReciprocalGMass
          (engelsmaMaynardRadius alpha N)
          (tripleLogCutoff (N - 1)) m ≤
        engelsmaS2ReciprocalGBoundaryGridSupportMass alpha m mesh N +
          engelsmaS2ReciprocalGUnitBoundaryBoxUnionMass
            (engelsmaOffFaceFinset m) alpha N := by
  filter_upwards [eventually_engelsmaS2OffFaceShortSupport_subset_boundary_or_unit
    halpha m hmesh] with N hsubset
  let H := engelsmaOffFaceFinset m
  let D := tripleLogCutoff (N - 1)
  let W := primorial D
  let f : (H → ℕ) → ℝ := fun u =>
    ∏ h : H, maynardS2ReciprocalGSquarefreeAF W (u h)
  have hshort : (∑ u ∈ engelsmaS2OffFaceShortSupport
      (engelsmaMaynardRadius alpha N) D m, f u) ≤
      ∑ u ∈ engelsmaSimplexBoundaryGridShellUnion H alpha mesh N ∪
        engelsmaUnitBoundaryBoxUnion H alpha N, f u := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro u hu hnot
    exact Finset.prod_nonneg (fun h hh =>
      maynardS2ReciprocalGSquarefreeAF_nonneg _ _)
  have hunion := Finset.sum_union_inter
    (s₁ := engelsmaSimplexBoundaryGridShellUnion
      (engelsmaOffFaceFinset m) alpha mesh N)
    (s₂ := engelsmaUnitBoundaryBoxUnion
      (engelsmaOffFaceFinset m) alpha N)
    (f := f)
  have hinter : 0 ≤ ∑ u ∈
      (engelsmaSimplexBoundaryGridShellUnion
        (engelsmaOffFaceFinset m) alpha mesh N) ∩
      engelsmaUnitBoundaryBoxUnion (engelsmaOffFaceFinset m) alpha N,
      ∏ h : engelsmaOffFaceFinset m,
        maynardS2ReciprocalGSquarefreeAF W (u h) := by
    apply Finset.sum_nonneg
    intro u hu
    apply Finset.prod_nonneg
    intro h hh
    exact maynardS2ReciprocalGSquarefreeAF_nonneg _ _
  have hU : (∑ u ∈ engelsmaSimplexBoundaryGridShellUnion H alpha mesh N ∪
      engelsmaUnitBoundaryBoxUnion H alpha N, f u) ≤
      ∑ u ∈ engelsmaSimplexBoundaryGridShellUnion H alpha mesh N, f u +
        ∑ u ∈ engelsmaUnitBoundaryBoxUnion H alpha N, f u := by
    linarith
  calc
    engelsmaS2OffFaceShortReciprocalGMass
        (engelsmaMaynardRadius alpha N) D m =
        ∑ u ∈ engelsmaS2OffFaceShortSupport
          (engelsmaMaynardRadius alpha N) D m, f u := by
            rfl
    _ ≤ ∑ u ∈ engelsmaSimplexBoundaryGridShellUnion H alpha mesh N ∪
        engelsmaUnitBoundaryBoxUnion H alpha N, f u := hshort
    _ ≤ _ := hU

def normalizedEngelsmaS2CoordinateFiberShortReciprocalGMass
    (alpha : ℝ) (N : ℕ) (m : BoundedGaps.engelsmaTuple) : ℝ :=
  engelsmaS2CoordinateFiberShortReciprocalGMass
      (engelsmaMaynardRadius alpha N) (tripleLogCutoff (N - 1)) m /
    (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
      Real.log (engelsmaMaynardRadius alpha N)) ^
        Fintype.card (engelsmaOffFaceFinset m)

set_option maxRecDepth 8000 in
theorem eventually_normalizedEngelsmaS2CoordinateFiberShortReciprocalGMass_le_boundary_unit
    {alpha : ℝ} (halpha : 0 < alpha)
    (m : BoundedGaps.engelsmaTuple) {mesh : ℕ} (hmesh : 0 < mesh) :
    ∀ᶠ N : ℕ in atTop,
      normalizedEngelsmaS2CoordinateFiberShortReciprocalGMass alpha N m ≤
        normalizedEngelsmaS2ReciprocalGBoundaryGridSupportMass
            alpha m mesh N +
          normalizedEngelsmaS2ReciprocalGUnitBoundaryBoxUnionMass
            (engelsmaOffFaceFinset m) alpha N := by
  have hmass := engelsmaS2OffFaceShortReciprocalGMass_le_boundary_unit
    halpha m hmesh
  have hscale := eventually_engelsmaS2OffFaceNaturalScale_pos halpha m
  filter_upwards [hmass, hscale] with N hmassN hscaleN
  unfold normalizedEngelsmaS2CoordinateFiberShortReciprocalGMass
    normalizedEngelsmaS2ReciprocalGBoundaryGridSupportMass
    normalizedEngelsmaS2ReciprocalGUnitBoundaryBoxUnionMass
  rw [engelsmaS2CoordinateFiberShortReciprocalGMass_eq_offFace]
  rw [← add_div]
  exact div_le_div_of_nonneg_right hmassN hscaleN.le

set_option maxRecDepth 8000 in
theorem eventually_normalizedEngelsmaS2CoordinateFiberShortReciprocalGMass_nonneg
    {alpha : ℝ} (halpha : 0 < alpha)
    (m : BoundedGaps.engelsmaTuple) :
    ∀ᶠ N : ℕ in atTop,
      0 ≤ normalizedEngelsmaS2CoordinateFiberShortReciprocalGMass alpha N m := by
  filter_upwards [eventually_engelsmaS2OffFaceNaturalScale_pos halpha m] with
      N hscale
  unfold normalizedEngelsmaS2CoordinateFiberShortReciprocalGMass
    engelsmaS2CoordinateFiberShortReciprocalGMass
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro r hr
    positivity
  · exact hscale.le

set_option maxRecDepth 9000 in
theorem tendsto_normalizedEngelsmaS2CoordinateFiberShortReciprocalGMass_zero
    {alpha : ℝ} (halpha : 0 < alpha)
    (m : BoundedGaps.engelsmaTuple) :
    Tendsto (fun N : ℕ =>
      normalizedEngelsmaS2CoordinateFiberShortReciprocalGMass alpha N m)
      atTop (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  have he4 : 0 < epsilon / 4 := by linarith
  have hvolT := tendsto_simplexBoundaryGridVolume_engelsmaS2OffFace_zero m
  have hmeshEvent : ∀ᶠ mesh : ℕ in atTop,
      0 < mesh ∧ simplexBoundaryGridVolume
        (engelsmaOffFaceFinset m) mesh < epsilon / 4 := by
    filter_upwards [eventually_gt_atTop 0,
      hvolT.eventually (Iio_mem_nhds he4)] with mesh hmesh hvol
    exact ⟨hmesh, by simpa using hvol⟩
  rw [eventually_atTop] at hmeshEvent
  obtain ⟨M, hM⟩ := hmeshEvent
  have hmeshData := hM M le_rfl
  let mesh := M
  have hmesh : 0 < mesh := by simpa [mesh] using hmeshData.1
  have hvol : simplexBoundaryGridVolume
      (engelsmaOffFaceFinset m) mesh < epsilon / 4 := by
    simpa [mesh] using hmeshData.2
  have hboundaryT :=
    tendsto_normalizedEngelsmaS2ReciprocalGBoundaryGridSupportMass
      halpha m hmesh
  have hboundary : ∀ᶠ N : ℕ in atTop,
      |normalizedEngelsmaS2ReciprocalGBoundaryGridSupportMass
          alpha m mesh N -
        simplexBoundaryGridVolume (engelsmaOffFaceFinset m) mesh| <
          epsilon / 4 := by
    filter_upwards [hboundaryT.eventually (Metric.ball_mem_nhds _ he4)] with
      N hN
    simpa [Real.dist_eq] using hN
  have hunitT :=
    tendsto_normalizedEngelsmaS2ReciprocalGUnitBoundaryBoxUnionMass_zero
      (H := engelsmaOffFaceFinset m) halpha
  have hunit : ∀ᶠ N : ℕ in atTop,
      |normalizedEngelsmaS2ReciprocalGUnitBoundaryBoxUnionMass
          (engelsmaOffFaceFinset m) alpha N| < epsilon / 4 := by
    filter_upwards [hunitT.eventually (Metric.ball_mem_nhds _ he4)] with N hN
    simpa [Real.dist_eq] using hN
  have hbound :=
    eventually_normalizedEngelsmaS2CoordinateFiberShortReciprocalGMass_le_boundary_unit
      halpha m hmesh
  have hnonneg :=
    eventually_normalizedEngelsmaS2CoordinateFiberShortReciprocalGMass_nonneg
      halpha m
  filter_upwards [hboundary, hunit, hbound, hnonneg] with
      N hboundaryN hunitN hboundN hnonnegN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonnegN]
  have hboundaryLe :
      normalizedEngelsmaS2ReciprocalGBoundaryGridSupportMass
          alpha m mesh N < epsilon / 2 := by
    have hle := le_abs_self
      (normalizedEngelsmaS2ReciprocalGBoundaryGridSupportMass
        alpha m mesh N -
          simplexBoundaryGridVolume (engelsmaOffFaceFinset m) mesh)
    linarith
  have hunitLe :
      normalizedEngelsmaS2ReciprocalGUnitBoundaryBoxUnionMass
          (engelsmaOffFaceFinset m) alpha N < epsilon / 4 :=
    (le_abs_self _).trans_lt hunitN
  linarith

set_option maxRecDepth 9000 in
theorem tendsto_normalizedEngelsmaS2CoordinateFiberShortSquareDiagonal_zero
    {alpha : ℝ} (halpha : 0 < alpha)
    (m : BoundedGaps.engelsmaTuple) :
    Tendsto (fun N : ℕ =>
      engelsmaS2CoordinateFiberShortSquareDiagonal
        (engelsmaMaynardRadius alpha N) (tripleLogCutoff (N - 1)) m /
      (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
        Real.log (engelsmaMaynardRadius alpha N)) ^
          Fintype.card (engelsmaOffFaceFinset m)) atTop (nhds 0) := by
  have hmass := tendsto_normalizedEngelsmaS2CoordinateFiberShortReciprocalGMass_zero
    halpha m
  have henv := hmass.const_mul (smallKCandidateBound ^ 2)
  have henv0 : Tendsto (fun N : ℕ =>
      smallKCandidateBound ^ 2 *
        normalizedEngelsmaS2CoordinateFiberShortReciprocalGMass alpha N m)
      atTop (nhds 0) := by
    simpa using henv
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun N => abs_nonneg _) ?_ henv0
  filter_upwards [
    eventually_engelsmaS2OffFaceNaturalScale_pos halpha m] with N hscale
  let R := engelsmaMaynardRadius alpha N
  let D := tripleLogCutoff (N - 1)
  let Q := (preSieveSingularSeries D *
    Real.log (engelsmaMaynardRadius alpha N)) ^
      Fintype.card (engelsmaOffFaceFinset m)
  have hQ : 0 < Q := by
    dsimp [Q]
    positivity
  have hdiag := abs_engelsmaS2CoordinateFiberShortSquareDiagonal_le_reciprocalGMass
    R D m
  change |engelsmaS2CoordinateFiberShortSquareDiagonal R D m / Q| ≤
    smallKCandidateBound ^ 2 *
      (engelsmaS2CoordinateFiberShortReciprocalGMass R D m / Q)
  rw [abs_div, abs_of_pos hQ]
  calc
    |engelsmaS2CoordinateFiberShortSquareDiagonal R D m| / Q ≤
        (smallKCandidateBound ^ 2 *
          engelsmaS2CoordinateFiberShortReciprocalGMass R D m) / Q :=
      div_le_div_of_nonneg_right hdiag hQ.le
    _ = smallKCandidateBound ^ 2 *
        (engelsmaS2CoordinateFiberShortReciprocalGMass R D m / Q) := by
      ring

end BoundedGaps.Maynard
