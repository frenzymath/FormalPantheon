import BoundedGaps.Maynard.ConcreteS2OffFaceGoodMomentCore

noncomputable section

namespace BoundedGaps.Maynard

open Filter Set
open scoped BigOperators

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1200000 in
theorem eventually_engelsmaS2OffFaceGoodQuadraticMoment_sub_inner_bounds
    {alpha : ℝ} (halpha : 0 < alpha)
    (m : BoundedGaps.engelsmaTuple)
    {mesh : ℕ} (hmesh : 0 < mesh) (b c : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      -normalizedEngelsmaS2OffFaceCollisionOuterMass alpha m N ≤
          normalizedEngelsmaS2OffFaceGoodQuadraticMoment alpha N m b c -
            normalizedEngelsmaS2OffFaceInnerGridQuadraticCellSum
              alpha m mesh N b c ∧
        normalizedEngelsmaS2OffFaceGoodQuadraticMoment alpha N m b c -
            normalizedEngelsmaS2OffFaceInnerGridQuadraticCellSum
              alpha m mesh N b c ≤
          normalizedEngelsmaS2OffFaceBoundaryGridSupportMass
              alpha m mesh N +
            normalizedEngelsmaS2OuterUnitBoundaryBoxUnionMass
              (engelsmaOffFaceFinset m) alpha N := by
  let H := engelsmaOffFaceFinset m
  have hsubset := eventually_engelsmaSimplexInnerGridSupport_subset
    (H := H) halpha hmesh
  have hcover := eventually_preSievedSimplexTupleSupport_mem_inner_or_boundaryShell
    (H := H) halpha hmesh
  have hgood := eventually_engelsmaS2OffFaceInnerShell_endpoint_good
    halpha m hmesh
  have hdis := eventually_engelsmaFractionalGridShells_pairwise_disjoint
    (H := H) halpha hmesh
  have hscale := eventually_engelsmaS2OffFaceNaturalScale_pos halpha m
  have hR := eventually_one_lt_engelsmaMaynardRadius halpha
  filter_upwards [hsubset, hcover, hgood, hdis, hscale, hR] with
      N hsubsetN hcoverN hgoodN hdisN hscaleN hRN0
  let R := engelsmaMaynardRadius alpha N
  let D := tripleLogCutoff (N - 1)
  let W := engelsmaMaynardModulus N
  let S := preSievedSimplexTupleSupport H R W
  let A := engelsmaSimplexInnerGridSupport H alpha mesh N
  let G := engelsmaS2OffFaceGoodSupport R D m
  let C := preSievedSimplexCollisionSupport H R W
  let B := engelsmaSimplexBoundaryGridShellUnion H alpha mesh N
  let U := engelsmaUnitBoundaryBoxUnion H alpha N
  let g : (H → ℕ) → ℝ := fun u =>
    engelsmaS2OffFaceQuadraticIntegrand m b c
      (engelsmaS2OffFaceNormalizedLogPoint alpha N m u) *
      outerTupleWeight H W u
  let w : (H → ℕ) → ℝ := fun u => outerTupleWeight H W u
  have hRN : 1 < R := by simpa [R] using hRN0
  have hW : W = primorial D := by
    simp [W, D, engelsmaMaynardModulus]
  have hMaynardSubset : G ⊆ S := by
    intro u hu
    have huData := mem_engelsmaS2OffFaceGoodSupport_iff.mp hu
    have huSupport : u ∈ maynardDivisorTupleSupport H R (primorial D) :=
      huData.1
    have huSupport' : u ∈
        (preSievedSimplexTupleSupport H R (primorial D)).filter fun v =>
          Squarefree (divisorTupleProduct H v) := by
      simpa only [← maynardDivisorTupleSupport_eq_preSievedSimplex_filter]
        using huSupport
    have huPre := (Finset.mem_filter.mp huSupport').1
    simpa [S, W, hW] using huPre
  have hAgood : A \ G ⊆ C := by
    intro u hu
    have huData := Finset.mem_sdiff.mp hu
    have huPre : u ∈ S := hsubsetN huData.1
    have huShell : ∃ j ∈ fractionalSimplexInnerGridIndex H mesh,
        u ∈ engelsmaFractionalTupleShell H alpha
          (fractionalGridLower mesh j) (fractionalGridUpper mesh j) N := by
      have huA := huData.1
      rw [show A = engelsmaSimplexInnerGridSupport H alpha mesh N by rfl,
        engelsmaSimplexInnerGridSupport, Finset.mem_biUnion] at huA
      exact huA
    obtain ⟨j, hj, huShell⟩ := huShell
    have huEnd : 1 < maynardS2CoordinateFiberEndpoint R
        (divisorTupleProduct H u) := by
      simpa [H, R] using hgoodN j hj u huShell
    have huNotSupport : u ∉ maynardDivisorTupleSupport H R (primorial D) := by
      intro huSupport
      apply huData.2
      exact mem_engelsmaS2OffFaceGoodSupport_iff.mpr ⟨huSupport, huEnd⟩
    have huNotSquarefree : ¬Squarefree (divisorTupleProduct H u) := by
      intro huSquarefree
      apply huNotSupport
      rw [maynardDivisorTupleSupport_eq_preSievedSimplex_filter]
      exact Finset.mem_filter.mpr
        ⟨by simpa [S, W, hW] using huPre, huSquarefree⟩
    exact Finset.mem_filter.mpr ⟨by simpa [S] using huPre, huNotSquarefree⟩
  have hgBounds : ∀ u ∈ S, 0 ≤ g u ∧ g u ≤ w u := by
    intro u hu
    have huSimplex := engelsmaS2OffFaceNormalizedLogPoint_mem_finiteSimplex
      (by simpa [R] using hRN) (by simpa [S] using hu)
    have hfNonneg := engelsmaS2OffFaceQuadraticIntegrand_nonneg
      (b := b) (c := c) huSimplex
    have hfAbs := abs_engelsmaS2OffFaceQuadraticIntegrand_le_one
      (b := b) (c := c) huSimplex
    have hfLe : engelsmaS2OffFaceQuadraticIntegrand m b c
        (engelsmaS2OffFaceNormalizedLogPoint alpha N m u) ≤ 1 :=
      (le_abs_self _).trans hfAbs
    have hw : 0 ≤ w u := by
      dsimp [w]
      unfold outerTupleWeight
      exact Finset.prod_nonneg (fun h hh =>
        maynardS2OuterSquarefreeAF_nonneg W (u h))
    dsimp [g]
    exact ⟨mul_nonneg hfNonneg hw, mul_le_of_le_one_left hw hfLe⟩
  have hremSubset : S \ A ⊆ B ∪ U := by
    intro u hu
    have huData := Finset.mem_sdiff.mp hu
    by_cases hunit : ∃ h : H, u h = 1
    · exact Finset.mem_union.mpr (Or.inr
        (preSievedSimplexUnitBoundary_subset_boxUnion huData.1 hunit))
    · have hnoUnit : ∀ h : H, u h ≠ 1 := not_exists.mp hunit
      rcases hcoverN u huData.1 hnoUnit with huInner | huBoundary
      · exact False.elim (huData.2 huInner)
      · exact Finset.mem_union.mpr (Or.inl huBoundary)
  have hGrem : G \ A ⊆ B ∪ U := by
    intro u hu
    exact hremSubset (Finset.mem_sdiff.mpr
      ⟨hMaynardSubset (Finset.mem_sdiff.mp hu).1, (Finset.mem_sdiff.mp hu).2⟩)
  have hAeq : (∑ u ∈ A, g u) =
      (∑ u ∈ A ∩ G, g u) + ∑ u ∈ A \ G, g u := by
    have hInt : A ∩ G ⊆ A := Finset.inter_subset_left
    have hdiff : A \ (A ∩ G) = A \ G := by
      ext u
      simp
    have hsum := Finset.sum_sdiff_eq_sub hInt (f := g)
    rw [hdiff] at hsum
    linarith
  have hGeq : (∑ u ∈ G, g u) =
      (∑ u ∈ G ∩ A, g u) + ∑ u ∈ G \ A, g u := by
    have hInt : G ∩ A ⊆ G := Finset.inter_subset_left
    have hdiff : G \ (G ∩ A) = G \ A := by
      ext u
      simp
    have hsum := Finset.sum_sdiff_eq_sub hInt (f := g)
    rw [hdiff] at hsum
    linarith
  have hLowerRaw : (∑ u ∈ A, g u) ≤
      (∑ u ∈ G, g u) + ∑ u ∈ C, w u := by
    rw [hAeq]
    apply add_le_add
    · apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      intro u hu huNot
      exact (hgBounds u (hMaynardSubset hu)).1
    · calc
        (∑ u ∈ A \ G, g u) ≤ ∑ u ∈ A \ G, w u := by
          apply Finset.sum_le_sum
          intro u hu
          exact (hgBounds u (hsubsetN (Finset.mem_sdiff.mp hu).1)).2
        _ ≤ ∑ u ∈ C, w u := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hAgood
          intro u hu huNot
          dsimp [w]
          unfold outerTupleWeight
          exact Finset.prod_nonneg (fun h hh =>
            maynardS2OuterSquarefreeAF_nonneg W (u h))
  have hUpperRaw : (∑ u ∈ G, g u) ≤
      (∑ u ∈ A, g u) + ∑ u ∈ B, w u + ∑ u ∈ U, w u := by
    rw [hGeq]
    have hGA : (∑ u ∈ G ∩ A, g u) ≤ ∑ u ∈ A, g u := by
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      intro u hu huNot
      exact (hgBounds u (hsubsetN hu)).1
    have hGW : (∑ u ∈ G \ A, g u) ≤
        ∑ u ∈ B, w u + ∑ u ∈ U, w u := by
      have hpoint : (∑ u ∈ G \ A, g u) ≤ ∑ u ∈ G \ A, w u := by
        apply Finset.sum_le_sum
        intro u hu
        exact (hgBounds u
          (hMaynardSubset (Finset.mem_sdiff.mp hu).1)).2
      have h1 : (∑ u ∈ G \ A, w u) ≤ ∑ u ∈ B ∪ U, w u := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hGrem
        intro u hu huNot
        dsimp [w]
        unfold outerTupleWeight
        exact Finset.prod_nonneg (fun h hh =>
          maynardS2OuterSquarefreeAF_nonneg W (u h))
      have h2 : (∑ u ∈ B ∪ U, w u) ≤
          (∑ u ∈ B, w u) + ∑ u ∈ U, w u := by
        have hinter : 0 ≤ ∑ u ∈ B ∩ U, w u := by
          apply Finset.sum_nonneg
          intro u hu
          dsimp [w]
          unfold outerTupleWeight
          exact Finset.prod_nonneg (fun h hh =>
            maynardS2OuterSquarefreeAF_nonneg W (u h))
        have heq := Finset.sum_union_inter (s₁ := B) (s₂ := U) (f := w)
        linarith
      exact hpoint.trans (h1.trans h2)
    linarith
  have hCellEq : (∑ u ∈ A, g u) =
      engelsmaS2OffFaceInnerGridQuadraticCellSum alpha m mesh N b c := by
    unfold A g engelsmaS2OffFaceInnerGridQuadraticCellSum
      engelsmaSimplexInnerGridSupport
    rw [Finset.sum_biUnion]
    intro j hj k hk hne
    exact hdisN j k hne
  have hGoodEq : (∑ u ∈ G, g u) =
      engelsmaS2OffFaceGoodQuadraticMoment alpha N m b c := by
    rfl
  have hCollisionEq : (∑ u ∈ C, w u) /
        engelsmaS2OffFaceNaturalScale alpha N m =
      normalizedEngelsmaS2OffFaceCollisionOuterMass alpha m N := by
    simp [C, w, W, R, H, engelsmaS2OffFaceNaturalScale,
      normalizedEngelsmaS2OffFaceCollisionOuterMass,
      engelsmaMaynardModulus]
  have hlowerDiv :
      (∑ u ∈ A, g u) / engelsmaS2OffFaceNaturalScale alpha N m -
        (∑ u ∈ G, g u) / engelsmaS2OffFaceNaturalScale alpha N m ≤
          (∑ u ∈ C, w u) / engelsmaS2OffFaceNaturalScale alpha N m := by
    rw [← sub_div]
    apply div_le_div_of_nonneg_right _ hscaleN.le
    linarith [hLowerRaw]
  have hupperDiv :
      (∑ u ∈ G, g u) / engelsmaS2OffFaceNaturalScale alpha N m ≤
        (∑ u ∈ A, g u) / engelsmaS2OffFaceNaturalScale alpha N m +
          (∑ u ∈ B, w u) / engelsmaS2OffFaceNaturalScale alpha N m +
            (∑ u ∈ U, w u) /
              engelsmaS2OffFaceNaturalScale alpha N m := by
    have hdiv := div_le_div_of_nonneg_right hUpperRaw hscaleN.le
    rw [add_div, add_div] at hdiv
    exact hdiv
  have hupperDiff :
      (∑ u ∈ G, g u) / engelsmaS2OffFaceNaturalScale alpha N m -
        (∑ u ∈ A, g u) / engelsmaS2OffFaceNaturalScale alpha N m ≤
          (∑ u ∈ B, w u) / engelsmaS2OffFaceNaturalScale alpha N m +
            (∑ u ∈ U, w u) / engelsmaS2OffFaceNaturalScale alpha N m := by
    linarith [hupperDiv]
  constructor
  · unfold normalizedEngelsmaS2OffFaceGoodQuadraticMoment
      normalizedEngelsmaS2OffFaceInnerGridQuadraticCellSum
    rw [← hGoodEq, ← hCellEq, ← hCollisionEq]
    linarith [hlowerDiv]
  · unfold normalizedEngelsmaS2OffFaceGoodQuadraticMoment
      normalizedEngelsmaS2OffFaceInnerGridQuadraticCellSum
    rw [← hGoodEq, ← hCellEq]
    have hB : (∑ u ∈ B, w u) /
        engelsmaS2OffFaceNaturalScale alpha N m =
      normalizedEngelsmaS2OffFaceBoundaryGridSupportMass alpha m mesh N := by
      rfl
    rw [← hB]
    have hU : (∑ u ∈ U, w u) /
        engelsmaS2OffFaceNaturalScale alpha N m =
      normalizedEngelsmaS2OuterUnitBoundaryBoxUnionMass H alpha N := by
      rfl
    rw [← hU]
    simpa [normalizedEngelsmaS2OffFaceGoodQuadraticMoment] using hupperDiff


end BoundedGaps.Maynard
