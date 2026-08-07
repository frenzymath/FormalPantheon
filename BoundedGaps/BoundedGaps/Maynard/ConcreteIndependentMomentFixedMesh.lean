import BoundedGaps.Maynard.ConcreteSimplexWeightedRiemann

noncomputable section
namespace BoundedGaps.Maynard

open Filter Set
open scoped BigOperators

def engelsmaNaturalQuadraticScale (alpha : ℝ) (N : ℕ) : ℝ :=
  (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
    Real.log (engelsmaMaynardRadius alpha N)) ^ 105

def engelsmaIndependentQuadraticWeightSum
    (alpha : ℝ) (N b c : ℕ) : ℝ :=
  ∑ u ∈ preSievedSimplexTupleSupport BoundedGaps.engelsmaTuple
      (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N),
    simplexQuadraticIntegrand 105 b c (engelsmaNormalizedLogPoint alpha N u) *
      reciprocalTotientTupleWeight BoundedGaps.engelsmaTuple u

def normalizedEngelsmaIndependentQuadraticNatural
    (alpha : ℝ) (N b c : ℕ) : ℝ :=
  engelsmaIndependentQuadraticWeightSum alpha N b c /
    engelsmaNaturalQuadraticScale alpha N

def engelsmaInnerGridQuadraticSum
    (alpha : ℝ) (m N b c : ℕ) : ℝ :=
  ∑ u ∈ engelsmaSimplexInnerGridSupport
      BoundedGaps.engelsmaTuple alpha m N,
    simplexQuadraticIntegrand 105 b c (engelsmaNormalizedLogPoint alpha N u) *
      reciprocalTotientTupleWeight BoundedGaps.engelsmaTuple u

def normalizedEngelsmaInnerGridQuadraticNatural
    (alpha : ℝ) (m N b c : ℕ) : ℝ :=
  engelsmaInnerGridQuadraticSum alpha m N b c /
    engelsmaNaturalQuadraticScale alpha N

def engelsmaInnerGridQuadraticCellSum
    (alpha : ℝ) (m N b c : ℕ) : ℝ :=
  ∑ j ∈ fractionalSimplexInnerGridIndex BoundedGaps.engelsmaTuple m,
    ∑ u ∈ engelsmaFractionalTupleShell BoundedGaps.engelsmaTuple alpha
        (fractionalGridLower m j) (fractionalGridUpper m j) N,
      simplexQuadraticIntegrand 105 b c (engelsmaNormalizedLogPoint alpha N u) *
        reciprocalTotientTupleWeight BoundedGaps.engelsmaTuple u

def normalizedEngelsmaInnerGridQuadraticCellNatural
    (alpha : ℝ) (m N b c : ℕ) : ℝ :=
  engelsmaInnerGridQuadraticCellSum alpha m N b c /
    engelsmaNaturalQuadraticScale alpha N

def engelsmaInnerGridQuadraticStepSum
    (alpha : ℝ) (m N b c : ℕ) : ℝ :=
  ∑ j ∈ fractionalSimplexInnerGridIndex BoundedGaps.engelsmaTuple m,
    simplexQuadraticIntegrand 105 b c (engelsmaGridLowerPoint m j) *
      engelsmaFractionalTupleShellMass BoundedGaps.engelsmaTuple alpha
        (fractionalGridLower m j) (fractionalGridUpper m j) N

def normalizedEngelsmaInnerGridQuadraticStep
    (alpha : ℝ) (m N b c : ℕ) : ℝ :=
  ∑ j ∈ fractionalSimplexInnerGridIndex BoundedGaps.engelsmaTuple m,
    simplexQuadraticIntegrand 105 b c (engelsmaGridLowerPoint m j) *
      normalizedEngelsmaFractionalTupleShellMass
        BoundedGaps.engelsmaTuple alpha
        (fractionalGridLower m j) (fractionalGridUpper m j) N

set_option maxRecDepth 10000 in
theorem engelsmaIndependentQuadraticWeightSum_eq_momentSum
    (alpha : ℝ) (N b c : ℕ) :
    engelsmaIndependentQuadraticWeightSum alpha N b c =
      engelsmaIndependentQuadraticMomentSum alpha N b c := by
  unfold engelsmaIndependentQuadraticWeightSum
    engelsmaIndependentQuadraticMomentSum
  apply Finset.sum_congr rfl
  intro u hu
  simp only [normalizedDivisorLogTuple]
  rw [show (∏ h : BoundedGaps.engelsmaTuple,
      (Nat.totient (u h) : ℝ)) =
      (commonTotientProduct BoundedGaps.engelsmaTuple u : ℝ) by
        unfold commonTotientProduct
        push_cast
        simp]
  rw [div_eq_mul_inv, ← one_div,
    inv_commonTotientProduct_eq_product]
  rfl

set_option maxRecDepth 10000 in
theorem tendsto_normalizedEngelsmaInnerGridQuadraticStep
    {alpha : ℝ} (halpha : 0 < alpha)
    {m : ℕ} (hm : 0 < m) (b c : ℕ) :
    Tendsto (fun N : ℕ =>
      normalizedEngelsmaInnerGridQuadraticStep alpha m N b c)
      atTop (nhds (simplexInnerGridQuadraticWeightedSum m b c)) := by
  let I := fractionalSimplexInnerGridIndex BoundedGaps.engelsmaTuple m
  have hlim :=
    tendsto_finite_linear_combination_normalizedEngelsmaFractionalTupleShellMass
      halpha I
      (fun j => simplexQuadraticIntegrand 105 b c (engelsmaGridLowerPoint m j))
      (fun j => fractionalGridLower m j)
      (fun j => fractionalGridUpper m j)
      (fun j hj h => (fractionalSimplexInnerGridIndex_data hm hj).1 h |>.1)
      (fun j hj h => (fractionalSimplexInnerGridIndex_data hm hj).1 h |>.2.1)
      (fun j hj h => (fractionalSimplexInnerGridIndex_data hm hj).1 h |>.2.2)
  simpa [I, normalizedEngelsmaInnerGridQuadraticStep,
    simplexInnerGridQuadraticWeightedSum] using hlim

set_option maxRecDepth 10000 in
theorem eventually_innerGridQuadraticSum_eq_cellSum
    {alpha : ℝ} (halpha : 0 < alpha)
    {m : ℕ} (hm : 0 < m) (b c : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      engelsmaInnerGridQuadraticSum alpha m N b c =
        engelsmaInnerGridQuadraticCellSum alpha m N b c := by
  have hdis := eventually_engelsmaSimplexInnerGridShells_pairwise_disjoint
    (H := BoundedGaps.engelsmaTuple) halpha hm
  filter_upwards [hdis] with N hdisN
  unfold engelsmaInnerGridQuadraticSum engelsmaInnerGridQuadraticCellSum
    engelsmaSimplexInnerGridSupport
  rw [Finset.sum_biUnion]
  intro j hj k hk hne
  exact hdisN j hj k hk hne

theorem simplexQuadraticIntegrand_nonneg_of_mem_simplex
    {k b c : ℕ} {t : Fin k → ℝ} (ht : t ∈ maynardSimplex k) :
    0 ≤ simplexQuadraticIntegrand k b c t := by
  unfold simplexQuadraticIntegrand
  apply mul_nonneg
  · exact pow_nonneg (sub_nonneg.mpr ht.2) b
  · exact pow_nonneg (Finset.sum_nonneg fun i hi => sq_nonneg (t i)) c

set_option maxRecDepth 10000 in
theorem normalizedEngelsmaInnerGridQuadraticStep_eq_div
    (alpha : ℝ) (m N b c : ℕ) :
    normalizedEngelsmaInnerGridQuadraticStep alpha m N b c =
      engelsmaInnerGridQuadraticStepSum alpha m N b c /
        engelsmaNaturalQuadraticScale alpha N := by
  unfold normalizedEngelsmaInnerGridQuadraticStep
    engelsmaInnerGridQuadraticStepSum
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  unfold normalizedEngelsmaFractionalTupleShellMass
    engelsmaNaturalQuadraticScale
  simp only [Fintype.card_coe, BoundedGaps.engelsmaTuple_card]
  ring

set_option maxRecDepth 10000 in
theorem normalizedEngelsmaSimplexInnerGridStepMass_eq_div
    (alpha : ℝ) (m N : ℕ) :
    normalizedEngelsmaSimplexInnerGridStepMass
        BoundedGaps.engelsmaTuple alpha m N =
      (∑ j ∈ fractionalSimplexInnerGridIndex
          BoundedGaps.engelsmaTuple m,
        engelsmaFractionalTupleShellMass BoundedGaps.engelsmaTuple alpha
          (fractionalGridLower m j) (fractionalGridUpper m j) N) /
        engelsmaNaturalQuadraticScale alpha N := by
  unfold normalizedEngelsmaSimplexInnerGridStepMass
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  unfold normalizedEngelsmaFractionalTupleShellMass
    engelsmaNaturalQuadraticScale
  simp only [Fintype.card_coe, BoundedGaps.engelsmaTuple_card]

set_option maxRecDepth 10000 in
theorem engelsmaInnerGridQuadraticStepSum_eq_cellSum
    (alpha : ℝ) (m N b c : ℕ) :
    engelsmaInnerGridQuadraticStepSum alpha m N b c =
      ∑ j ∈ fractionalSimplexInnerGridIndex BoundedGaps.engelsmaTuple m,
        ∑ u ∈ engelsmaFractionalTupleShell BoundedGaps.engelsmaTuple alpha
            (fractionalGridLower m j) (fractionalGridUpper m j) N,
          simplexQuadraticIntegrand 105 b c (engelsmaGridLowerPoint m j) *
            reciprocalTotientTupleWeight BoundedGaps.engelsmaTuple u := by
  unfold engelsmaInnerGridQuadraticStepSum
    engelsmaFractionalTupleShellMass
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]

set_option maxRecDepth 10000 in
theorem innerGridQuadraticCellSum_sub_stepSum_le
    {alpha : ℝ} {m N b c : ℕ} {epsilon : ℝ}
    (_hepsilon : 0 ≤ epsilon)
    (hosc : ∀ j ∈ fractionalSimplexInnerGridIndex
        BoundedGaps.engelsmaTuple m,
      ∀ u ∈ engelsmaFractionalTupleShell BoundedGaps.engelsmaTuple alpha
        (fractionalGridLower m j) (fractionalGridUpper m j) N,
        |simplexQuadraticIntegrand 105 b c (engelsmaNormalizedLogPoint alpha N u) -
          simplexQuadraticIntegrand 105 b c
            (engelsmaGridLowerPoint m j)| ≤ epsilon) :
    |engelsmaInnerGridQuadraticCellSum alpha m N b c -
        engelsmaInnerGridQuadraticStepSum alpha m N b c| ≤
      epsilon * ∑ j ∈ fractionalSimplexInnerGridIndex
          BoundedGaps.engelsmaTuple m,
        engelsmaFractionalTupleShellMass BoundedGaps.engelsmaTuple alpha
          (fractionalGridLower m j) (fractionalGridUpper m j) N := by
  rw [engelsmaInnerGridQuadraticStepSum_eq_cellSum]
  unfold engelsmaInnerGridQuadraticCellSum
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ fractionalSimplexInnerGridIndex BoundedGaps.engelsmaTuple m,
        |(∑ u ∈ engelsmaFractionalTupleShell BoundedGaps.engelsmaTuple alpha
              (fractionalGridLower m j) (fractionalGridUpper m j) N,
            simplexQuadraticIntegrand 105 b c (engelsmaNormalizedLogPoint alpha N u) *
              reciprocalTotientTupleWeight BoundedGaps.engelsmaTuple u) -
          ∑ u ∈ engelsmaFractionalTupleShell BoundedGaps.engelsmaTuple alpha
              (fractionalGridLower m j) (fractionalGridUpper m j) N,
            simplexQuadraticIntegrand 105 b c (engelsmaGridLowerPoint m j) *
              reciprocalTotientTupleWeight BoundedGaps.engelsmaTuple u| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ fractionalSimplexInnerGridIndex BoundedGaps.engelsmaTuple m,
        epsilon * engelsmaFractionalTupleShellMass BoundedGaps.engelsmaTuple alpha
          (fractionalGridLower m j) (fractionalGridUpper m j) N := by
      apply Finset.sum_le_sum
      intro j hj
      rw [← Finset.sum_sub_distrib]
      calc
        _ ≤ ∑ u ∈ engelsmaFractionalTupleShell BoundedGaps.engelsmaTuple alpha
              (fractionalGridLower m j) (fractionalGridUpper m j) N,
            |simplexQuadraticIntegrand 105 b c (engelsmaNormalizedLogPoint alpha N u) *
                reciprocalTotientTupleWeight BoundedGaps.engelsmaTuple u -
              simplexQuadraticIntegrand 105 b c (engelsmaGridLowerPoint m j) *
                reciprocalTotientTupleWeight BoundedGaps.engelsmaTuple u| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ u ∈ engelsmaFractionalTupleShell BoundedGaps.engelsmaTuple alpha
              (fractionalGridLower m j) (fractionalGridUpper m j) N,
            epsilon * reciprocalTotientTupleWeight BoundedGaps.engelsmaTuple u := by
          apply Finset.sum_le_sum
          intro u hu
          rw [← sub_mul, abs_mul, abs_of_nonneg
            (show 0 ≤ reciprocalTotientTupleWeight BoundedGaps.engelsmaTuple u by
              unfold reciprocalTotientTupleWeight
              positivity)]
          exact mul_le_mul_of_nonneg_right (hosc j hj u hu)
            (by unfold reciprocalTotientTupleWeight; positivity)
        _ = _ := by
          unfold engelsmaFractionalTupleShellMass
          rw [Finset.mul_sum]
    _ = _ := by rw [Finset.mul_sum]

theorem eventually_engelsmaNaturalQuadraticScale_pos
    {alpha : ℝ} (halpha : 0 < alpha) :
    ∀ᶠ N : ℕ in atTop, 0 < engelsmaNaturalQuadraticScale alpha N := by
  have hR := eventually_one_lt_engelsmaMaynardRadius halpha
  filter_upwards [hR] with N hRN
  unfold engelsmaNaturalQuadraticScale
  have hS := preSieveSingularSeries_pos (tripleLogCutoff (N - 1))
  have hRNreal : (1 : ℝ) < engelsmaMaynardRadius alpha N := by
    exact_mod_cast hRN
  have hlog := Real.log_pos hRNreal
  exact pow_pos (mul_pos hS hlog) 105

set_option maxRecDepth 10000 in
theorem innerGridQuadraticCellNatural_sub_step_le
    {alpha : ℝ} {m N b c : ℕ} {epsilon : ℝ}
    (hscale : 0 < engelsmaNaturalQuadraticScale alpha N)
    (hepsilon : 0 ≤ epsilon)
    (hosc : ∀ j ∈ fractionalSimplexInnerGridIndex
        BoundedGaps.engelsmaTuple m,
      ∀ u ∈ engelsmaFractionalTupleShell BoundedGaps.engelsmaTuple alpha
        (fractionalGridLower m j) (fractionalGridUpper m j) N,
        |simplexQuadraticIntegrand 105 b c (engelsmaNormalizedLogPoint alpha N u) -
          simplexQuadraticIntegrand 105 b c
            (engelsmaGridLowerPoint m j)| ≤ epsilon) :
    |normalizedEngelsmaInnerGridQuadraticCellNatural alpha m N b c -
        normalizedEngelsmaInnerGridQuadraticStep alpha m N b c| ≤
      epsilon * normalizedEngelsmaSimplexInnerGridStepMass
        BoundedGaps.engelsmaTuple alpha m N := by
  have hraw := innerGridQuadraticCellSum_sub_stepSum_le hepsilon hosc
  rw [normalizedEngelsmaInnerGridQuadraticStep_eq_div,
    normalizedEngelsmaSimplexInnerGridStepMass_eq_div]
  unfold normalizedEngelsmaInnerGridQuadraticCellNatural
  rw [← sub_div, abs_div, abs_of_pos hscale]
  apply (div_le_div_of_nonneg_right hraw hscale.le).trans_eq
  ring

def normalizedEngelsmaSimplexBoundaryGridSupportMassNatural
    (alpha : ℝ) (m N : ℕ) : ℝ :=
  engelsmaSimplexBoundaryGridSupportMass BoundedGaps.engelsmaTuple alpha m N /
    engelsmaNaturalQuadraticScale alpha N

theorem normalizedEngelsmaUnitBoundaryBoxUnionMass_eq_natural
    (alpha : ℝ) (N : ℕ) :
    normalizedEngelsmaUnitBoundaryBoxUnionMass
        BoundedGaps.engelsmaTuple alpha N =
      engelsmaUnitBoundaryBoxUnionMass BoundedGaps.engelsmaTuple alpha N /
        engelsmaNaturalQuadraticScale alpha N := by
  unfold normalizedEngelsmaUnitBoundaryBoxUnionMass
    engelsmaNaturalQuadraticScale
  simp only [Fintype.card_coe, BoundedGaps.engelsmaTuple_card]

set_option maxRecDepth 10000 in
theorem eventually_normalizedBoundaryGridSupportMassNatural_eq_stepMass
    {alpha : ℝ} (halpha : 0 < alpha)
    {m : ℕ} (hm : 0 < m) :
    ∀ᶠ N : ℕ in atTop,
      normalizedEngelsmaSimplexBoundaryGridSupportMassNatural alpha m N =
        normalizedEngelsmaSimplexBoundaryGridStepMass
          BoundedGaps.engelsmaTuple alpha m N := by
  have heq := eventually_engelsmaSimplexBoundaryGridSupportMass_eq_stepMass
    (H := BoundedGaps.engelsmaTuple) halpha hm
  filter_upwards [heq] with N heqN
  unfold normalizedEngelsmaSimplexBoundaryGridSupportMassNatural
    normalizedEngelsmaSimplexBoundaryGridStepMass
  rw [heqN, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  unfold normalizedEngelsmaFractionalTupleShellMass
    engelsmaNaturalQuadraticScale
  simp only [Fintype.card_coe, BoundedGaps.engelsmaTuple_card]

set_option maxRecDepth 10000 in
theorem eventually_normalizedInnerGridQuadraticNatural_eq_cellNatural
    {alpha : ℝ} (halpha : 0 < alpha)
    {m : ℕ} (hm : 0 < m) (b c : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      normalizedEngelsmaInnerGridQuadraticNatural alpha m N b c =
        normalizedEngelsmaInnerGridQuadraticCellNatural alpha m N b c := by
  have heq := eventually_innerGridQuadraticSum_eq_cellSum halpha hm b c
  filter_upwards [heq] with N heqN
  unfold normalizedEngelsmaInnerGridQuadraticNatural
    normalizedEngelsmaInnerGridQuadraticCellNatural
  rw [heqN]

set_option maxRecDepth 10000 in
theorem eventually_independentNatural_sub_inner_le_boundary
    {alpha : ℝ} (halpha : 0 < alpha)
    {m : ℕ} (hm : 0 < m) (b c : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      0 ≤ normalizedEngelsmaIndependentQuadraticNatural alpha N b c -
          normalizedEngelsmaInnerGridQuadraticNatural alpha m N b c ∧
        normalizedEngelsmaIndependentQuadraticNatural alpha N b c -
            normalizedEngelsmaInnerGridQuadraticNatural alpha m N b c ≤
          normalizedEngelsmaSimplexBoundaryGridSupportMassNatural alpha m N +
            normalizedEngelsmaUnitBoundaryBoxUnionMass
              BoundedGaps.engelsmaTuple alpha N := by
  have hsubset := eventually_engelsmaSimplexInnerGridSupport_subset
    (H := BoundedGaps.engelsmaTuple) halpha hm
  have hcover := eventually_preSievedSimplexTupleSupport_mem_inner_or_boundaryShell
    (H := BoundedGaps.engelsmaTuple) halpha hm
  have hscale := eventually_engelsmaNaturalQuadraticScale_pos halpha
  have hR := eventually_one_lt_engelsmaMaynardRadius halpha
  filter_upwards [hsubset, hcover, hscale, hR] with
      N hsubsetN hcoverN hscaleN hRN
  let S := preSievedSimplexTupleSupport BoundedGaps.engelsmaTuple
    (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N)
  let A := engelsmaSimplexInnerGridSupport
    BoundedGaps.engelsmaTuple alpha m N
  let B := engelsmaSimplexBoundaryGridShellUnion
    BoundedGaps.engelsmaTuple alpha m N
  let U := engelsmaUnitBoundaryBoxUnion
    BoundedGaps.engelsmaTuple alpha N
  let g : (BoundedGaps.engelsmaTuple → ℕ) → ℝ := fun u =>
    simplexQuadraticIntegrand 105 b c (engelsmaNormalizedLogPoint alpha N u) *
      reciprocalTotientTupleWeight BoundedGaps.engelsmaTuple u
  let w : (BoundedGaps.engelsmaTuple → ℕ) → ℝ := fun u =>
    reciprocalTotientTupleWeight BoundedGaps.engelsmaTuple u
  have hAS : A ⊆ S := hsubsetN
  have hgBounds : ∀ u ∈ S, 0 ≤ g u ∧ g u ≤ w u := by
    intro u hu
    have hsimplex := normalizedEngelsmaLogTuple_mem_simplex_of_independent hRN hu
    have hfNonneg := simplexQuadraticIntegrand_nonneg_of_mem_simplex
      (b := b) (c := c) hsimplex
    have hfAbs := abs_simplexQuadraticIntegrand_le_one
      (b := b) (c := c) hsimplex
    have hfLe : simplexQuadraticIntegrand 105 b c
        (engelsmaNormalizedLogPoint alpha N u) ≤ 1 :=
      (le_abs_self _).trans hfAbs
    have hw : 0 ≤ w u := by
      dsimp [w]
      unfold reciprocalTotientTupleWeight
      positivity
    dsimp [g]
    exact ⟨mul_nonneg hfNonneg hw, mul_le_of_le_one_left hw hfLe⟩
  have hremSubset : S \ A ⊆ B ∪ U := by
    intro u hu
    have huData := Finset.mem_sdiff.mp hu
    by_cases hunit : ∃ h : BoundedGaps.engelsmaTuple, u h = 1
    · exact Finset.mem_union.mpr (Or.inr
        (preSievedSimplexUnitBoundary_subset_boxUnion huData.1 hunit))
    · have hnoUnit : ∀ h : BoundedGaps.engelsmaTuple, u h ≠ 1 :=
        not_exists.mp hunit
      rcases hcoverN u huData.1 hnoUnit with huInner | huBoundary
      · exact False.elim (huData.2 huInner)
      · exact Finset.mem_union.mpr (Or.inl huBoundary)
  have hremG : (∑ u ∈ S \ A, g u) ≤ ∑ u ∈ S \ A, w u := by
    apply Finset.sum_le_sum
    intro u hu
    exact (hgBounds u (Finset.sdiff_subset hu)).2
  have hremW : (∑ u ∈ S \ A, w u) ≤ ∑ u ∈ B ∪ U, w u := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hremSubset
    intro u hu hnot
    dsimp [w]
    unfold reciprocalTotientTupleWeight
    positivity
  have hunion : (∑ u ∈ B ∪ U, w u) ≤
      (∑ u ∈ B, w u) + ∑ u ∈ U, w u := by
    have hinter : 0 ≤ ∑ u ∈ B ∩ U, w u := by
      apply Finset.sum_nonneg
      intro u hu
      dsimp [w]
      unfold reciprocalTotientTupleWeight
      positivity
    have heq := Finset.sum_union_inter (s₁ := B) (s₂ := U) (f := w)
    linarith
  have hrawNonneg : 0 ≤ (∑ u ∈ S, g u) - ∑ u ∈ A, g u := by
    rw [← Finset.sum_sdiff_eq_sub hAS]
    apply Finset.sum_nonneg
    intro u hu
    exact (hgBounds u (Finset.sdiff_subset hu)).1
  have hrawUpper : (∑ u ∈ S, g u) - ∑ u ∈ A, g u ≤
      (∑ u ∈ B, w u) + ∑ u ∈ U, w u := by
    rw [← Finset.sum_sdiff_eq_sub hAS]
    exact hremG.trans (hremW.trans hunion)
  have hnormEq :
      normalizedEngelsmaIndependentQuadraticNatural alpha N b c -
          normalizedEngelsmaInnerGridQuadraticNatural alpha m N b c =
        ((∑ u ∈ S, g u) - ∑ u ∈ A, g u) /
          engelsmaNaturalQuadraticScale alpha N := by
    unfold normalizedEngelsmaIndependentQuadraticNatural
      engelsmaIndependentQuadraticWeightSum
      normalizedEngelsmaInnerGridQuadraticNatural
      engelsmaInnerGridQuadraticSum
    dsimp [S, A, g]
    ring
  rw [hnormEq]
  constructor
  · exact div_nonneg hrawNonneg hscaleN.le
  · have hdiv := div_le_div_of_nonneg_right hrawUpper hscaleN.le
    apply hdiv.trans_eq
    unfold normalizedEngelsmaSimplexBoundaryGridSupportMassNatural
      engelsmaSimplexBoundaryGridSupportMass
    rw [normalizedEngelsmaUnitBoundaryBoxUnionMass_eq_natural]
    unfold engelsmaUnitBoundaryBoxUnionMass
    dsimp [B, U, w]
    ring

end BoundedGaps.Maynard
