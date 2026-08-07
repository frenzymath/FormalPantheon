import BoundedGaps.Maynard.ConcreteSimplexGridCover

noncomputable section

namespace BoundedGaps.Maynard

open Filter Set
open scoped BigOperators

def engelsmaSimplexOuterGridShellUnion
    (H : Finset ℕ) (alpha : ℝ) (m N : ℕ) : Finset (H → ℕ) :=
  (fractionalSimplexOuterGridIndex H m).biUnion fun j =>
    engelsmaFractionalTupleShell H alpha
      (fractionalGridLower m j) (fractionalGridUpper m j) N

def engelsmaSimplexBoundaryGridShellUnion
    (H : Finset ℕ) (alpha : ℝ) (m N : ℕ) : Finset (H → ℕ) :=
  (fractionalSimplexBoundaryGridIndex H m).biUnion fun j =>
    engelsmaFractionalTupleShell H alpha
      (fractionalGridLower m j) (fractionalGridUpper m j) N

def normalizedEngelsmaSimplexBoundaryGridStepMass
    (H : Finset ℕ) (alpha : ℝ) (m N : ℕ) : ℝ :=
  ∑ j ∈ fractionalSimplexBoundaryGridIndex H m,
    normalizedEngelsmaFractionalTupleShellMass H alpha
      (fractionalGridLower m j) (fractionalGridUpper m j) N

def simplexBoundaryGridVolume (H : Finset ℕ) (m : ℕ) : ℝ :=
  ∑ j ∈ fractionalSimplexBoundaryGridIndex H m,
    ∏ h : H, (fractionalGridUpper m j h - fractionalGridLower m j h)

def engelsmaSimplexBoundaryGridSupportMass
    (H : Finset ℕ) (alpha : ℝ) (m N : ℕ) : ℝ :=
  ∑ u ∈ engelsmaSimplexBoundaryGridShellUnion H alpha m N,
    reciprocalTotientTupleWeight H u

theorem tendsto_normalizedEngelsmaSimplexBoundaryGridStepMass
    {H : Finset ℕ} {alpha : ℝ} (halpha : 0 < alpha)
    {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ =>
      normalizedEngelsmaSimplexBoundaryGridStepMass H alpha m N)
      atTop (nhds (simplexBoundaryGridVolume H m)) := by
  let I := fractionalSimplexBoundaryGridIndex H m
  have hlim :=
    tendsto_finite_linear_combination_normalizedEngelsmaFractionalTupleShellMass
      halpha I (fun _ => (1 : ℝ))
      (fun j => fractionalGridLower m j)
      (fun j => fractionalGridUpper m j)
      (fun j hj h => (fractionalGridEndpoints_mem_Icc hm
        (Finset.mem_filter.mp hj).1 h).1)
      (fun j hj h => (fractionalGridEndpoints_mem_Icc hm
        (Finset.mem_filter.mp hj).1 h).2.1)
      (fun j hj h => (fractionalGridEndpoints_mem_Icc hm
        (Finset.mem_filter.mp hj).1 h).2.2)
  simpa [I, normalizedEngelsmaSimplexBoundaryGridStepMass,
    simplexBoundaryGridVolume] using hlim

theorem eventually_engelsmaSimplexBoundaryGridSupportMass_eq_stepMass
    {H : Finset ℕ} {alpha : ℝ} {m : ℕ}
    (halpha : 0 < alpha) (hm : 0 < m) :
    ∀ᶠ N : ℕ in atTop,
      engelsmaSimplexBoundaryGridSupportMass H alpha m N =
        ∑ j ∈ fractionalSimplexBoundaryGridIndex H m,
          engelsmaFractionalTupleShellMass H alpha
            (fractionalGridLower m j) (fractionalGridUpper m j) N := by
  have hdis := eventually_engelsmaFractionalGridShells_pairwise_disjoint
    (H := H) halpha hm
  filter_upwards [hdis] with N hdisN
  unfold engelsmaSimplexBoundaryGridSupportMass
    engelsmaSimplexBoundaryGridShellUnion
  rw [Finset.sum_biUnion]
  · rfl
  · intro j hj k hk hne
    exact hdisN j k hne

theorem eventually_engelsmaSimplexOuterGridShellUnion_disjoint_preSieved
    {H : Finset ℕ} {alpha : ℝ} {m : ℕ}
    (halpha : 0 < alpha) (hm : 0 < m) :
    ∀ᶠ N : ℕ in atTop,
      Disjoint (engelsmaSimplexOuterGridShellUnion H alpha m N)
        (preSievedSimplexTupleSupport H
          (engelsmaMaynardRadius alpha N)
          (engelsmaMaynardModulus N)) := by
  let I := fractionalSimplexOuterGridIndex H m
  have hcard : ∀ j ∈ I, 0 < Fintype.card H := by
    intro j hj
    by_contra hcard
    have hzero : Fintype.card H = 0 := Nat.eq_zero_of_not_pos hcard
    have hEmpty : IsEmpty H := Fintype.card_eq_zero_iff.mp hzero
    letI := hEmpty
    have houter := (Finset.mem_filter.mp hj).2
    simp at houter
    linarith
  have hcell : ∀ j ∈ I, ∀ h : H,
      ∀ᶠ N : ℕ in atTop, ∀ u : H → ℕ,
        u h ∈ squarefreeCoprimeCoordinateShell
          (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius
            (alpha * fractionalGridLower m j h) N)
          (engelsmaMaynardRadius
            (alpha * fractionalGridUpper m j h) N) →
        Real.log (u h) /
            Real.log (engelsmaMaynardRadius alpha N) >
          fractionalGridLower m j h -
            ((∑ i : H, fractionalGridLower m j i) - 1) /
              (2 * Fintype.card H) := by
    intro j hj h
    let a : ℝ := fractionalGridLower m j h
    let delta : ℝ :=
      ((∑ i : H, fractionalGridLower m j i) - 1) /
        (2 * Fintype.card H)
    have houter : 1 < ∑ i : H, fractionalGridLower m j i :=
      (Finset.mem_filter.mp hj).2
    have hdelta : 0 < delta := by
      dsimp [delta]
      have hcardReal : (0 : ℝ) < Fintype.card H := by
        exact_mod_cast hcard j hj
      exact div_pos (sub_pos.mpr houter) (by positivity)
    have ha : 0 ≤ a := by
      dsimp [a, fractionalGridLower]
      positivity
    have hcellEvent : ∀ᶠ N : ℕ in atTop, ∀ u : H → ℕ,
        u h ∈ squarefreeCoprimeCoordinateShell
            (engelsmaMaynardModulus N)
            (engelsmaMaynardRadius (alpha * a) N)
            (engelsmaMaynardRadius
              (alpha * fractionalGridUpper m j h) N) →
          Real.log (u h) /
              Real.log (engelsmaMaynardRadius alpha N) > a - delta := by
      by_cases ha0 : a = 0
      · have hR0 : ∀ N : ℕ,
            engelsmaMaynardRadius (alpha * a) N = 1 := by
          intro N
          simp [a, ha0, engelsmaMaynardRadius, maynardDivisorCutoff]
        have hR := eventually_one_lt_engelsmaMaynardRadius halpha
        filter_upwards [hR] with N hRN u hu
        have huData := Finset.mem_sdiff.mp hu |>.1
        have huIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp huData).1
        have huOne : 1 < u h := by
          have hgt : engelsmaMaynardRadius (alpha * a) N < u h := by
            by_contra hnot
            apply Finset.mem_sdiff.mp hu |>.2
            apply Finset.mem_filter.mpr
            exact ⟨Finset.mem_Icc.mpr ⟨huIcc.1, Nat.le_of_not_gt hnot⟩,
              (Finset.mem_filter.mp huData).2⟩
          simpa [hR0 N] using hgt
        have hlog : 0 < Real.log (u h) :=
          Real.log_pos (by exact_mod_cast huOne)
        have hden : 0 < Real.log (engelsmaMaynardRadius alpha N) := by
          exact Real.log_pos (by exact_mod_cast hRN)
        have : 0 < Real.log (u h) /
            Real.log (engelsmaMaynardRadius alpha N) :=
          div_pos hlog hden
        have htarget : a - delta = -delta := by simp [a, ha0]
        rw [htarget]
        exact (neg_lt_zero.mpr hdelta).trans this
      · have haPos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        let beta : ℝ := max 0 (a - delta)
        have hbeta : 0 ≤ beta := le_max_left _ _
        have hbg : beta < a := by
          dsimp [beta]
          exact max_lt haPos (sub_lt_self a hdelta)
        have hmargin := eventually_nat_le_engelsmaMaynardRadius_of_log_ratio_le
          halpha hbeta hbg
        have hR := eventually_one_lt_engelsmaMaynardRadius halpha
        filter_upwards [hmargin, hR] with N hmarginN hRN u hu
        have huData := Finset.mem_sdiff.mp hu |>.1
        have huIcc := Finset.mem_Icc.mp (Finset.mem_filter.mp huData).1
        have hgt : engelsmaMaynardRadius (alpha * a) N < u h := by
          by_contra hnot
          apply Finset.mem_sdiff.mp hu |>.2
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_Icc.mpr ⟨huIcc.1, Nat.le_of_not_gt hnot⟩,
            (Finset.mem_filter.mp huData).2⟩
        have huPos : 0 < u h := by exact_mod_cast huIcc.1
        have hnotLe : ¬u h ≤ engelsmaMaynardRadius (alpha * a) N :=
          Nat.not_le_of_gt hgt
        have hratio : beta < Real.log (u h) /
            Real.log (engelsmaMaynardRadius alpha N) := by
          by_contra hnotRatio
          apply hnotLe
          apply hmarginN (u h) huPos
          exact le_of_not_gt hnotRatio
        have htarget : a - delta ≤ beta := by
          dsimp [beta]
          exact le_max_right _ _
        exact lt_of_le_of_lt htarget hratio
    simpa [a, delta] using hcellEvent
  have hcells : ∀ j ∈ I, ∀ᶠ N : ℕ in atTop, ∀ h : H, ∀ u : H → ℕ,
      u h ∈ squarefreeCoprimeCoordinateShell
          (engelsmaMaynardModulus N)
          (engelsmaMaynardRadius
            (alpha * fractionalGridLower m j h) N)
          (engelsmaMaynardRadius
            (alpha * fractionalGridUpper m j h) N) →
        Real.log (u h) /
            Real.log (engelsmaMaynardRadius alpha N) >
          fractionalGridLower m j h -
            ((∑ i : H, fractionalGridLower m j i) - 1) /
              (2 * Fintype.card H) := by
    intro j hj
    have hall := (Finset.univ : Finset H).eventually_all.mpr
      (fun h hh => hcell j hj h)
    filter_upwards [hall] with N hallN h u hu
    exact hallN h (Finset.mem_univ h) u hu
  have hgrid := I.eventually_all.mpr (fun j hj => hcells j hj)
  have hR := eventually_one_lt_engelsmaMaynardRadius halpha
  filter_upwards [hgrid, hR] with N hgridN hRN
  apply Finset.disjoint_left.mpr
  intro u huOuter huSimplex
  rw [engelsmaSimplexOuterGridShellUnion, Finset.mem_biUnion] at huOuter
  obtain ⟨j, hj, huShell⟩ := huOuter
  have hratios : ∀ h : H,
      Real.log (u h) /
          Real.log (engelsmaMaynardRadius alpha N) >
        fractionalGridLower m j h -
          ((∑ i : H, fractionalGridLower m j i) - 1) /
            (2 * Fintype.card H) := by
    intro h
    exact hgridN j hj h u (Fintype.mem_piFinset.mp huShell h)
  have hsumLower : 1 < ∑ h : H, fractionalGridLower m j h :=
    (Finset.mem_filter.mp hj).2
  have hsumRatio : 1 < ∑ h : H,
      Real.log (u h) /
        Real.log (engelsmaMaynardRadius alpha N) := by
    have hcardReal : (0 : ℝ) < Fintype.card H := by
      exact_mod_cast hcard j hj
    let delta : ℝ := ((∑ h : H, fractionalGridLower m j h) - 1) /
      (2 * Fintype.card H)
    have hcardNe : (Fintype.card H : ℝ) ≠ 0 := ne_of_gt hcardReal
    have hmul : (Fintype.card H : ℝ) * delta =
        ((∑ h : H, fractionalGridLower m j h) - 1) / 2 := by
      dsimp [delta]
      field_simp [hcardNe]
    have hmargin : 1 < ∑ h : H,
        (fractionalGridLower m j h - delta) := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [hmul]
      linarith
    letI : Nonempty H := Fintype.card_pos_iff.mp (hcard j hj)
    apply lt_trans hmargin
    apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    intro h hh
    simpa [delta] using hratios h
  have huPos : ∀ h : H, 0 < u h :=
    fun h => (preSievedSimplexTupleSupport_coordinate huSimplex h).1
  have hsimplex := (divisorTupleProduct_lt_iff_sum_normalizedDivisorLogTuple_lt_one
    hRN huPos).mp (mem_preSievedSimplexTupleSupport_iff.mp huSimplex).2
  unfold normalizedDivisorLogTuple at hsimplex
  linarith

theorem eventually_preSievedSimplexTupleSupport_mem_inner_or_boundaryShell
    {H : Finset ℕ} {alpha : ℝ} {m : ℕ}
    (halpha : 0 < alpha) (hm : 0 < m) :
    ∀ᶠ N : ℕ in atTop, ∀ u : H → ℕ,
      u ∈ preSievedSimplexTupleSupport H
          (engelsmaMaynardRadius alpha N)
          (engelsmaMaynardModulus N) →
      (∀ h : H, u h ≠ 1) →
      u ∈ engelsmaSimplexInnerGridSupport H alpha m N ∨
        u ∈ engelsmaSimplexBoundaryGridShellUnion H alpha m N := by
  have hcover := eventually_preSievedSimplexTupleSupport_mem_gridShellUnion_of_no_unit
    (H := H) halpha hm
  have houter := eventually_engelsmaSimplexOuterGridShellUnion_disjoint_preSieved
    (H := H) halpha hm
  filter_upwards [hcover, houter] with N hcoverN houterN u hu hunit
  have hfull := hcoverN u hu hunit
  rw [engelsmaFractionalTupleGridShellUnion, Finset.mem_biUnion] at hfull
  obtain ⟨j, hj, huShell⟩ := hfull
  have hjPartition : j ∈ fractionalSimplexInnerGridIndex H m ∪
      (fractionalSimplexBoundaryGridIndex H m ∪
        fractionalSimplexOuterGridIndex H m) := by
    rw [← fractionalGridIndex_eq_inner_union_boundary_union_outer H m]
    exact hj
  rcases Finset.mem_union.mp hjPartition with hjInner | hjRest
  · left
    rw [engelsmaSimplexInnerGridSupport, Finset.mem_biUnion]
    exact ⟨j, hjInner, huShell⟩
  · rcases Finset.mem_union.mp hjRest with hjBoundary | hjOuter
    · right
      rw [engelsmaSimplexBoundaryGridShellUnion, Finset.mem_biUnion]
      exact ⟨j, hjBoundary, huShell⟩
    · exfalso
      apply Finset.disjoint_left.mp houterN
        (Finset.mem_biUnion.mpr ⟨j, hjOuter, huShell⟩) hu

end BoundedGaps.Maynard
