import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaCandidateSingularities
import Mathlib.Topology.MetricSpace.Infsep
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Dirichlet explicit-formula candidate isolation

`KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 114--115, moves the
modified explicit-formula contour across finitely many ordinary L-function
zeros and the principal pole. Once those candidate locations lie in the
rectangle interior, this file selects one positive radius whose closed disks
remain inside the rectangle and are pairwise disjoint.

The later good-height theorem must establish the interior hypothesis. No
contour identity, residue sum, or quantitative lower bound for the radius is
asserted here. Semantic review: `SEM-503`.
-/

noncomputable section

open Complex Metric Set

namespace BoundedGaps.Maynard

/-- A finite set of candidate singularities strictly inside a rectangle has a
common positive radius for contained, pairwise-disjoint closed disks. -/
theorem exists_dirichletExplicitFormulaCandidateSingularityRadius
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (z w : ℂ)
    (hinterior :
      dirichletExplicitFormulaCandidateSingularities chi z w ⊆
        interior (Complex.Rectangle z w)) :
    ∃ R : ℝ, 0 < R ∧
      (∀ rho ∈ dirichletExplicitFormulaCandidateSingularities chi z w,
        Metric.closedBall rho R ⊆ interior (Complex.Rectangle z w)) ∧
      (dirichletExplicitFormulaCandidateSingularities chi z w).PairwiseDisjoint
        (fun rho => Metric.closedBall rho R) := by
  let C := dirichletExplicitFormulaCandidateSingularities chi z w
  change C ⊆ interior (Complex.Rectangle z w) at hinterior
  change ∃ R : ℝ, 0 < R ∧
    (∀ rho ∈ C, closedBall rho R ⊆ interior (Complex.Rectangle z w)) ∧
    C.PairwiseDisjoint (fun rho => closedBall rho R)
  have hCfinite : C.Finite := by
    simpa only [C] using
      dirichletExplicitFormulaCandidateSingularities_finite chi z w
  obtain ⟨delta, hdelta, hdeltaSubset⟩ :=
    hCfinite.isCompact.exists_cthickening_subset_open
      isOpen_interior hinterior
  by_cases hC : C.Nontrivial
  · have hinfsep : 0 < C.infsep :=
      hCfinite.infsep_pos_iff_nontrivial.mpr hC
    let R := min delta (C.infsep / 3)
    have hR : 0 < R := by
      exact lt_min hdelta (div_pos hinfsep (by norm_num))
    refine ⟨R, hR, ?_, ?_⟩
    · intro rho hrho
      exact (closedBall_subset_cthickening hrho R).trans
        ((cthickening_mono (min_le_left delta (C.infsep / 3)) C).trans
          hdeltaSubset)
    · rintro rho hrho sigma hsigma hne
      apply closedBall_disjoint_closedBall
      have hRsep : R ≤ C.infsep / 3 :=
        min_le_right delta (C.infsep / 3)
      calc
        R + R ≤ C.infsep / 3 + C.infsep / 3 :=
          add_le_add hRsep hRsep
        _ < C.infsep := by linarith
        _ ≤ dist rho sigma := infsep_le_dist_of_mem hrho hsigma hne
  · have hCsubsingleton : C.Subsingleton := not_nontrivial_iff.mp hC
    refine ⟨delta, hdelta, ?_, hCsubsingleton.pairwise _⟩
    intro rho hrho
    exact (closedBall_subset_cthickening hrho delta).trans hdeltaSubset

end BoundedGaps.Maynard
