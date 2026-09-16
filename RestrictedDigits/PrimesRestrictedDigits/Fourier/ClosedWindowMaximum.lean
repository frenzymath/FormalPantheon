import Mathlib.Algebra.Ring.Periodic
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Maxima on closed perturbation windows

This file implements the compact replacement for the open perturbation supremum in
`MAYNARD-PRD-PUBLISHED`, Lemma 10.5, pp. 175--178.
-/

namespace PrimesRestrictedDigits

/-- The maximum value of `f (x + eta)` over the closed window
`-delta <= eta <= delta`. The useful API assumes `0 <= delta`. -/
noncomputable def closedWindowMaximum
    (f : Real -> Real) (delta x : Real) : Real :=
  sSup ((fun eta : Real => f (x + eta)) '' Set.Icc (-delta) delta)

theorem exists_closedWindowMaximum_eq
    {f : Real -> Real} (hf : Continuous f) {delta : Real}
    (hdelta : 0 <= delta) (x : Real) :
    ∃ eta ∈ Set.Icc (-delta) delta,
      closedWindowMaximum f delta x = f (x + eta) := by
  have hcompact : IsCompact (Set.Icc (-delta) delta) := isCompact_Icc
  have hnonempty : (Set.Icc (-delta) delta).Nonempty :=
    ⟨0, by constructor <;> linarith⟩
  obtain ⟨eta, heta, hmax⟩ := UpperSemicontinuousOn.exists_isMaxOn
    hnonempty hcompact
      ((hf.comp (continuous_const.add continuous_id)).continuousOn.upperSemicontinuousOn)
  refine ⟨eta, heta, ?_⟩
  apply IsGreatest.csSup_eq
  constructor
  · exact ⟨eta, heta, rfl⟩
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact hmax hz

theorem le_closedWindowMaximum
    {f : Real -> Real} (hf : Continuous f) {delta : Real}
    (_hdelta : 0 <= delta) (x : Real) {eta : Real}
    (heta : eta ∈ Set.Icc (-delta) delta) :
    f (x + eta) <= closedWindowMaximum f delta x := by
  rw [closedWindowMaximum]
  apply le_csSup
  · exact (isCompact_Icc.image
      (hf.comp (continuous_const.add continuous_id))).bddAbove
  · exact ⟨eta, heta, rfl⟩

theorem closedWindowMaximum_nonneg
    {f : Real -> Real} (hf : Continuous f) (hf0 : ∀ x, 0 <= f x)
    {delta : Real} (hdelta : 0 <= delta) (x : Real) :
    0 <= closedWindowMaximum f delta x := by
  exact (hf0 (x + 0)).trans
    (le_closedWindowMaximum hf hdelta x ⟨by linarith, hdelta⟩)

theorem closedWindowMaximum_mono
    {f g : Real -> Real} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ x, f x <= g x) {delta : Real} (hdelta : 0 <= delta)
    (x : Real) :
    closedWindowMaximum f delta x <= closedWindowMaximum g delta x := by
  obtain ⟨eta, heta, hmax⟩ := exists_closedWindowMaximum_eq hf hdelta x
  rw [hmax]
  exact (hfg _).trans (le_closedWindowMaximum hg hdelta x heta)

theorem closedWindowMaximum_zero
    {f : Real -> Real} (hf : Continuous f) (x : Real) :
    closedWindowMaximum f 0 x = f x := by
  obtain ⟨eta, heta, hmax⟩ := exists_closedWindowMaximum_eq hf le_rfl x
  have heta0 : eta = 0 := by
    rw [Set.mem_Icc] at heta
    linarith
  simpa [heta0] using hmax

theorem closedWindowMaximum_add_period
    {f : Real -> Real} (hf : Continuous f) (hp : Function.Periodic f 1)
    {delta : Real} (hdelta : 0 <= delta) (x : Real) :
    closedWindowMaximum f delta (x + 1) =
      closedWindowMaximum f delta x := by
  obtain ⟨eta, heta, hleft⟩ :=
    exists_closedWindowMaximum_eq hf hdelta (x + 1)
  obtain ⟨z, hz, hright⟩ := exists_closedWindowMaximum_eq hf hdelta x
  rw [hleft, hright]
  apply le_antisymm
  · rw [show x + 1 + eta = (x + eta) + 1 by ring, hp]
    rw [← hright]
    exact le_closedWindowMaximum hf hdelta x heta
  · rw [show x + z = (x + 1 + z) - 1 by ring, hp.sub_eq]
    rw [← hleft]
    exact le_closedWindowMaximum hf hdelta (x + 1) hz

end PrimesRestrictedDigits
