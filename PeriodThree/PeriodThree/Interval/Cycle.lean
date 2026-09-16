module

public import PeriodThree.Interval.Covering

meta import all Mathlib.Tactic.Linarith -- shake: keep (used by cycle arithmetic)

/-!
# Finite interval cycles

This file turns a finite chain of exact compact pullbacks into a periodic point.
It is the finite-cycle construction used in the proof of [LY75, T1, pp. 987-988].
-/

@[expose] public section

open Set

namespace PeriodThree

private theorem existsIteratePullbackThroughSelfCover
    {J : Set ℝ} {F : ℝ → ℝ} (hF : ContinuousOn F J)
    {l r u v : ℝ} (hsource : Icc l r ⊆ J)
    (hself : Icc l r ⊆ F '' Icc l r) (huv : u ≤ v)
    (htarget : Icc u v ⊆ F '' Icc l r) (n : ℕ) :
    ∃ p q : ℝ, p ≤ q ∧ Icc p q ⊆ Icc l r ∧
      (F^[n + 1]) '' Icc p q = Icc u v ∧
      ∀ i, i < n + 1 → (F^[i]) '' Icc p q ⊆ Icc l r := by
  induction n with
  | zero =>
      obtain ⟨p, q, hpq, hpq_sub, hpq_image⟩ :=
        existsCompactIntervalPreimage ordConnected_Icc
          (hF.mono hsource) huv htarget
      refine ⟨p, q, hpq, hpq_sub, ?_, ?_⟩
      · simpa using hpq_image
      · intro i hi
        have hi0 : i = 0 := by omega
        simpa [hi0] using hpq_sub
  | succ n ih =>
      obtain ⟨p, q, hpq, hpq_sub, hpq_image, hpq_mem⟩ := ih
      obtain ⟨p', q', hpq', hpq'_sub, hpq'_image⟩ :=
        existsCompactIntervalPreimage ordConnected_Icc
          (hF.mono hsource) hpq (hpq_sub.trans hself)
      refine ⟨p', q', hpq', hpq'_sub, ?_, ?_⟩
      · have h_exp : n + 1 + 1 = (n + 1).succ := by omega
        rw [h_exp, Function.iterate_succ, Set.image_comp, hpq'_image, hpq_image]
      · intro i hi
        rcases i with _ | i
        · simpa using hpq'_sub
        · have hi' : i < n + 1 := by omega
          rw [Function.iterate_succ, Set.image_comp, hpq'_image]
          exact hpq_mem i hi'

/-- A repeated source interval followed by a target interval and a closing
cover has a periodic point following that finite cycle. This packages the
compact-pullback step in [LY75, proof of T1, pp. 987-988]. -/
theorem existsPeriodicPointOfRepeatedIntervalCover
    {J : Set ℝ} {F : ℝ → ℝ} (hF : ContinuousOn F J) (hFJ : MapsTo F J J)
    {l r u v : ℝ} (hsource : Icc l r ⊆ J)
    (hself : Icc l r ⊆ F '' Icc l r) (huv : u ≤ v)
    (htarget : Icc u v ⊆ F '' Icc l r) (hclose : Icc l r ⊆ F '' Icc u v)
    (n : ℕ) :
    ∃ x ∈ Icc l r, Function.IsPeriodicPt F (n + 2) x ∧
      (F^[n + 1]) x ∈ Icc u v ∧ ∀ i, i < n + 1 → (F^[i]) x ∈ Icc l r := by
  obtain ⟨p, q, hpq, hpq_sub, hpq_image, hpq_mem⟩ :=
    existsIteratePullbackThroughSelfCover hF hsource hself huv htarget n
  have hpqJ : Icc p q ⊆ J := hpq_sub.trans hsource
  have hsurj : Set.SurjOn (F^[n + 2]) (Icc p q) (Icc p q) := by
    intro x hx
    obtain ⟨z, hz, hzx⟩ := hclose (hpq_sub hx)
    obtain ⟨y, hy, hyz⟩ := (hpq_image ▸ hz : z ∈ (F^[n + 1]) '' Icc p q)
    refine ⟨y, hy, ?_⟩
    rw [show n + 2 = (n + 1).succ by omega, Function.iterate_succ_apply', hyz, hzx]
  obtain ⟨x, hx, hxfix⟩ :=
    exists_mem_Icc_isFixedPt_of_surjOn ((hF.iterate hFJ (n + 2)).mono hpqJ) hpq hsurj
  refine ⟨x, hpq_sub hx, hxfix, ?_, ?_⟩
  · rw [← hpq_image]
    exact ⟨x, hx, rfl⟩
  · intro i hi
    exact hpq_mem i hi ⟨x, hx, rfl⟩

end PeriodThree
