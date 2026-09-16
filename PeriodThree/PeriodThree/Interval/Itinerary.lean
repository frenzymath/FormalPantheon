module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.Compact

/-!
# Infinite compact-interval itineraries

This file proves Li and Yorke's nested-itinerary realization lemma by taking a
nested intersection of finite-path solution sets.
-/

@[expose] public section

open Set

namespace PeriodThree

/-- A sequence of nonempty compact intervals with each next interval covered by
the image of its predecessor has a point following the whole itinerary. This is
[LY75, Lemma 1, p. 987]. -/
theorem existsOrbitFollowingIntervals
    {J : Set ℝ} {F : ℝ → ℝ} (hF : ContinuousOn F J) (hFJ : MapsTo F J J)
    {l r : ℕ → ℝ} (hlr : ∀ n, l n ≤ r n)
    (hsub : ∀ n, Icc (l n) (r n) ⊆ J)
    (hcover : ∀ n, Icc (l (n + 1)) (r (n + 1)) ⊆ F '' Icc (l n) (r n)) :
    ∃ x ∈ Icc (l 0) (r 0), ∀ n, (F^[n]) x ∈ Icc (l n) (r n) := by
  have hpath : ∀ n y, y ∈ Icc (l n) (r n) →
      ∃ x ∈ Icc (l 0) (r 0), (F^[n]) x = y ∧
        ∀ i, i ≤ n → (F^[i]) x ∈ Icc (l i) (r i) := by
    intro n
    induction n with
    | zero =>
        intro y hy
        refine ⟨y, hy, by simp, ?_⟩
        intro i hi
        have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
        simpa [hi0] using hy
    | succ n ih =>
        intro y hy
        obtain ⟨z, hz, hzy⟩ := hcover n (by simpa [Nat.succ_eq_add_one] using hy)
        obtain ⟨x, hx0, hxn, hxall⟩ := ih z hz
        refine ⟨x, hx0, ?_, ?_⟩
        · rw [Function.iterate_succ_apply', hxn, hzy]
        · intro i hi
          rcases Nat.lt_or_eq_of_le hi with hlt | rfl
          · exact hxall i (Nat.le_of_lt_succ hlt)
          · simpa only [Function.iterate_succ_apply', hxn, hzy] using hy
  let I0 : Set ℝ := Icc (l 0) (r 0)
  let Q : ℕ → Set I0 := fun n =>
    {x | ∀ i, i ≤ n → (F^[i]) (x : ℝ) ∈ Icc (l i) (r i)}
  letI : CompactSpace I0 := isCompact_iff_compactSpace.mp isCompact_Icc
  have hI0J : I0 ⊆ J := hsub 0
  have hQclosed (n : ℕ) : IsClosed (Q n) := by
    rw [show Q n = ⋂ i, ⋂ (_ : i ≤ n),
        {x : I0 | (F^[i]) (x : ℝ) ∈ Icc (l i) (r i)} by
      ext x
      simp [Q]]
    exact isClosed_iInter fun i => isClosed_iInter fun _ =>
      isClosed_Icc.preimage (((hF.iterate hFJ i).mono hI0J).restrict)
  have hQnonempty (n : ℕ) : (Q n).Nonempty := by
    obtain ⟨x, hx0, _, hxall⟩ := hpath n (l n) (left_mem_Icc.mpr (hlr n))
    exact ⟨⟨x, hx0⟩, hxall⟩
  have hQnested (n : ℕ) : Q (n + 1) ⊆ Q n := by
    intro x hx i hi
    exact hx i (hi.trans (Nat.le_succ n))
  have hinter : (⋂ n, Q n).Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed Q hQnested hQnonempty
      (hQclosed 0).isCompact hQclosed
  obtain ⟨x, hx⟩ := hinter
  refine ⟨x, x.property, ?_⟩
  intro n
  exact (mem_iInter.mp hx n) n le_rfl

end PeriodThree
