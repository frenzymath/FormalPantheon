import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Prime.Basic
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-!
# The explicit 105-tuple used for the constant 600

The tuple is the one printed in the footnote following the proof of
Maynard2013v3, Theorem 1.3.  Admissibility is expressed by the equivalent
finite residue condition: for every prime `p`, the residues of the tuple
modulo `p` occupy fewer than all `p` classes.
-/

namespace BoundedGaps

def IsAdmissible (H : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → (H.image (fun h => h % p)).card < p

theorem isAdmissible_iff_avoids_residue (H : Finset ℕ) : IsAdmissible H ↔
    ∀ p : ℕ, p.Prime → ∃ a < p, ∀ h ∈ H, h % p ≠ a := by
  constructor
  · intro h p hp
    let R := H.image (fun h => h % p)
    have hRsub : R ⊆ Finset.range p := by
      intro a ha
      obtain ⟨h', hh', rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_range.mpr
        (Nat.mod_lt _ (Nat.lt_of_lt_of_le Nat.zero_lt_two hp.two_le))
    have hcard : R.card < (Finset.range p).card := by
      simpa [R] using h p hp
    obtain ⟨a, ha⟩ := Finset.sdiff_nonempty_of_card_lt_card hcard
    have ha' := Finset.mem_sdiff.mp ha
    refine ⟨a, Finset.mem_range.mp ha'.1, ?_⟩
    intro h' hh' hmod
    apply ha'.2
    exact Finset.mem_image.mpr ⟨h', hh', hmod⟩
  · intro h p hp
    obtain ⟨a, ha_lt, ha_avoid⟩ := h p hp
    have hRsub : H.image (fun h => h % p) ⊆ Finset.range p := by
      intro b hb
      obtain ⟨h', hh', rfl⟩ := Finset.mem_image.mp hb
      exact Finset.mem_range.mpr
        (Nat.mod_lt _ (Nat.lt_of_lt_of_le Nat.zero_lt_two hp.two_le))
    have hRne : H.image (fun h => h % p) ≠ Finset.range p := by
      intro hEq
      have : a ∈ H.image (fun h => h % p) := by
        rw [hEq]
        exact Finset.mem_range.mpr ha_lt
      obtain ⟨h', hh', hmod⟩ := Finset.mem_image.mp this
      exact ha_avoid h' hh' hmod
    simpa using Finset.card_lt_card
      (Finset.ssubset_iff_subset_ne.mpr ⟨hRsub, hRne⟩)

def engelsmaTuple : Finset ℕ :=
  [0, 10, 12, 24, 28, 30, 34, 42, 48, 52, 54, 64, 70, 72, 78, 82, 90, 94,
    100, 112, 114, 118, 120, 124, 132, 138, 148, 154, 168, 174, 178, 180,
    184, 190, 192, 202, 204, 208, 220, 222, 232, 234, 250, 252, 258, 262,
    264, 268, 280, 288, 294, 300, 310, 322, 324, 328, 330, 334, 342, 352,
    358, 360, 364, 372, 378, 384, 390, 394, 400, 402, 408, 412, 418, 420,
    430, 432, 442, 444, 450, 454, 462, 468, 472, 478, 484, 490, 492, 498,
    504, 510, 528, 532, 534, 538, 544, 558, 562, 570, 574, 580, 582, 588,
    594, 598, 600].toFinset

theorem engelsmaTuple_card : engelsmaTuple.card = 105 := by
  decide

theorem engelsmaTuple_mem_zero : 0 ∈ engelsmaTuple := by decide

theorem engelsmaTuple_mem_six_hundred : 600 ∈ engelsmaTuple := by decide

theorem engelsmaTuple_le_six_hundred {h : ℕ} (hh : h ∈ engelsmaTuple) :
    h ≤ 600 := by
  simp [engelsmaTuple] at hh
  omega

private theorem admissible_of_card_lt_prime {H : Finset ℕ} {p : ℕ}
    (hcard : H.card < p) :
    (H.image (fun h => h % p)).card < p := by
  exact (Finset.card_image_le.trans_lt hcard)

theorem engelsmaTuple_admissible : IsAdmissible engelsmaTuple := by
  intro p hp
  by_cases hsmall : p ≤ engelsmaTuple.card
  · rw [engelsmaTuple_card] at hsmall
    have hfinite : ∀ q ∈ Finset.range 106, q.Prime →
        (engelsmaTuple.image (fun h => h % q)).card < q := by
      decide
    exact hfinite p (by simp [Nat.lt_succ_iff, hsmall]) hp
  · exact admissible_of_card_lt_prime (Nat.lt_of_not_ge hsmall)

theorem engelsmaTuple_sorted_bounds :
    engelsmaTuple.card = 105 ∧
      (∀ h ∈ engelsmaTuple, h ≤ 600) ∧
      0 ∈ engelsmaTuple ∧ 600 ∈ engelsmaTuple := by
  exact ⟨engelsmaTuple_card, (fun h hh => engelsmaTuple_le_six_hundred hh),
    engelsmaTuple_mem_zero, engelsmaTuple_mem_six_hundred⟩

end BoundedGaps
