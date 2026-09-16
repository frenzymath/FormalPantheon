import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Uniform branch walls on a closed I6 fiber interval

For a positive closed interval `[l,h]`, this module translates the three Buchstab range
conditions for `y = (B - t) / t` into endpoint inequalities. The result is an algebraic bridge
for later fiber covers; it makes no claim about the exact band-complement region or any
integral.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.13), region `R_4`.
-/

open Set

namespace PrimesRestrictedDigits

noncomputable section

theorem sectionSixFirstLowBelowI6_fiber_branch_walls
    {B l h : Real} (hl : 0 < l) (hlh : l <= h) :
    ((∀ t ∈ Icc l h, 3 <= (B - t) / t) ↔ 4 * h <= B) ∧
    ((∀ t ∈ Icc l h,
        2 <= (B - t) / t ∧ (B - t) / t <= 3) ↔
      (3 * h <= B ∧ B <= 4 * l)) ∧
    ((∀ t ∈ Icc l h,
        1 <= (B - t) / t ∧ (B - t) / t <= 2) ↔
      (2 * h <= B ∧ B <= 3 * l)) := by
  have htpos : ∀ t ∈ Icc l h, 0 < t := by
    intro t ht
    exact hl.trans_le ht.1
  have htail : (∀ t ∈ Icc l h, 3 <= (B - t) / t) ↔ 4 * h <= B := by
    constructor
    · intro hall
      have hh := hall h ⟨hlh, le_rfl⟩
      rw [le_div_iff₀ (htpos h ⟨hlh, le_rfl⟩)] at hh
      linarith
    · intro hB t ht
      rw [le_div_iff₀ (htpos t ht)]
      linarith [ht.2]
  have hmiddle :
      (∀ t ∈ Icc l h,
        2 <= (B - t) / t ∧ (B - t) / t <= 3) ↔
        (3 * h <= B ∧ B <= 4 * l) := by
    constructor
    · intro hall
      have hh := (hall h ⟨hlh, le_rfl⟩).1
      have hlower := (hall l ⟨le_rfl, hlh⟩).2
      rw [le_div_iff₀ (htpos h ⟨hlh, le_rfl⟩)] at hh
      rw [div_le_iff₀ (htpos l ⟨le_rfl, hlh⟩)] at hlower
      constructor <;> linarith
    · rintro ⟨hB, hBl⟩ t ht
      constructor
      · rw [le_div_iff₀ (htpos t ht)]
        linarith [ht.2]
      · rw [div_le_iff₀ (htpos t ht)]
        linarith [ht.1]
  have hinverse :
      (∀ t ∈ Icc l h,
        1 <= (B - t) / t ∧ (B - t) / t <= 2) ↔
        (2 * h <= B ∧ B <= 3 * l) := by
    constructor
    · intro hall
      have hh := (hall h ⟨hlh, le_rfl⟩).1
      have hlower := (hall l ⟨le_rfl, hlh⟩).2
      rw [le_div_iff₀ (htpos h ⟨hlh, le_rfl⟩)] at hh
      rw [div_le_iff₀ (htpos l ⟨le_rfl, hlh⟩)] at hlower
      constructor <;> linarith
    · rintro ⟨hB, hBl⟩ t ht
      constructor
      · rw [le_div_iff₀ (htpos t ht)]
        linarith [ht.2]
      · rw [div_le_iff₀ (htpos t ht)]
        linarith [ht.1]
  exact ⟨htail, hmiddle, hinverse⟩

end

end PrimesRestrictedDigits
