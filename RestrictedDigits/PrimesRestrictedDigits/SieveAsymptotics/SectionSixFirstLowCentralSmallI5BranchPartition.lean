import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5Argument
import Mathlib.Tactic.Linarith

/-!
# I5 Buchstab branch range equivalences

This is the endpoint-safe algebraic bridge for the low-central-small outer
carrier in Maynard's Section 6, Eq. (6.12). It proves range equivalences only;
it does not assert a disjoint partition or a numerical integral bound.
-/

namespace PrimesRestrictedDigits

private theorem i5_branch_partition_of_pos {B t : Real} (ht : 0 < t) :
    (3 <= (B - t) / t ↔ 4 * t <= B) ∧
    ((2 <= (B - t) / t ∧ (B - t) / t <= 3) ↔
      (3 * t <= B ∧ B <= 4 * t)) ∧
    ((1 <= (B - t) / t ∧ (B - t) / t <= 2) ↔
      (B <= 3 * t ∧ 2 * t <= B)) := by
  have htail : 3 <= (B - t) / t ↔ 4 * t <= B := by
    constructor
    · intro h
      have h' := (le_div_iff₀ ht).mp h
      linarith
    · intro h
      apply (le_div_iff₀ ht).2
      linarith
  have hmiddle :
      ((2 <= (B - t) / t ∧ (B - t) / t <= 3) ↔
        (3 * t <= B ∧ B <= 4 * t)) := by
    constructor
    · rintro ⟨h2, h3⟩
      have h2' := (le_div_iff₀ ht).mp h2
      have h3' := (div_le_iff₀ ht).mp h3
      constructor <;> linarith
    · rintro ⟨h2, h3⟩
      constructor
      · apply (le_div_iff₀ ht).2
        linarith
      · apply (div_le_iff₀ ht).2
        linarith
  have hinverse :
      ((1 <= (B - t) / t ∧ (B - t) / t <= 2) ↔
        (B <= 3 * t ∧ 2 * t <= B)) := by
    constructor
    · rintro ⟨h1, h2⟩
      have h1' := (le_div_iff₀ ht).mp h1
      have h2' := (div_le_iff₀ ht).mp h2
      constructor <;> linarith
    · rintro ⟨h2, h1⟩
      constructor
      · apply (le_div_iff₀ ht).2
        linarith
      · apply (div_le_iff₀ ht).2
        linarith
  exact ⟨htail, hmiddle, hinverse⟩

theorem sectionSixFirstLowCentralSmallUniformOuter_branch_partition
    {delta : Real} {x : (((Real × Real) × Real) × Real)}
    (hgap : 0 < sectionSixThetaGap delta)
    (hx : x ∈ sectionSixFirstLowCentralSmallUniformOuterRegion delta) :
    (3 <= (1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2 ↔
      4 * x.2 <= 1 - x.1.1.1 - x.1.1.2 - x.1.2) ∧
    ((2 <= (1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2 ∧
        (1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2 <= 3) ↔
      (3 * x.2 <= 1 - x.1.1.1 - x.1.1.2 - x.1.2 ∧
        1 - x.1.1.1 - x.1.1.2 - x.1.2 <= 4 * x.2)) ∧
    ((1 <= (1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2 ∧
        (1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2 <= 2) ↔
      (1 - x.1.1.1 - x.1.1.2 - x.1.2 <= 3 * x.2 ∧
        2 * x.2 <= 1 - x.1.1.1 - x.1.1.2 - x.1.2)) := by
  have htPos : 0 < x.2 := hgap.trans hx.1
  exact i5_branch_partition_of_pos
    (B := 1 - x.1.1.1 - x.1.1.2 - x.1.2) (t := x.2) htPos

end PrimesRestrictedDigits
