import PrimesRestrictedDigits.SieveAsymptotics.SectionSixP2ClampedIntervalAlgebraD976

/-!
# Exact endpoints for the original refined P2 profile

Flatten the nested clamps without changing its coefficients or argument order. Source:
`MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.12).
-/

set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace PrimesRestrictedDigits

private theorem clamp_half_eq_D984 (d W B x : Real) (hx : x ≤ B / 2) :
    sectionSixBuchstabClamp d (min W (B / 2)) x =
      sectionSixBuchstabClamp d W x := by
  unfold sectionSixBuchstabClamp
  rw [min_assoc, min_eq_right hx]

private theorem cuts_in_half_D984 (B d W : Real) (hB : 0 ≤ B) :
    let h := min W (B / 2)
    let m13 := sectionSixBuchstabClamp d h (4 * B / 17)
    let m4 := sectionSixBuchstabClamp m13 h (B / 4)
    let m3 := sectionSixBuchstabClamp m4 h (B / 3)
    m4 = sectionSixBuchstabClamp d h (B / 4) ∧
      m3 = sectionSixBuchstabClamp d h (B / 3) := by
  dsimp only
  have hquarter : 4 * B / 17 ≤ B / 4 := by linarith
  have hthird : B / 4 ≤ B / 3 := by linarith
  rw [sectionSixBuchstabClamp_raiseLower_D976 hquarter]
  exact ⟨rfl, sectionSixBuchstabClamp_raiseLower_D976 hthird⟩

theorem sectionSixBuchstabRefinedCuts_eq_D984 (B d W : Real) (hB : 0 ≤ B) :
    let h := min W (B / 2)
    let m13 := sectionSixBuchstabClamp d h (4 * B / 17)
    let m4 := sectionSixBuchstabClamp m13 h (B / 4)
    let m3 := sectionSixBuchstabClamp m4 h (B / 3)
    m13 = sectionSixBuchstabClamp d W (4 * B / 17) ∧
      m4 = sectionSixBuchstabClamp d W (B / 4) ∧
      m3 = sectionSixBuchstabClamp d W (B / 3) := by
  dsimp only
  obtain ⟨hm4, hm3⟩ := cuts_in_half_D984 B d W hB
  exact ⟨clamp_half_eq_D984 d W B _ (by linarith),
    hm4.trans (clamp_half_eq_D984 d W B _ (by linarith)),
    hm3.trans (clamp_half_eq_D984 d W B _ (by linarith))⟩

private theorem middle_raw_D984 (B : Real) (i : Fin 8) :
    B / (uniformRealGridUpper (2 : Real) 3 i + 1) = 8 * B / (25 + (i : Nat)) ∧
      B / (uniformRealGridLower (2 : Real) 3 i + 1) = 8 * B / (24 + (i : Nat)) := by
  fin_cases i <;> constructor <;>
    norm_num [uniformRealGridLower, uniformRealGridUpper] <;> ring

private theorem inverse_raw_D984 (B : Real) (i : Fin 8) :
    B / (uniformRealGridUpper (1 : Real) 2 i + 1) = 8 * B / (17 + (i : Nat)) ∧
      B / (uniformRealGridLower (1 : Real) 2 i + 1) = 8 * B / (16 + (i : Nat)) := by
  fin_cases i <;> constructor <;>
    norm_num [uniformRealGridLower, uniformRealGridUpper] <;> ring

theorem sectionSixBuchstabRefinedMiddleCell_eq_D984
    (B d W : Real) (hB : 0 ≤ B) (i : Fin 8) :
    let h := min W (B / 2)
    let m13 := sectionSixBuchstabClamp d h (4 * B / 17)
    let m4 := sectionSixBuchstabClamp m13 h (B / 4)
    let m3 := sectionSixBuchstabClamp m4 h (B / 3)
    sectionSixBuchstabArgumentCell B m4 m3
      (uniformRealGridLower (2 : Real) 3 i) (uniformRealGridUpper (2 : Real) 3 i) =
      (sectionSixBuchstabClamp d W (8 * B / (25 + (i : Nat))),
        sectionSixBuchstabClamp d W (8 * B / (24 + (i : Nat)))) := by
  dsimp only
  obtain ⟨hm4, hm3⟩ := cuts_in_half_D984 B d W hB
  obtain ⟨hrawL, hrawH⟩ := middle_raw_D984 B i
  have hLlo : B / 4 ≤ 8 * B / (25 + (i : Nat)) := by
    fin_cases i <;> norm_num <;> linarith
  have hLhi : 8 * B / (25 + (i : Nat)) ≤ B / 3 := by
    fin_cases i <;> norm_num <;> linarith
  have hHlo : B / 4 ≤ 8 * B / (24 + (i : Nat)) := by
    fin_cases i <;> norm_num <;> linarith
  have hHhi : 8 * B / (24 + (i : Nat)) ≤ B / 3 := by
    fin_cases i <;> norm_num <;> linarith
  unfold sectionSixBuchstabArgumentCell
  rw [hm3, hm4, hrawL, hrawH,
    sectionSixBuchstabClamp_between_D976 hLlo hLhi,
    sectionSixBuchstabClamp_between_D976 hHlo hHhi]
  exact Prod.ext
    (clamp_half_eq_D984 d W B _ (by linarith))
    (clamp_half_eq_D984 d W B _ (by linarith))

theorem sectionSixBuchstabRefinedInverseCell_eq_D984
    (B d W : Real) (hB : 0 ≤ B) (i : Fin 8) :
    let h := min W (B / 2)
    let m13 := sectionSixBuchstabClamp d h (4 * B / 17)
    let m4 := sectionSixBuchstabClamp m13 h (B / 4)
    let m3 := sectionSixBuchstabClamp m4 h (B / 3)
    sectionSixBuchstabArgumentCell B m3 h
      (uniformRealGridLower (1 : Real) 2 i) (uniformRealGridUpper (1 : Real) 2 i) =
      (sectionSixBuchstabClamp d W (8 * B / (17 + (i : Nat))),
        sectionSixBuchstabClamp d W (8 * B / (16 + (i : Nat)))) := by
  dsimp only
  have hm3 := (cuts_in_half_D984 B d W hB).2
  obtain ⟨hrawL, hrawH⟩ := inverse_raw_D984 B i
  have hLlo : B / 3 ≤ 8 * B / (17 + (i : Nat)) := by
    fin_cases i <;> norm_num <;> linarith
  have hLhi : 8 * B / (17 + (i : Nat)) ≤ B / 2 := by
    fin_cases i <;> norm_num <;> linarith
  have hHlo : B / 3 ≤ 8 * B / (16 + (i : Nat)) := by
    fin_cases i <;> norm_num <;> linarith
  have hHhi : 8 * B / (16 + (i : Nat)) ≤ B / 2 := by
    fin_cases i <;> norm_num <;> linarith
  unfold sectionSixBuchstabArgumentCell
  rw [hm3, hrawL, hrawH,
    sectionSixBuchstabClamp_raiseLower_D976 hLlo,
    sectionSixBuchstabClamp_raiseLower_D976 hHlo]
  exact Prod.ext (clamp_half_eq_D984 d W B _ hLhi)
    (clamp_half_eq_D984 d W B _ hHhi)

theorem sectionSixBuchstabRefinedFiberBound_eq_flat_D984
    (u v d W B : Real) (hB : 0 ≤ B) :
    sectionSixBuchstabRefinedFiberBound u v W B d (min W (B / 2)) =
      sectionSixBuchstabConstantPayload u v W d
        (sectionSixBuchstabClamp d W (4 * B / 17)) (281 / 500) +
      sectionSixBuchstabConstantPayload u v W
        (sectionSixBuchstabClamp d W (4 * B / 17))
        (sectionSixBuchstabClamp d W (B / 4)) (564383 / 1000000) +
      (∑ i : Fin 8, sectionSixBuchstabConstantPayload u v W
        (sectionSixBuchstabClamp d W (8 * B / (25 + (i : Nat))))
        (sectionSixBuchstabClamp d W (8 * B / (24 + (i : Nat))))
        (sectionSixBuchstabMiddleEightCellCap i)) +
      ∑ i : Fin 8, sectionSixBuchstabSecantPayload u v W B
        (sectionSixBuchstabClamp d W (8 * B / (17 + (i : Nat))))
        (sectionSixBuchstabClamp d W (8 * B / (16 + (i : Nat))))
        (uniformRealGridLower (1 : Real) 2 i) (uniformRealGridUpper (1 : Real) 2 i) := by
  obtain ⟨hm13, hm4, _⟩ := sectionSixBuchstabRefinedCuts_eq_D984 B d W hB
  simp only [sectionSixBuchstabRefinedFiberBound,
    sectionSixBuchstabRefinedMiddleCell_eq_D984 B d W hB,
    sectionSixBuchstabRefinedInverseCell_eq_D984 B d W hB]
  rw [hm4, hm13]

end PrimesRestrictedDigits
