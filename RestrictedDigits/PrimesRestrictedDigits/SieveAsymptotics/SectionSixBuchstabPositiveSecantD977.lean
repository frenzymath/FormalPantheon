import PrimesRestrictedDigits.SieveAsymptotics.SectionSixBuchstabEightSecantFiberD900D

/-!
# Sign-safe rational Buchstab payloads

Exact factorization preserves the inverse secant's negative correction. Source context:
`MAYNARD-PRD-PUBLISHED`, Section 6, Eqs. (6.12)-(6.13).
-/

set_option autoImplicit false
set_option warningAsError true

namespace PrimesRestrictedDigits

theorem sectionSixBuchstabConstantPayload_eq_width_D977
    (u v w l h C : Real) (hl : l ≠ 0) (hh : h ≠ 0) :
    sectionSixBuchstabConstantPayload u v w l h C =
      C * (h - l) / (u * v * w * l * h) := by
  by_cases hU : u * v * w = 0
  · simp [sectionSixBuchstabConstantPayload, hU]
  · rcases mul_ne_zero_iff.mp hU with ⟨huv, hw⟩
    rcases mul_ne_zero_iff.mp huv with ⟨hu, hv⟩
    unfold sectionSixBuchstabConstantPayload
    field_simp [hu, hv, hw, hl, hh]

theorem sectionSixBuchstabSecantPayload_eq_positiveSplit_D977
    (u v w B l h a b : Real)
    (hl : l ≠ 0) (hh : h ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    sectionSixBuchstabSecantPayload u v w B l h a b =
      ((h - l) * ((a + b + 1) * h - B) / (u * v * w * l * h ^ 2) +
        (h - l) * ((a + b + 1) * l - B) / (u * v * w * l ^ 2 * h)) /
          (2 * a * b) := by
  by_cases hU : u * v * w = 0
  · simp [sectionSixBuchstabSecantPayload, hU]
  · rcases mul_ne_zero_iff.mp hU with ⟨huv, hw⟩
    rcases mul_ne_zero_iff.mp huv with ⟨hu, hv⟩
    unfold sectionSixBuchstabSecantPayload
    field_simp [hu, hv, hw, hl, hh, ha, hb]
    ring

theorem sectionSixBuchstabSecantPayload_nonneg_D977
    {u v w B l h a b : Real}
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (hl : 0 < l) (hlh : l ≤ h) (ha : 0 < a) (hb : 0 < b)
    (hupper : B ≤ (b + 1) * l) :
    0 ≤ sectionSixBuchstabSecantPayload u v w B l h a b := by
  have hh : 0 < h := hl.trans_le hlh
  have hc : 0 ≤ a + b + 1 := by positivity
  have hlow : 0 ≤ (a + b + 1) * l - B := by
    nlinarith [mul_pos ha hl]
  have hhigh : 0 ≤ (a + b + 1) * h - B := by
    nlinarith [mul_nonneg hc (sub_nonneg.mpr hlh)]
  rw [sectionSixBuchstabSecantPayload_eq_positiveSplit_D977
    u v w B l h a b hl.ne' hh.ne' ha.ne' hb.ne']
  apply div_nonneg _ (by positivity)
  exact add_nonneg
    (div_nonneg (mul_nonneg (sub_nonneg.mpr hlh) hhigh) (by positivity))
    (div_nonneg (mul_nonneg (sub_nonneg.mpr hlh) hlow) (by positivity))

end PrimesRestrictedDigits
