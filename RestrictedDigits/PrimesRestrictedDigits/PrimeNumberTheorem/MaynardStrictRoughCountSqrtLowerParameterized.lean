import PrimesRestrictedDigits.PrimeNumberTheorem.MaynardBuchstabAsymptotic
import PrimesRestrictedDigits.PrimeNumberTheorem.MaynardStrictRoughCountSqrtGap
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Parameterized strict square-root rough-count lower envelope

Every coefficient strictly below the limiting coefficient one is eventually available for the
strict square-root carrier. This is the form intended for the later positive-main-term
assembly.

Source: `MAYNARD-PRD-PUBLISHED`, Sections 5--6.
-/

namespace PrimesRestrictedDigits

open Filter Asymptotics

theorem exists_maynardStrictRoughCount_sqrt_lower_of_lt_one
    {c : Real} (hc : 0 < c) (hc1 : c < 1) :
    ∃ Y0 : Real, 4 ≤ Y0 ∧ ∀ Y : Real, Y0 ≤ Y ->
      c * (Y / Real.log Y) ≤
        (maynardStrictRoughCount Y (Real.sqrt Y) : Real) := by
  let d : Real := (1 + c) / 2
  have hd0 : 0 < d := by dsimp [d]; linarith
  have hdc : 0 < d - c := by dsimp [d]; linarith
  have hd1 : d < 1 := by dsimp [d]; linarith
  have hlim := tendsto_maynardRoughCount_power_normalized
    (u := (2 : Real)) (by norm_num)
  have hlim' : Tendsto
      (fun Y : Real =>
        (maynardRoughCount Y (Y ^ (1 / (2 : Real))) : Real) /
          ((2 : Real) * Y / Real.log Y))
      atTop (nhds (1 / 2 : Real)) := by
    simpa using hlim
  have hnorm : ∀ᶠ Y : Real in atTop,
      d / 2 <
        (maynardRoughCount Y (Y ^ (1 / (2 : Real))) : Real) /
          ((2 : Real) * Y / Real.log Y) :=
    (tendsto_order.mp hlim').1 (d / 2) (by dsimp [d]; linarith)
  have hY : ∀ᶠ Y : Real in atTop, 1 < Y := eventually_gt_atTop 1
  have hroughEvent : ∀ᶠ Y : Real in atTop,
      d * (Y / Real.log Y) <
        (maynardRoughCount Y (Real.sqrt Y) : Real) := by
    filter_upwards [hnorm, hY] with Y hnormY hYone
    have hlog : 0 < Real.log Y := Real.log_pos hYone
    have hden : 0 < (2 : Real) * Y / Real.log Y := by positivity
    have hscaled := (lt_div_iff₀ hden).mp hnormY
    have hsqrt : Y ^ (1 / (2 : Real)) = Real.sqrt Y := by
      symm
      exact Real.sqrt_eq_rpow Y
    rw [hsqrt] at hscaled
    have hrewrite : d * (Y / Real.log Y) =
        (d / 2) * (2 * Y / Real.log Y) := by ring
    rw [hrewrite]
    exact hscaled
  obtain ⟨Er, hEr⟩ := eventually_atTop.mp hroughEvent
  have hsmall := Real.isLittleO_log_id_atTop.bound hdc
  obtain ⟨Eg, hEg⟩ := Filter.eventually_atTop.mp hsmall
  have hYevent := Filter.tendsto_id.eventually_ge_atTop (2 : Real)
  obtain ⟨Bg, hBg⟩ := Filter.eventually_atTop.mp hYevent
  let Y0 : Real := max 4 (max Er (max Eg Bg))
  refine ⟨Y0, le_max_left _ _, ?_⟩
  intro Y hY0
  have hEr' : Er ≤ Y :=
    (le_max_left Er (max Eg Bg)).trans
      (le_max_right 4 (max Er (max Eg Bg))) |>.trans hY0
  have hEg' : Eg ≤ Y :=
    (le_max_left Eg Bg).trans (le_max_right Er (max Eg Bg)) |>.trans
      (le_max_right 4 (max Er (max Eg Bg))) |>.trans hY0
  have hBg' : Bg ≤ Y :=
    (le_max_right Eg Bg).trans (le_max_right Er (max Eg Bg)) |>.trans
      (le_max_right 4 (max Er (max Eg Bg))) |>.trans hY0
  have hY2 : 2 ≤ Y := by simpa only [id_eq] using hBg Y hBg'
  have hY1 : 1 < Y := by linarith
  have hlog : 0 < Real.log Y := Real.log_pos hY1
  have hbound := hEg Y hEg'
  change ‖Real.log Y‖ ≤ (d - c) * ‖Y‖ at hbound
  rw [Real.norm_of_nonneg (Real.log_nonneg hY1.le),
    Real.norm_of_nonneg (by linarith : 0 ≤ Y)] at hbound
  have hA : (1 : Real) ≤ (d - c) * (Y / Real.log Y) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hlog).2
    nlinarith [hbound]
  have hrough := hEr Y hEr'
  have hgapNat := maynardRoughCount_sqrt_le_strict_add_one
    (show 4 ≤ Y by exact (le_max_left 4 _).trans hY0)
  have hgap : (maynardRoughCount Y (Real.sqrt Y) : Real) ≤
      (maynardStrictRoughCount Y (Real.sqrt Y) : Real) + 1 := by
    exact_mod_cast hgapNat
  have hmain : d * (Y / Real.log Y) - 1 <
      (maynardStrictRoughCount Y (Real.sqrt Y) : Real) := by
    linarith
  have hcoef : c * (Y / Real.log Y) ≤
      d * (Y / Real.log Y) - 1 := by
    nlinarith [hA]
  exact hcoef.trans_lt hmain |>.le

end PrimesRestrictedDigits
