import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Curvature-controlled cell interpolation

If adding a positive quadratic makes a function convex on a closed cell, its
value throughout the cell is bounded by the larger endpoint value plus the
quadratic curvature error. This replaces an uncertified interior-extremum
search in the later digit-kernel certificate.
-/

namespace PrimesRestrictedDigits

theorem le_max_endpoints_add_curvature_of_convexOn
    {f : ℝ → ℝ} {a b x M : ℝ}
    (hab : a ≤ b) (hx : x ∈ Set.Icc a b) (hM : 0 ≤ M)
    (hconv : ConvexOn ℝ (Set.Icc a b)
      (fun y => f y + (M / 2) * y ^ 2)) :
    f x ≤ max (f a) (f b) + M * (b - a) ^ 2 / 8 := by
  rcases hx with ⟨hax, hxb⟩
  by_cases hab0 : a = b
  · subst b
    have hxa : x = a := le_antisymm hxb hax
    subst x
    calc
      f a ≤ max (f a) (f a) := le_max_left _ _
      _ ≤ max (f a) (f a) + M * (a - a) ^ 2 / 8 := by
        have : 0 ≤ M * (a - a) ^ 2 / 8 := by positivity
        exact le_add_of_nonneg_right this
  · have hablt : a < b := lt_of_le_of_ne hab hab0
    let s : ℝ := (b - x) / (b - a)
    let t : ℝ := (x - a) / (b - a)
    have hw : 0 < b - a := sub_pos.mpr hablt
    have hs : 0 ≤ s := by
      dsimp [s]
      exact div_nonneg (sub_nonneg.mpr hxb) (le_of_lt hw)
    have ht : 0 ≤ t := by
      dsimp [t]
      exact div_nonneg (sub_nonneg.mpr hax) (le_of_lt hw)
    have hst : s + t = 1 := by
      dsimp [s, t]
      field_simp
      ring
    have hpoint : s • a + t • b = x := by
      dsimp [s, t]
      field_simp
      ring
    have hconvx := hconv.2 (show a ∈ Set.Icc a b by exact ⟨le_rfl, hab⟩)
      (show b ∈ Set.Icc a b by exact ⟨hab, le_rfl⟩) hs ht hst
    have hconvx' :
        f x + (M / 2) * x ^ 2 ≤
          (s * f a + t * f b) + (M / 2) * (s * a ^ 2 + t * b ^ 2) := by
      rw [hpoint] at hconvx
      change f x + (M / 2) * x ^ 2 ≤
        s * (f a + (M / 2) * a ^ 2) +
          t * (f b + (M / 2) * b ^ 2) at hconvx
      calc
        f x + (M / 2) * x ^ 2 ≤
            s * (f a + (M / 2) * a ^ 2) +
              t * (f b + (M / 2) * b ^ 2) := hconvx
        _ = (s * f a + t * f b) +
            (M / 2) * (s * a ^ 2 + t * b ^ 2) := by ring
    have hquad : s * a ^ 2 + t * b ^ 2 =
        x ^ 2 + (x - a) * (b - x) := by
      dsimp [s, t]
      field_simp
      ring
    have hendpoint : s * f a + t * f b ≤ max (f a) (f b) := by
      have ha := mul_le_mul_of_nonneg_left (le_max_left (f a) (f b)) hs
      have hb := mul_le_mul_of_nonneg_left (le_max_right (f a) (f b)) ht
      calc
        s * f a + t * f b ≤ s * max (f a) (f b) +
            t * max (f a) (f b) := add_le_add ha hb
        _ = max (f a) (f b) := by rw [← add_mul, hst, one_mul]
    have hprod : (x - a) * (b - x) ≤ (b - a) ^ 2 / 4 := by
      nlinarith [sq_nonneg ((x - a) - (b - x))]
    have hcurv :
        (M / 2) * ((x - a) * (b - x)) ≤ M * (b - a) ^ 2 / 8 := by
      have h := mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ M / 2)
      nlinarith
    have hfx :
        f x ≤ (s * f a + t * f b) + (M / 2) * ((x - a) * (b - x)) := by
      nlinarith [hconvx', hquad]
    exact le_trans hfx (add_le_add hendpoint hcurv)

end PrimesRestrictedDigits
