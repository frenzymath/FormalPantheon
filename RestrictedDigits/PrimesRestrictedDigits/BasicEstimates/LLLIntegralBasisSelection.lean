import PrimesRestrictedDigits.BasicEstimates.LLLIntegralBasis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

/-!
# Finite flag minimizers for fixed-rank LLL reduction

The second minimizer includes the size bound on its first projection
coefficient. Without that normalization, integral shears give infinitely many
lattice vectors with the same orthogonal remainder.
-/

noncomputable section

namespace PrimesRestrictedDigits

open InnerProductSpace

private abbrev E := EuclideanSpace Real (Fin 3)

/-- Choose a basis whose vector at `i` is globally shortest among all vectors
which occur at that position in an integral basis. -/
theorem exists_integralBasis_minimal_at {n : Nat}
    (Lambda : Submodule Int E) [DiscreteTopology Lambda]
    (b0 : Module.Basis (Fin n) Int Lambda) (i : Fin n) :
    ∃ b : Module.Basis (Fin n) Int Lambda,
      ∀ c : Module.Basis (Fin n) Int Lambda,
        ‖(b i : E)‖ <= ‖(c i : E)‖ := by
  let candidates : Set Lambda :=
    {x | ‖(x : E)‖ <= ‖(b0 i : E)‖ ∧
      ∃ b : Module.Basis (Fin n) Int Lambda, b i = x}
  have hfinite : candidates.Finite := by
    apply (finite_norm_le_of_discrete_intSubmodule Lambda
      ‖(b0 i : E)‖).subset
    intro x hx
    exact hx.1
  have hnonempty : candidates.Nonempty := ⟨b0 i, le_rfl, b0, rfl⟩
  obtain ⟨x, hx, hmin⟩ :=
    Set.exists_min_image candidates (fun x => ‖(x : E)‖) hfinite hnonempty
  obtain ⟨hxBound, b, hb⟩ := hx
  refine ⟨b, fun c => ?_⟩
  by_cases hc : ‖(c i : E)‖ <= ‖(b0 i : E)‖
  · simpa [hb] using hmin (c i) ⟨hc, c, rfl⟩
  · have hlt : ‖(b0 i : E)‖ < ‖(c i : E)‖ := lt_of_not_ge hc
    simpa [hb] using hxBound.trans hlt.le

/-- The coefficient of `y` along a nonzero first vector `x`. -/
def lllFirstCoefficient (x y : E) : Real :=
  inner Real x y / ‖x‖ ^ 2

/-- The remainder after removing the first-vector component. -/
def lllFirstRemainder (x y : E) : E :=
  y - lllFirstCoefficient x y • x

theorem lllFirstRemainder_add (x y : E) :
    lllFirstRemainder x y + lllFirstCoefficient x y • x = y := by
  simp [lllFirstRemainder]

theorem lllFirstCoefficient_sub_smul (x y : E) (hx : x ≠ 0) (r : Real) :
    lllFirstCoefficient x (y - r • x) =
      lllFirstCoefficient x y - r := by
  have hnorm : ‖x‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  simp only [lllFirstCoefficient, inner_sub_right, inner_smul_right,
    real_inner_self_eq_norm_sq]
  field_simp

theorem lllFirstRemainder_sub_smul (x y : E) (hx : x ≠ 0) (r : Real) :
    lllFirstRemainder x (y - r • x) = lllFirstRemainder x y := by
  rw [lllFirstRemainder, lllFirstCoefficient_sub_smul x y hx r]
  simp [lllFirstRemainder]
  module

theorem finite_lllSecondCandidates
    (Lambda : Submodule Int E) [DiscreteTopology Lambda]
    (x : Lambda) (B : Real) :
    Set.Finite {y : Lambda |
      ‖lllFirstRemainder (x : E) (y : E)‖ <= B ∧
      |lllFirstCoefficient (x : E) (y : E)| <= 1 / 2} := by
  apply (finite_norm_le_of_discrete_intSubmodule Lambda
    (B + (1 / 2 : Real) * ‖(x : E)‖)).subset
  intro y hy
  calc
    ‖(y : E)‖ =
        ‖lllFirstRemainder (x : E) (y : E) +
          lllFirstCoefficient (x : E) (y : E) • (x : E)‖ := by
      rw [lllFirstRemainder_add]
    _ <= ‖lllFirstRemainder (x : E) (y : E)‖ +
        ‖lllFirstCoefficient (x : E) (y : E) • (x : E)‖ :=
      norm_add_le _ _
    _ <= B + (1 / 2 : Real) * ‖(x : E)‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact add_le_add hy.1
        (mul_le_mul_of_nonneg_right hy.2 (norm_nonneg _))

/-- With the first vector fixed, choose a size-reduced second vector whose
first Gram--Schmidt remainder has minimum norm. -/
theorem exists_integralBasis_minimal_second_finThree
    (Lambda : Submodule Int E) [DiscreteTopology Lambda]
    (b0 : Module.Basis (Fin 3) Int Lambda)
    (hReduced :
      |lllFirstCoefficient (b0 0 : E) (b0 1 : E)| <= 1 / 2) :
    ∃ b : Module.Basis (Fin 3) Int Lambda,
      b 0 = b0 0 ∧
      |lllFirstCoefficient (b 0 : E) (b 1 : E)| <= 1 / 2 ∧
      ∀ c : Module.Basis (Fin 3) Int Lambda,
        c 0 = b0 0 ->
        |lllFirstCoefficient (c 0 : E) (c 1 : E)| <= 1 / 2 ->
        ‖lllFirstRemainder (b 0 : E) (b 1 : E)‖ <=
          ‖lllFirstRemainder (c 0 : E) (c 1 : E)‖ := by
  let B := ‖lllFirstRemainder (b0 0 : E) (b0 1 : E)‖
  let candidates : Set Lambda :=
    {y | ‖lllFirstRemainder (b0 0 : E) (y : E)‖ <= B ∧
      |lllFirstCoefficient (b0 0 : E) (y : E)| <= 1 / 2 ∧
      ∃ b : Module.Basis (Fin 3) Int Lambda,
        b 0 = b0 0 ∧ b 1 = y}
  have hfinite : candidates.Finite := by
    apply (finite_lllSecondCandidates Lambda (b0 0) B).subset
    intro y hy
    exact ⟨hy.1, hy.2.1⟩
  have hnonempty : candidates.Nonempty :=
    ⟨b0 1, le_rfl, hReduced, b0, rfl, rfl⟩
  obtain ⟨y, hy, hmin⟩ := Set.exists_min_image candidates
    (fun y => ‖lllFirstRemainder (b0 0 : E) (y : E)‖)
    hfinite hnonempty
  obtain ⟨hyBound, hyReduced, b, hb0, hb1⟩ := hy
  refine ⟨b, hb0, ?_, fun c hc0 hcReduced => ?_⟩
  · simpa [hb0, hb1] using hyReduced
  by_cases hcBound :
      ‖lllFirstRemainder (b0 0 : E) (c 1 : E)‖ <= B
  · have hc : c 1 ∈ candidates :=
      ⟨hcBound, by simpa [hc0] using hcReduced, c, hc0, rfl⟩
    simpa [hb0, hb1, hc0] using hmin (c 1) hc
  · have hlt : B < ‖lllFirstRemainder (b0 0 : E) (c 1 : E)‖ :=
      lt_of_not_ge hcBound
    simpa [hb0, hb1, hc0] using hyBound.trans hlt.le

end PrimesRestrictedDigits
