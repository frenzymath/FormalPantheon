import PrimesRestrictedDigits.BasicEstimates.LLLFixedRank
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Metric consequences of LLL reduction

These are the source-level adjacent Gram--Schmidt estimates used in the fixed-rank coordinate
proofs.
-/

namespace PrimesRestrictedDigits

open InnerProductSpace

private theorem norm_smul_sq (c : Real) {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace Real E] (x : E) :
    ‖c • x‖ ^ 2 = |c| ^ 2 * ‖x‖ ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs]
  ring

theorem IsLLLReduced.norm_sq_le_two_mul_next
    {n : Nat} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace Real E] {b : Fin n -> E}
    (hb : IsLLLReduced b) (i : Fin n) (hi : i.val + 1 < n) :
    ‖gramSchmidt Real b i‖ ^ 2 <=
      2 * ‖gramSchmidt Real b ⟨i.val + 1, hi⟩‖ ^ 2 := by
  let j : Fin n := ⟨i.val + 1, hi⟩
  let mu := lllCoefficient b j i
  let u := gramSchmidt Real b i
  let v := gramSchmidt Real b j
  have hij : i < j := by
    exact Fin.mk_lt_mk.mpr (Nat.lt_succ_self i.val)
  have hmu : |mu| <= (1 / 2 : Real) :=
    hb.coefficient_bound j i hij
  have hmuSq : |mu| ^ 2 <= (1 / 2 : Real) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg mu) (by norm_num)).2 hmu
  have hterm : ‖mu • u‖ ^ 2 <= (1 / 4 : Real) * ‖u‖ ^ 2 := by
    rw [norm_smul_sq]
    nlinarith [sq_nonneg ‖u‖]
  have huv : inner Real v u = 0 :=
    gramSchmidt_orthogonal Real b hij.ne'
  have huv' : inner Real v (mu • u) = 0 := by
    simp [inner_smul_right, huv]
  have hsum : ‖v + mu • u‖ ^ 2 = ‖v‖ ^ 2 + ‖mu • u‖ ^ 2 := by
    simpa [pow_two] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero v (mu • u) huv'
  have hlovasz : (3 / 4 : Real) * ‖u‖ ^ 2 <= ‖v + mu • u‖ ^ 2 := by
    simpa [j, mu, u, v] using hb.lovasz i hi
  nlinarith

theorem IsLLLReduced.abs_coefficient_mul_norm_le
    {n : Nat} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace Real E] {b : Fin n -> E}
    (hb : IsLLLReduced b) (i : Fin n) (hi : i.val + 1 < n) :
    |lllCoefficient b ⟨i.val + 1, hi⟩ i| *
        ‖gramSchmidt Real b i‖ <=
      (3 / 4 : Real) *
        ‖gramSchmidt Real b ⟨i.val + 1, hi⟩‖ := by
  let j : Fin n := ⟨i.val + 1, hi⟩
  let mu := lllCoefficient b j i
  let u := gramSchmidt Real b i
  let v := gramSchmidt Real b j
  have hij : i < j := by
    exact Fin.mk_lt_mk.mpr (Nat.lt_succ_self i.val)
  have hmu : |mu| <= (1 / 2 : Real) :=
    hb.coefficient_bound j i hij
  have hmuSq : |mu| ^ 2 <= (1 / 2 : Real) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg mu) (by norm_num)).2 hmu
  have huv := hb.norm_sq_le_two_mul_next i hi
  apply (sq_le_sq₀ (mul_nonneg (abs_nonneg mu) (norm_nonneg u))
    (mul_nonneg (by norm_num) (norm_nonneg v))).1
  calc
    (|mu| * ‖u‖) ^ 2 = |mu| ^ 2 * ‖u‖ ^ 2 := by ring
    _ <= (1 / 4 : Real) * ‖u‖ ^ 2 := by
      nlinarith [sq_nonneg ‖u‖]
    _ <= (1 / 4 : Real) * (2 * ‖v‖ ^ 2) := by
      exact mul_le_mul_of_nonneg_left huv (by norm_num)
    _ <= ((3 / 4 : Real) * ‖v‖) ^ 2 := by
      nlinarith [sq_nonneg ‖v‖]

theorem norm_add_smul_le_five_div_four
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    (u v : E) (mu : Real) (huv : inner Real v u = 0)
    (hmu : |mu| * ‖u‖ <= (3 / 4 : Real) * ‖v‖) :
    ‖v + mu • u‖ <= (5 / 4 : Real) * ‖v‖ := by
  have huv' : inner Real v (mu • u) = 0 := by
    simp [inner_smul_right, huv]
  have hsum : ‖v + mu • u‖ ^ 2 = ‖v‖ ^ 2 + ‖mu • u‖ ^ 2 := by
    simpa [pow_two] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero v (mu • u) huv'
  have hmuSq : ‖mu • u‖ ^ 2 <= ((3 / 4 : Real) * ‖v‖) ^ 2 := by
    rw [norm_smul_sq]
    simpa [mul_pow] using
      (sq_le_sq₀ (mul_nonneg (abs_nonneg mu) (norm_nonneg u))
        (mul_nonneg (by norm_num) (norm_nonneg v))).2 hmu
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) (norm_nonneg v))).1
  nlinarith [sq_nonneg ‖v‖]

theorem norm_left_le_norm_add_of_inner_eq_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    (u v : E) (huv : inner Real u v = 0) :
    ‖u‖ <= ‖u + v‖ := by
  have hsum : ‖u + v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
    simpa [pow_two] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero u v huv
  apply (sq_le_sq₀ (norm_nonneg u) (norm_nonneg (u + v))).1
  nlinarith [sq_nonneg ‖v‖]

theorem norm_right_le_norm_add_of_inner_eq_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    (u v : E) (huv : inner Real u v = 0) :
    ‖v‖ <= ‖u + v‖ := by
  rw [add_comm]
  exact norm_left_le_norm_add_of_inner_eq_zero v u
    (by simpa [real_inner_comm] using huv)

end PrimesRestrictedDigits
