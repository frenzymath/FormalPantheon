import PrimesRestrictedDigits.BasicEstimates.LLLFixedRankBounds
import Mathlib.Tactic.Module

/-!
# Rank-two LLL coordinate control

This proves the rank-two weighted norm comparison.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

open InnerProductSpace

theorem sum_norm_smul_le_three_norm_sum_of_lllReduced
    (b : Fin 2 -> EuclideanSpace Real (Fin 3))
    (hb : IsLLLReduced b) (a : Fin 2 -> Real) :
    ∑ i, ‖a i • b i‖ <= 3 * ‖∑ i, a i • b i‖ := by
  let g0 := gramSchmidt Real b (0 : Fin 2)
  let g1 := gramSchmidt Real b (1 : Fin 2)
  let mu := lllCoefficient b (1 : Fin 2) (0 : Fin 2)
  let c0 := a 0 + a 1 * mu
  let x := ∑ i, a i • b i
  have hb0 : b 0 = g0 := by
    have : Finset.Iio (0 : Fin 2) = ∅ := by decide
    calc
      b 0 = g0 + ∑ j ∈ Finset.Iio (0 : Fin 2),
          lllCoefficient b 0 j • gramSchmidt Real b j := by
        simpa [g0] using eq_gramSchmidt_add_sum b (0 : Fin 2)
      _ = g0 := by simp [this]
  have hb1 : b 1 = g1 + mu • g0 := by
    have : Finset.Iio (1 : Fin 2) = {0} := by decide
    calc
      b 1 = g1 + ∑ j ∈ Finset.Iio (1 : Fin 2),
          lllCoefficient b 1 j • gramSchmidt Real b j := by
        simpa [g1] using eq_gramSchmidt_add_sum b (1 : Fin 2)
      _ = g1 + mu • g0 := by simp [g0, mu, this]
  have hg10 : inner Real g1 g0 = 0 := by
    exact gramSchmidt_orthogonal Real b (by norm_num : (1 : Fin 2) ≠ 0)
  have hg01 : inner Real g0 g1 = 0 := by
    rw [real_inner_comm]
    exact hg10
  have hmu : |mu| * ‖g0‖ <= (3 / 4 : Real) * ‖g1‖ := by
    simpa [g0, g1, mu] using
      hb.abs_coefficient_mul_norm_le (0 : Fin 2) (by norm_num)
  have hb1norm : ‖b 1‖ <= (5 / 4 : Real) * ‖g1‖ := by
    rw [hb1]
    exact norm_add_smul_le_five_div_four g0 g1 mu hg10 hmu
  have hx : x = c0 • g0 + a 1 • g1 := by
    simp only [x, Fin.sum_univ_two, hb0, hb1]
    dsimp [c0]
    module
  have hcomponents : inner Real (c0 • g0) (a 1 • g1) = 0 := by
    simp [inner_smul_left, inner_smul_right, hg01]
  have hc0 : ‖c0 • g0‖ <= ‖x‖ := by
    rw [hx]
    exact norm_left_le_norm_add_of_inner_eq_zero _ _ hcomponents
  have hc1 : ‖a 1 • g1‖ <= ‖x‖ := by
    rw [hx]
    exact norm_right_le_norm_add_of_inner_eq_zero _ _ hcomponents
  have hmuScaled :
      ‖(a 1 * mu) • g0‖ <= (3 / 4 : Real) * ‖a 1 • g1‖ := by
    have h := mul_le_mul_of_nonneg_left hmu (abs_nonneg (a 1))
    simpa [norm_smul, Real.norm_eq_abs, abs_mul, mul_assoc, mul_left_comm,
      mul_comm] using h
  have ha0 : ‖a 0 • b 0‖ <= (7 / 4 : Real) * ‖x‖ := by
    calc
      ‖a 0 • b 0‖ = ‖c0 • g0 - (a 1 * mu) • g0‖ := by
        congr 1
        rw [hb0]
        dsimp [c0]
        module
      _ <= ‖c0 • g0‖ + ‖(a 1 * mu) • g0‖ := norm_sub_le _ _
      _ <= ‖x‖ + (3 / 4 : Real) * ‖a 1 • g1‖ :=
        add_le_add hc0 hmuScaled
      _ <= (7 / 4 : Real) * ‖x‖ := by nlinarith
  have ha1 : ‖a 1 • b 1‖ <= (5 / 4 : Real) * ‖x‖ := by
    calc
      ‖a 1 • b 1‖ = |a 1| * ‖b 1‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ <= |a 1| * ((5 / 4 : Real) * ‖g1‖) :=
        mul_le_mul_of_nonneg_left hb1norm (abs_nonneg (a 1))
      _ = (5 / 4 : Real) * ‖a 1 • g1‖ := by
        rw [norm_smul, Real.norm_eq_abs]
        ring
      _ <= (5 / 4 : Real) * ‖x‖ :=
        mul_le_mul_of_nonneg_left hc1 (by norm_num)
  rw [Fin.sum_univ_two]
  nlinarith

end PrimesRestrictedDigits
