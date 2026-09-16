import PrimesRestrictedDigits.BasicEstimates.LLLFixedRankBounds
import Mathlib.Tactic.Module

/-!
# Rank-three LLL coordinate control

This proves the rank-three weighted norm comparison.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

open InnerProductSpace

theorem sum_norm_smul_le_nine_norm_sum_of_lllReduced
    (b : Fin 3 -> EuclideanSpace Real (Fin 3))
    (hb : IsLLLReduced b) (a : Fin 3 -> Real) :
    ∑ i, ‖a i • b i‖ <= 9 * ‖∑ i, a i • b i‖ := by
  let g0 := gramSchmidt Real b (0 : Fin 3)
  let g1 := gramSchmidt Real b (1 : Fin 3)
  let g2 := gramSchmidt Real b (2 : Fin 3)
  let mu10 := lllCoefficient b (1 : Fin 3) (0 : Fin 3)
  let mu20 := lllCoefficient b (2 : Fin 3) (0 : Fin 3)
  let mu21 := lllCoefficient b (2 : Fin 3) (1 : Fin 3)
  let c0 := a 0 + a 1 * mu10 + a 2 * mu20
  let c1 := a 1 + a 2 * mu21
  let x := ∑ i, a i • b i
  have hb0 : b 0 = g0 := by
    have : Finset.Iio (0 : Fin 3) = ∅ := by decide
    calc
      b 0 = g0 + ∑ j ∈ Finset.Iio (0 : Fin 3),
          lllCoefficient b 0 j • gramSchmidt Real b j := by
        simpa [g0] using eq_gramSchmidt_add_sum b (0 : Fin 3)
      _ = g0 := by simp [this]
  have hb1 : b 1 = g1 + mu10 • g0 := by
    have : Finset.Iio (1 : Fin 3) = {0} := by decide
    calc
      b 1 = g1 + ∑ j ∈ Finset.Iio (1 : Fin 3),
          lllCoefficient b 1 j • gramSchmidt Real b j := by
        simpa [g1] using eq_gramSchmidt_add_sum b (1 : Fin 3)
      _ = g1 + mu10 • g0 := by simp [g0, mu10, this]
  have hb2 : b 2 = g2 + (mu20 • g0 + mu21 • g1) := by
    have : Finset.Iio (2 : Fin 3) = {0, 1} := by decide
    calc
      b 2 = g2 + ∑ j ∈ Finset.Iio (2 : Fin 3),
          lllCoefficient b 2 j • gramSchmidt Real b j := by
        simpa [g2] using eq_gramSchmidt_add_sum b (2 : Fin 3)
      _ = g2 + (mu20 • g0 + mu21 • g1) := by
        simp [g0, g1, mu20, mu21, this]
  have hg01 : inner Real g0 g1 = 0 := by
    exact gramSchmidt_orthogonal Real b (by norm_num : (0 : Fin 3) ≠ 1)
  have hg02 : inner Real g0 g2 = 0 := by
    exact gramSchmidt_orthogonal Real b (by decide : (0 : Fin 3) ≠ 2)
  have hg12 : inner Real g1 g2 = 0 := by
    exact gramSchmidt_orthogonal Real b (by decide : (1 : Fin 3) ≠ 2)
  have hg10 : inner Real g1 g0 = 0 := by
    simpa [real_inner_comm] using hg01
  have hmu10 : |mu10| * ‖g0‖ <= (3 / 4 : Real) * ‖g1‖ := by
    simpa [g0, g1, mu10] using
      hb.abs_coefficient_mul_norm_le (0 : Fin 3) (by norm_num)
  have hmu21 : |mu21| * ‖g1‖ <= (3 / 4 : Real) * ‖g2‖ := by
    simpa [g1, g2, mu21] using
      hb.abs_coefficient_mul_norm_le (1 : Fin 3) (by norm_num)
  have hg02norm : ‖g0‖ <= 2 * ‖g2‖ := by
    have h01 := hb.norm_sq_le_two_mul_next (0 : Fin 3) (by norm_num)
    have h12 := hb.norm_sq_le_two_mul_next (1 : Fin 3) (by norm_num)
    apply (sq_le_sq₀ (norm_nonneg g0)
      (mul_nonneg (by norm_num) (norm_nonneg g2))).1
    dsimp [g0, g1, g2] at h01 h12
    nlinarith [sq_nonneg ‖g1‖]
  have hmu20abs : |mu20| <= (1 / 2 : Real) := by
    simpa [mu20] using hb.coefficient_bound (2 : Fin 3) (0 : Fin 3) (by decide)
  have hmu20 : |mu20| * ‖g0‖ <= ‖g2‖ := by
    calc
      |mu20| * ‖g0‖ <= (1 / 2 : Real) * ‖g0‖ :=
        mul_le_mul_of_nonneg_right hmu20abs (norm_nonneg g0)
      _ <= (1 / 2 : Real) * (2 * ‖g2‖) :=
        mul_le_mul_of_nonneg_left hg02norm (by norm_num)
      _ = ‖g2‖ := by ring
  have hb1norm : ‖b 1‖ <= (5 / 4 : Real) * ‖g1‖ := by
    rw [hb1]
    exact norm_add_smul_le_five_div_four g0 g1 mu10 hg10 hmu10
  have hb2norm : ‖b 2‖ <= (11 / 4 : Real) * ‖g2‖ := by
    calc
      ‖b 2‖ = ‖g2 + (mu20 • g0 + mu21 • g1)‖ := by rw [hb2]
      _ <= ‖g2‖ + ‖mu20 • g0 + mu21 • g1‖ := norm_add_le _ _
      _ <= ‖g2‖ + (‖mu20 • g0‖ + ‖mu21 • g1‖) := by
        gcongr
        exact norm_add_le _ _
      _ = ‖g2‖ + |mu20| * ‖g0‖ + |mu21| * ‖g1‖ := by
        simp only [norm_smul, Real.norm_eq_abs]
        ring
      _ <= ‖g2‖ + ‖g2‖ + (3 / 4 : Real) * ‖g2‖ := by
        gcongr
      _ = (11 / 4 : Real) * ‖g2‖ := by ring
  have hx : x = (c0 • g0 + c1 • g1) + a 2 • g2 := by
    simp only [x, Fin.sum_univ_three, hb0, hb1, hb2]
    dsimp [c0, c1]
    module
  have hcomp01 : inner Real (c0 • g0) (c1 • g1) = 0 := by
    simp [inner_smul_left, inner_smul_right, hg01]
  have hcomp012 :
      inner Real (c0 • g0 + c1 • g1) (a 2 • g2) = 0 := by
    simp [inner_add_left, inner_smul_left, inner_smul_right, hg02, hg12]
  have hc01 : ‖c0 • g0 + c1 • g1‖ <= ‖x‖ := by
    rw [hx]
    exact norm_left_le_norm_add_of_inner_eq_zero _ _ hcomp012
  have hc2 : ‖a 2 • g2‖ <= ‖x‖ := by
    rw [hx]
    exact norm_right_le_norm_add_of_inner_eq_zero _ _ hcomp012
  have hc0 : ‖c0 • g0‖ <= ‖x‖ :=
    (norm_left_le_norm_add_of_inner_eq_zero _ _ hcomp01).trans hc01
  have hc1 : ‖c1 • g1‖ <= ‖x‖ :=
    (norm_right_le_norm_add_of_inner_eq_zero _ _ hcomp01).trans hc01
  have hmu10Scaled :
      ‖(a 1 * mu10) • g0‖ <= (3 / 4 : Real) * ‖a 1 • g1‖ := by
    have h := mul_le_mul_of_nonneg_left hmu10 (abs_nonneg (a 1))
    simpa [norm_smul, Real.norm_eq_abs, abs_mul, mul_assoc, mul_left_comm,
      mul_comm] using h
  have hmu21Scaled :
      ‖(a 2 * mu21) • g1‖ <= (3 / 4 : Real) * ‖a 2 • g2‖ := by
    have h := mul_le_mul_of_nonneg_left hmu21 (abs_nonneg (a 2))
    simpa [norm_smul, Real.norm_eq_abs, abs_mul, mul_assoc, mul_left_comm,
      mul_comm] using h
  have hmu20Scaled : ‖(a 2 * mu20) • g0‖ <= ‖a 2 • g2‖ := by
    have h := mul_le_mul_of_nonneg_left hmu20 (abs_nonneg (a 2))
    simpa [norm_smul, Real.norm_eq_abs, abs_mul, mul_assoc, mul_left_comm,
      mul_comm] using h
  have ha1g : ‖a 1 • g1‖ <= (7 / 4 : Real) * ‖x‖ := by
    calc
      ‖a 1 • g1‖ = ‖c1 • g1 - (a 2 * mu21) • g1‖ := by
        congr 1
        dsimp [c1]
        module
      _ <= ‖c1 • g1‖ + ‖(a 2 * mu21) • g1‖ := norm_sub_le _ _
      _ <= ‖x‖ + (3 / 4 : Real) * ‖a 2 • g2‖ :=
        add_le_add hc1 hmu21Scaled
      _ <= (7 / 4 : Real) * ‖x‖ := by nlinarith
  have ha0g : ‖a 0 • g0‖ <= (53 / 16 : Real) * ‖x‖ := by
    calc
      ‖a 0 • g0‖ =
          ‖(c0 • g0 - (a 1 * mu10) • g0) - (a 2 * mu20) • g0‖ := by
        congr 1
        dsimp [c0]
        module
      _ <= ‖c0 • g0 - (a 1 * mu10) • g0‖ +
          ‖(a 2 * mu20) • g0‖ := norm_sub_le _ _
      _ <= (‖c0 • g0‖ + ‖(a 1 * mu10) • g0‖) +
          ‖(a 2 * mu20) • g0‖ := by
        gcongr
        exact norm_sub_le _ _
      _ <= (‖x‖ + (3 / 4 : Real) * ‖a 1 • g1‖) + ‖a 2 • g2‖ := by
        gcongr
      _ <= (53 / 16 : Real) * ‖x‖ := by nlinarith
  have ha0 : ‖a 0 • b 0‖ <= (53 / 16 : Real) * ‖x‖ := by simpa [hb0] using ha0g
  have ha1 : ‖a 1 • b 1‖ <= (35 / 16 : Real) * ‖x‖ := by
    calc
      ‖a 1 • b 1‖ = |a 1| * ‖b 1‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ <= |a 1| * ((5 / 4 : Real) * ‖g1‖) :=
        mul_le_mul_of_nonneg_left hb1norm (abs_nonneg (a 1))
      _ = (5 / 4 : Real) * ‖a 1 • g1‖ := by
        rw [norm_smul, Real.norm_eq_abs]
        ring
      _ <= (5 / 4 : Real) * ((7 / 4 : Real) * ‖x‖) :=
        mul_le_mul_of_nonneg_left ha1g (by norm_num)
      _ = (35 / 16 : Real) * ‖x‖ := by ring
  have ha2 : ‖a 2 • b 2‖ <= (11 / 4 : Real) * ‖x‖ := by
    calc
      ‖a 2 • b 2‖ = |a 2| * ‖b 2‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ <= |a 2| * ((11 / 4 : Real) * ‖g2‖) :=
        mul_le_mul_of_nonneg_left hb2norm (abs_nonneg (a 2))
      _ = (11 / 4 : Real) * ‖a 2 • g2‖ := by
        rw [norm_smul, Real.norm_eq_abs]
        ring
      _ <= (11 / 4 : Real) * ‖x‖ :=
        mul_le_mul_of_nonneg_left hc2 (by norm_num)
  rw [Fin.sum_univ_three]
  change ‖a 0 • b 0‖ + ‖a 1 • b 1‖ + ‖a 2 • b 2‖ <= 9 * ‖x‖
  nlinarith [norm_nonneg x]

end PrimesRestrictedDigits
