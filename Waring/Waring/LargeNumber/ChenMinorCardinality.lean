import Waring.Analytic.ChenNineNumerics
import Waring.LargeNumber.ChenEleven

/-!
# Cardinality absorption in Chen's minor-arc estimate
-/

set_option autoImplicit false

namespace Waring.LargeNumber

/-- Lemma 11's family lower bound absorbs one Parseval cardinality into the
square of the cardinality, with Chen's convenient coefficient `80000`. -/
theorem chenElevenSums_card_le_scaled_square
    {N : Nat} (hN : 10 ^ 780 ≤ N) :
    ((chenElevenSums N).card : Real) ≤
      80000 *
        (mainScale N : Real) ^ (-(5 - 5 * scaleRatio ^ 11)) *
          ((chenElevenSums N).card : Real) ^ 2 := by
  let P : Real := mainScale N
  let E : Real := 5 - 5 * scaleRatio ^ 11
  let U : Real := (chenElevenSums N).card
  have hpNat : 0 < mainScale N := by
    have hp156 := ten_pow_oneFiftySix_le_mainScale hN
    exact lt_of_lt_of_le (by norm_num) hp156
  have hp : 0 < P := by
    dsimp [P]
    exact_mod_cast hpNat
  have hU :
      (17 / 10 : Real) / 2 ^ 17 * P ^ E ≤ U := by
    simpa [P, E, U] using (chen_lemma_eleven hN).2
  have hcoefficient :
      (10 : Real) * 2 ^ 17 / 17 ≤ 80000 :=
    Analytic.chenNine_endpoint_combinatorial_coefficient
  have hpowCancel : P ^ (-E) * P ^ E = 1 := by
    rw [← Real.rpow_add hp]
    simp
  have hcoefficientCancel :
      ((10 : Real) * 2 ^ 17 / 17) * ((17 / 10 : Real) / 2 ^ 17) = 1 := by
    norm_num
  have hone : 1 ≤ 80000 * P ^ (-E) * U := by
    calc
      (1 : Real) =
          (((10 : Real) * 2 ^ 17 / 17) * P ^ (-E)) *
            (((17 / 10 : Real) / 2 ^ 17) * P ^ E) := by
        symm
        calc
          (((10 : Real) * 2 ^ 17 / 17) * P ^ (-E)) *
              (((17 / 10 : Real) / 2 ^ 17) * P ^ E) =
              (((10 : Real) * 2 ^ 17 / 17) *
                ((17 / 10 : Real) / 2 ^ 17)) *
                  (P ^ (-E) * P ^ E) := by ring
          _ = 1 := by rw [hcoefficientCancel, hpowCancel]; ring
      _ ≤ (80000 * P ^ (-E)) * U := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right hcoefficient
            (Real.rpow_nonneg hp.le _)
        · exact hU
        · positivity
        · positivity
      _ = 80000 * P ^ (-E) * U := by ring
  calc
    U = 1 * U := by ring
    _ ≤ (80000 * P ^ (-E) * U) * U :=
      mul_le_mul_of_nonneg_right hone (by positivity)
    _ = 80000 * P ^ (-E) * U ^ 2 := by ring

end Waring.LargeNumber
