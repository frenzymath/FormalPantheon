import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell1SignedAssembly

/-! Scalar coefficient formulas for the cached Cell1 signed row. -/
open scoped BigOperators Polynomial

namespace PrimesRestrictedDigits

noncomputable section

namespace SectionSixFirstLowCentralLargeAboveCell1Certificate

@[simp] theorem cell1CachedQQRow_coeff_if (i l : Nat) :
    (cell1CachedQQRow i).coeff l =
      if i < 11 then (if l < 9 then cell1QQStageValue i l else 0) else 0 := by
  by_cases hi : i < 11 <;>
    simp [cell1CachedQQRow, cell1StageRow_coeff, cell1StageProductValue_zero, hi]

@[simp] theorem cell1CachedTwoPdQRow_coeff_if (i l : Nat) :
    (cell1CachedTwoPdQRow i).coeff l =
      if i < 9 then (if l < 9 then cell1TwoPdQStageValue i l else 0) else 0 := by
  by_cases hi : i < 9 <;>
    simp [cell1CachedTwoPdQRow, cell1StageRow_coeff, cell1StageProductValue_one, hi]

@[simp] theorem cell1CachedQdQdRow_coeff_if (i l : Nat) :
    (cell1CachedQdQdRow i).coeff l =
      if i < 9 then (if l < 9 then cell1QdQdStageValue i l else 0) else 0 := by
  by_cases hi : i < 9 <;>
    simp [cell1CachedQdQdRow, cell1StageRow_coeff, cell1StageProductValue_two, hi]

@[simp] theorem cell1CachedPQRow_coeff_if (i l : Nat) :
    (cell1CachedPQRow i).coeff l =
      if i < 10 then (if l < 9 then cell1PQStageValue i l else 0) else 0 := by
  by_cases hi : i < 10 <;>
    simp [cell1CachedPQRow, cell1StageRow_coeff, cell1StageProductValue_three, hi]

theorem cell1CachedSignedOuterRow_coeff (k l : Nat) :
    (cell1CachedSignedOuterRow k).coeff l =
      cell1ScalarConv (fun i j => (cell1PDeriv2Coeff i).coeff j)
          (fun i j => (cell1CachedQQRow i).coeff j) k l -
        cell1ScalarConv (fun i j => (cell1CachedTwoPdQRow i).coeff j)
          (fun i j => (cell1QDerivCoeff i).coeff j) k l +
        cell1ScalarConv (fun i j => (cell1TwoPCoeff i).coeff j)
          (fun i j => (cell1CachedQdQdRow i).coeff j) k l -
        cell1ScalarConv (fun i j => (cell1CachedPQRow i).coeff j)
          (fun i j => (cell1QDeriv2Coeff i).coeff j) k l := by
  simp only [cell1CachedSignedOuterRow, Polynomial.coeff_sub,
    Polynomial.coeff_add, cell1OuterConv_coeff]

theorem cell1X_mul_powerRow_coeff (k l : Nat) :
    (Polynomial.X * cell1PowerRow k).coeff l =
      if l = 0 then 0
      else if l - 1 < 11 then cell1PowerCoeff k (l - 1) else 0 := by
  cases l with
  | zero => simp
  | succ l =>
      rw [Polynomial.coeff_X_mul, cell1Power_row_coeff]
      simp

end SectionSixFirstLowCentralLargeAboveCell1Certificate

end

end PrimesRestrictedDigits
