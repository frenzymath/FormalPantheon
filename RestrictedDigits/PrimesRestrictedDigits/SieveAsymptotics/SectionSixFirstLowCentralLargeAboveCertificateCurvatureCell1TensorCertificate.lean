import PrimesRestrictedDigits.BasicEstimates.TensorBernsteinNonnegative
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateNodes
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell1Data
/-! Internal certificate shard for upper `I_4` cell 1. -/
open Set
open scoped BigOperators Polynomial
namespace PrimesRestrictedDigits
noncomputable section
open Polynomial (C X)
namespace SectionSixFirstLowCentralLargeAboveCell1Certificate
private theorem cell1_one_sub_pow_coeff {R : Type*} [CommRing R] (a b : Nat) : ((1 - X : Polynomial R) ^ a).coeff b = (-1 : R) ^ a * ((-1 : R) ^ (a - b) * (a.choose b : R)) := by
  have hsub : (1 - X : Polynomial R) = -(X + C (-1 : R)) := by simp [sub_eq_add_neg]
  have hnegpow : ((-1 : Polynomial R) ^ a) = C ((-1 : R) ^ a) := by rw [show (-1 : Polynomial R) = C (-1 : R) by simp, ← Polynomial.C_pow]
  have hneg : (-(X + C (-1 : R)) : Polynomial R) ^ a = C ((-1 : R) ^ a) * (X + C (-1 : R)) ^ a := by rw [neg_pow, hnegpow]
  rw [hsub, hneg, Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow]
private theorem cell1_bernstein_coeff_formula {R : Type*} [CommRing R] (n i k : Nat) : (bernsteinPolynomial R n i).coeff k = if i ≤ k then (n.choose i : R) * ((-1 : R) ^ (n - i) * ((-1 : R) ^ ((n - i) - (k - i)) * ((n - i).choose (k - i) : R))) else 0 := by
  rw [bernsteinPolynomial, ← Polynomial.C_eq_natCast, mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul', cell1_one_sub_pow_coeff]
  split_ifs <;> simp_all
private theorem cell1BernsteinPolynomial_natDegree_le (R : Type*) [CommRing R] {n i : Nat} (hi : i ≤ n) : (bernsteinPolynomial R n i).natDegree ≤ n := by
  rw [bernsteinPolynomial]
  have hc : ((Nat.choose n i : Polynomial R)).natDegree ≤ 0 := by simp
  have hx : (Polynomial.X ^ i : Polynomial R).natDegree ≤ i := Polynomial.natDegree_X_pow_le i
  have hs : (1 - Polynomial.X : Polynomial R).natDegree ≤ 1 := Polynomial.natDegree_sub_le_of_le (m := 1) (n := 1) (by simp) (Polynomial.natDegree_X_le (R := R))
  have h := Polynomial.natDegree_mul_le_of_le (Polynomial.natDegree_mul_le_of_le hc hx) (Polynomial.natDegree_pow_le_of_le (n - i) hs)
  simpa only [zero_add, mul_one, Nat.add_sub_of_le hi] using h
private theorem cell1_bernstein_outer_coeff (n i k : Nat) :
    (bernsteinPolynomial (Polynomial Rat) n i).coeff k =
      C ((bernsteinPolynomial Rat n i).coeff k) := by
  simpa only [Polynomial.coeff_map] using
    (congrArg (fun p : Polynomial (Polynomial Rat) => p.coeff k)
      (bernsteinPolynomial.map (C : Rat →+* Polynomial Rat) n i)).symm
private theorem cell1_tensor_coeff_formula
    (n m : Nat) (a : Nat → Nat → Rat) (k l : Nat) :
    ((tensorBernsteinPolynomial n m a).coeff k).coeff l =
      ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
        a i j * (bernsteinPolynomial Rat n i).coeff l *
          (bernsteinPolynomial Rat m j).coeff k := by
  rw [tensorBernsteinPolynomial]
  simp_rw [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    cell1_bernstein_outer_coeff, Polynomial.coeff_mul_C,
    Polynomial.coeff_C_mul]
local macro "cell1_tensor_coeff" : tactic => `(tactic| (rw [cell1Tensor, cell1_tensor_coeff_formula]; repeat rw [Finset.sum_range_succ]; simp_rw [cell1_bernstein_coeff_formula]; norm_num [Finset.sum_range_succ, Nat.choose, cell1BernsteinCoefficient, cell1BernsteinScale, cell1BernsteinNumerator, cell1PowerCoeff, cell1PowerScale, cell1PowerNumerator] <;> ring_nf))
local macro "cell1_tensor_row" n:ident k:num : command => `(
namespace $n
@[simp] private theorem c0 : (cell1Tensor.coeff $k).coeff 0 = cell1PowerCoeff $k 0 := by cell1_tensor_coeff
@[simp] private theorem c1 : (cell1Tensor.coeff $k).coeff 1 = cell1PowerCoeff $k 1 := by cell1_tensor_coeff
@[simp] private theorem c2 : (cell1Tensor.coeff $k).coeff 2 = cell1PowerCoeff $k 2 := by cell1_tensor_coeff
@[simp] private theorem c3 : (cell1Tensor.coeff $k).coeff 3 = cell1PowerCoeff $k 3 := by cell1_tensor_coeff
@[simp] private theorem c4 : (cell1Tensor.coeff $k).coeff 4 = cell1PowerCoeff $k 4 := by cell1_tensor_coeff
@[simp] private theorem c5 : (cell1Tensor.coeff $k).coeff 5 = cell1PowerCoeff $k 5 := by cell1_tensor_coeff
@[simp] private theorem c6 : (cell1Tensor.coeff $k).coeff 6 = cell1PowerCoeff $k 6 := by cell1_tensor_coeff
@[simp] private theorem c7 : (cell1Tensor.coeff $k).coeff 7 = cell1PowerCoeff $k 7 := by cell1_tensor_coeff
@[simp] private theorem c8 : (cell1Tensor.coeff $k).coeff 8 = cell1PowerCoeff $k 8 := by cell1_tensor_coeff
@[simp] private theorem c9 : (cell1Tensor.coeff $k).coeff 9 = cell1PowerCoeff $k 9 := by cell1_tensor_coeff
@[simp] private theorem c10 : (cell1Tensor.coeff $k).coeff 10 = cell1PowerCoeff $k 10 := by cell1_tensor_coeff
end $n)
cell1_tensor_row cell1Tensor_coeff_row_0 0 cell1_tensor_row cell1Tensor_coeff_row_1 1 cell1_tensor_row cell1Tensor_coeff_row_2 2 cell1_tensor_row cell1Tensor_coeff_row_3 3 cell1_tensor_row cell1Tensor_coeff_row_4 4 cell1_tensor_row cell1Tensor_coeff_row_5 5 cell1_tensor_row cell1Tensor_coeff_row_6 6 cell1_tensor_row cell1Tensor_coeff_row_7 7 cell1_tensor_row cell1Tensor_coeff_row_8 8 cell1_tensor_row cell1Tensor_coeff_row_9 9 cell1_tensor_row cell1Tensor_coeff_row_10 10 cell1_tensor_row cell1Tensor_coeff_row_11 11 cell1_tensor_row cell1Tensor_coeff_row_12 12
private theorem cell1Tensor_natDegree : cell1Tensor.natDegree ≤ 12 := by rw [cell1Tensor, tensorBernsteinPolynomial]; apply Polynomial.natDegree_sum_le_of_forall_le; intro i hi; apply Polynomial.natDegree_sum_le_of_forall_le; intro j hj; exact (Polynomial.natDegree_mul_le_of_le (m := 0) (n := 12) (Polynomial.natDegree_C _).le (cell1BernsteinPolynomial_natDegree_le (Polynomial Rat) (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))).trans (by simp)
theorem cell1Tensor_eq_power : cell1Tensor = cell1Power := by
  ext k l
  by_cases hk : k < 13
  · by_cases hl : l < 11
    · rw [cell1Power_outer_coeff k hk, cell1Power_row_coeff k l, if_pos hl]; interval_cases k <;> interval_cases l <;> simp
    · have hl' : 11 ≤ l := Nat.le_of_not_gt hl; have hp : (cell1Power.coeff k).coeff l = 0 := (by rw [cell1Power_outer_coeff k hk, cell1Power_row_coeff k l, if_neg hl]); have ht : (cell1Tensor.coeff k).coeff l = 0 := (by rw [cell1Tensor, cell1_tensor_coeff_formula]; apply Finset.sum_eq_zero; intro a ha; apply Finset.sum_eq_zero; intro b hb; rw [Polynomial.coeff_eq_zero_of_natDegree_lt ((cell1BernsteinPolynomial_natDegree_le Rat (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha))).trans_lt (Nat.lt_of_succ_le hl'))]; ring); rw [hp, ht]
  · have hk' : 13 ≤ k := Nat.le_of_not_gt hk; have hp : (cell1Power.coeff k).coeff l = 0 := (by rw [cell1Power, Polynomial.finsetSum_coeff]; simp_rw [Polynomial.coeff_C_mul_X_pow]; rw [Polynomial.finsetSum_coeff]; apply Finset.sum_eq_zero; intro i hi; have hi' : i < 13 := Finset.mem_range.mp hi; have hik : k ≠ i := Nat.ne_of_gt (lt_of_lt_of_le hi' hk'); simp [hik]); have ht : cell1Tensor.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (cell1Tensor_natDegree.trans_lt (Nat.lt_of_succ_le hk')); rw [hp, ht]; simp
end SectionSixFirstLowCentralLargeAboveCell1Certificate
end
end PrimesRestrictedDigits
