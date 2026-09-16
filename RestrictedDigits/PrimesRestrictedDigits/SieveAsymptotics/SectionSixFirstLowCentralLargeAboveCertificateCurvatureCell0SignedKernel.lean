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
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell0Data
/-!
# Shared signed-kernel infrastructure for Cell0

The signed replay is expressed as four cached outer products.  This module
contains no coordinate replay and deliberately does not unfold the tensor
certificate.  Later stage shards provide the finite coefficient tables.
-/
open Set
open scoped BigOperators Polynomial
namespace PrimesRestrictedDigits
noncomputable section
open Polynomial (C X)
namespace SectionSixFirstLowCentralLargeAboveCell0Certificate

def cell0OuterConst (a : Rat) (i : Nat) : Polynomial Rat :=
  if i = 0 then C a else 0

def cell0OuterConv (p q : Nat → Polynomial Rat) (k : Nat) : Polynomial Rat :=
  ∑ a ∈ Finset.antidiagonal k, p a.1 * q a.2

theorem cell0_coeff_mul_outer (p q : BivariateRat) (k : Nat) :
    (p * q).coeff k = cell0OuterConv (fun i => p.coeff i) (fun i => q.coeff i) k := by
  simp only [cell0OuterConv, Polynomial.coeff_mul]

def cell0PCoeff (i : Nat) : Polynomial Rat := if i < 8 then cell0PRow i else 0
def cell0QCoeff (i : Nat) : Polynomial Rat := if i < 9 then cell0QRow i else 0

theorem cell0PRow_coeff_if (i l : Nat) :
    (cell0PRow i).coeff l =
      if l < 4 then cell0PScale * (cell0PNumerator i l : Rat) else 0 := by
  simpa only [cell0PRow] using
    cell0FinitePolynomial_coeff 4 l
      (fun j => cell0PScale * (cell0PNumerator i j : Rat))

theorem cell0QRow_coeff_if (i l : Nat) :
    (cell0QRow i).coeff l =
      if l < 5 then cell0QScale * (cell0QNumerator i l : Rat) else 0 := by
  simpa only [cell0QRow] using
    cell0FinitePolynomial_coeff 5 l
      (fun j => cell0QScale * (cell0QNumerator i j : Rat))

theorem cell0PCoeff_coeff (i l : Nat) :
    (cell0PCoeff i).coeff l =
      if i < 8 then (if l < 4 then cell0PScale * (cell0PNumerator i l : Rat) else 0) else 0 := by
  by_cases hi : i < 8
  · simpa [cell0PCoeff, hi] using cell0PRow_coeff_if i l
  · simp [cell0PCoeff, hi]

theorem cell0QCoeff_coeff (i l : Nat) :
    (cell0QCoeff i).coeff l =
      if i < 9 then (if l < 5 then cell0QScale * (cell0QNumerator i l : Rat) else 0) else 0 := by
  by_cases hi : i < 9
  · simpa [cell0QCoeff, hi] using cell0QRow_coeff_if i l
  · simp [cell0QCoeff, hi]

theorem cell0PFull_coeff_eq_PCoeff (i : Nat) :
    cell0PFull.coeff i = cell0PCoeff i := by
  simpa only [cell0PCoeff] using cell0PFull_coeff i

theorem cell0QFull_coeff_eq_QCoeff (i : Nat) :
    cell0QFull.coeff i = cell0QCoeff i := by
  simpa only [cell0QCoeff] using cell0QFull_coeff i

theorem cell0OuterConst_coeff (a : Rat) (i l : Nat) :
    (cell0OuterConst a i).coeff l = if i = 0 then (if l = 0 then a else 0) else 0 := by
  by_cases hi : i = 0 <;> by_cases hl : l = 0 <;>
    simp [cell0OuterConst, Polynomial.coeff_C, hi, hl]

def cell0ScalarConv (p q : Nat → Nat → Rat) (k l : Nat) : Rat :=
  ∑ a ∈ Finset.antidiagonal k, ∑ b ∈ Finset.antidiagonal l,
    p a.1 b.1 * q a.2 b.2

theorem cell0OuterConv_coeff (p q : Nat → Polynomial Rat) (k l : Nat) :
    (cell0OuterConv p q k).coeff l =
      cell0ScalarConv (fun i j => (p i).coeff j) (fun i j => (q i).coeff j) k l := by
  rw [cell0OuterConv, cell0ScalarConv, Polynomial.finsetSum_coeff]
  simp_rw [Polynomial.coeff_mul]

def cell0PDerivCoeff (i : Nat) : Polynomial Rat := cell0PCoeff (i + 1) * (i + 1)
def cell0QDerivCoeff (i : Nat) : Polynomial Rat := cell0QCoeff (i + 1) * (i + 1)
def cell0PDeriv2Coeff (i : Nat) : Polynomial Rat := cell0PDerivCoeff (i + 1) * (i + 1)
def cell0QDeriv2Coeff (i : Nat) : Polynomial Rat := cell0QDerivCoeff (i + 1) * (i + 1)

theorem cell0Constant_outer_coeff (a : Rat) (i : Nat) :
    (cell0Constant a).coeff i = cell0OuterConst a i := by
  by_cases hi : i = 0 <;> simp [cell0Constant, cell0OuterConst, hi,
    Polynomial.coeff_C_of_ne_zero]

theorem cell0PFull_deriv_coeff (i : Nat) :
    cell0PFull.derivative.coeff i = cell0PDerivCoeff i := by
  simp [Polynomial.coeff_derivative, cell0PDerivCoeff,
    cell0PFull_coeff_eq_PCoeff]

theorem cell0QFull_deriv_coeff (i : Nat) :
    cell0QFull.derivative.coeff i = cell0QDerivCoeff i := by
  simp [Polynomial.coeff_derivative, cell0QDerivCoeff,
    cell0QFull_coeff_eq_QCoeff]

theorem cell0PFull_deriv2_coeff (i : Nat) :
    cell0PFull.derivative.derivative.coeff i = cell0PDeriv2Coeff i := by
  simp only [Polynomial.coeff_derivative, cell0PDeriv2Coeff, cell0PDerivCoeff,
    cell0PFull_coeff_eq_PCoeff]

theorem cell0QFull_deriv2_coeff (i : Nat) :
    cell0QFull.derivative.derivative.coeff i = cell0QDeriv2Coeff i := by
  simp only [Polynomial.coeff_derivative, cell0QDeriv2Coeff, cell0QDerivCoeff,
    cell0QFull_coeff_eq_QCoeff]

-- The derivative products are stored with a natural cast in the polynomial
-- factor.  Normalize the successor cast before exposing that factor as `C`.
theorem cell0_natSucc_rat (i : Nat) :
    (i : Rat) + 1 = ((i + 1 : Nat) : Rat) := by
  simp only [Nat.cast_add, Nat.cast_one]

theorem cell0_natSucc_poly (i : Nat) :
    (i : Polynomial Rat) + 1 = ((i + 1 : Nat) : Polynomial Rat) := by
  simp only [Nat.cast_add, Nat.cast_one]

theorem cell0PDerivCoeff_coeff (i l : Nat) :
    (cell0PDerivCoeff i).coeff l = (cell0PCoeff (i + 1)).coeff l * (i + 1 : Rat) := by
  rw [cell0PDerivCoeff, cell0_natSucc_poly, cell0_natSucc_rat,
    ← Polynomial.C_eq_natCast, Polynomial.coeff_mul_C]

theorem cell0QDerivCoeff_coeff (i l : Nat) :
    (cell0QDerivCoeff i).coeff l = (cell0QCoeff (i + 1)).coeff l * (i + 1 : Rat) := by
  rw [cell0QDerivCoeff, cell0_natSucc_poly, cell0_natSucc_rat,
    ← Polynomial.C_eq_natCast, Polynomial.coeff_mul_C]

theorem cell0PDeriv2Coeff_coeff (i l : Nat) :
    (cell0PDeriv2Coeff i).coeff l =
      (cell0PDerivCoeff (i + 1)).coeff l * (i + 1 : Rat) := by
  rw [cell0PDeriv2Coeff, cell0_natSucc_poly, cell0_natSucc_rat,
    ← Polynomial.C_eq_natCast, Polynomial.coeff_mul_C]

theorem cell0QDeriv2Coeff_coeff (i l : Nat) :
    (cell0QDeriv2Coeff i).coeff l =
      (cell0QDerivCoeff (i + 1)).coeff l * (i + 1 : Rat) := by
  rw [cell0QDeriv2Coeff, cell0_natSucc_poly, cell0_natSucc_rat,
    ← Polynomial.C_eq_natCast, Polynomial.coeff_mul_C]

def cell0TwoPdCoeff (i : Nat) : Polynomial Rat := C 2 * cell0PDerivCoeff i
def cell0TwoPCoeff (i : Nat) : Polynomial Rat := C 2 * cell0PCoeff i

theorem cell0TwoPdCoeff_coeff (i l : Nat) :
    (cell0TwoPdCoeff i).coeff l = 2 * (cell0PDerivCoeff i).coeff l := by
  simp [cell0TwoPdCoeff, Polynomial.coeff_C_mul]

theorem cell0TwoPCoeff_coeff (i l : Nat) :
    (cell0TwoPCoeff i).coeff l = 2 * (cell0PCoeff i).coeff l := by
  simp [cell0TwoPCoeff, Polynomial.coeff_C_mul]

def cell0SignedOuterRaw (k : Nat) : Polynomial Rat :=
  cell0OuterConv cell0PDeriv2Coeff (fun j => cell0OuterConv cell0QCoeff cell0QCoeff j) k -
    cell0OuterConv (fun j => cell0OuterConv (fun h =>
      cell0OuterConv (cell0OuterConst 2) cell0PDerivCoeff h) cell0QCoeff j)
      cell0QDerivCoeff k +
    cell0OuterConv (fun j => cell0OuterConv (cell0OuterConst 2) cell0PCoeff j)
      (fun j => cell0OuterConv cell0QDerivCoeff cell0QDerivCoeff j) k -
    cell0OuterConv (fun j => cell0OuterConv cell0PCoeff cell0QCoeff j)
      cell0QDeriv2Coeff k

theorem cell0SignedCurvature_coeff_raw (k : Nat) :
    cell0SignedCurvature.coeff k = -cell0SignedOuterRaw k := by
  rw [cell0SignedCurvature, cell0RationalPolynomials_eq_full, cell0Constant,
    Polynomial.coeff_C_mul]
  simp only [cell0SignedOuterRaw, Polynomial.coeff_sub, Polynomial.coeff_add,
    cell0_coeff_mul_outer, pow_two, cell0PFull_coeff_eq_PCoeff,
    cell0QFull_coeff_eq_QCoeff,
    cell0PFull_deriv_coeff, cell0QFull_deriv_coeff,
    cell0PFull_deriv2_coeff, cell0QFull_deriv2_coeff,
    cell0Constant_outer_coeff, Polynomial.C_neg, Polynomial.C_1,
    neg_mul, one_mul]

theorem cell0TwoPd_outer_eq (i : Nat) :
    cell0OuterConv (cell0OuterConst 2) cell0PDerivCoeff i = cell0TwoPdCoeff i := by
  have h := cell0_coeff_mul_outer (cell0Constant 2) cell0PFull.derivative i
  simp_rw [cell0Constant_outer_coeff, cell0PFull_deriv_coeff] at h
  rw [cell0Constant, Polynomial.coeff_C_mul, cell0PFull_deriv_coeff] at h
  simpa only [cell0TwoPdCoeff] using h.symm

theorem cell0TwoP_outer_eq (i : Nat) :
    cell0OuterConv (cell0OuterConst 2) cell0PCoeff i = cell0TwoPCoeff i := by
  have h := cell0_coeff_mul_outer (cell0Constant 2) cell0PFull i
  simp_rw [cell0Constant_outer_coeff, cell0PFull_coeff_eq_PCoeff] at h
  rw [cell0Constant, Polynomial.coeff_C_mul, cell0PFull_coeff_eq_PCoeff] at h
  simpa only [cell0TwoPCoeff] using h.symm

def cell0StageProductRow (s k : Nat) : Polynomial Rat :=
  match s with
  | 0 => cell0OuterConv cell0QCoeff cell0QCoeff k
  | 1 => cell0OuterConv cell0TwoPdCoeff cell0QCoeff k
  | 2 => cell0OuterConv cell0QDerivCoeff cell0QDerivCoeff k
  | 3 => cell0OuterConv cell0PCoeff cell0QCoeff k
  | _ => 0

def cell0SignedOuterRow (k : Nat) : Polynomial Rat :=
  -(cell0OuterConv cell0PDeriv2Coeff (cell0StageProductRow 0) k -
    cell0OuterConv (cell0StageProductRow 1) cell0QDerivCoeff k +
    cell0OuterConv cell0TwoPCoeff (cell0StageProductRow 2) k -
    cell0OuterConv (cell0StageProductRow 3) cell0QDeriv2Coeff k)

theorem cell0SignedOuterRaw_eq (k : Nat) :
    cell0SignedOuterRaw k =
      cell0OuterConv cell0PDeriv2Coeff (cell0StageProductRow 0) k -
        cell0OuterConv (cell0StageProductRow 1) cell0QDerivCoeff k +
        cell0OuterConv cell0TwoPCoeff (cell0StageProductRow 2) k -
        cell0OuterConv (cell0StageProductRow 3) cell0QDeriv2Coeff k := by
  have hpd : (fun i : Nat =>
      cell0OuterConv (cell0OuterConst 2) cell0PDerivCoeff i) = cell0TwoPdCoeff :=
    funext cell0TwoPd_outer_eq
  have hp : (fun i : Nat =>
      cell0OuterConv (cell0OuterConst 2) cell0PCoeff i) = cell0TwoPCoeff :=
    funext cell0TwoP_outer_eq
  have h0 : cell0StageProductRow 0 =
      (fun j : Nat => cell0OuterConv cell0QCoeff cell0QCoeff j) := by
    funext j
    rfl
  have h1 : cell0StageProductRow 1 =
      (fun j : Nat => cell0OuterConv cell0TwoPdCoeff cell0QCoeff j) := by
    funext j
    rfl
  have h2 : cell0StageProductRow 2 =
      (fun j : Nat => cell0OuterConv cell0QDerivCoeff cell0QDerivCoeff j) := by
    funext j
    rfl
  have h3 : cell0StageProductRow 3 =
      (fun j : Nat => cell0OuterConv cell0PCoeff cell0QCoeff j) := by
    funext j
    rfl
  unfold cell0SignedOuterRaw
  rw [hpd, hp, h0, h1, h2, h3]

theorem cell0SignedCurvature_coeff_formula (k : Nat) :
    cell0SignedCurvature.coeff k = cell0SignedOuterRow k := by
  rw [cell0SignedCurvature_coeff_raw, cell0SignedOuterRaw_eq]
  rfl

theorem cell0InnerDegreeLe_derivative {n : Nat} {p : BivariateRat}
    (hp : cell0InnerDegreeLe n p) : cell0InnerDegreeLe n p.derivative := by
  intro i
  rw [Polynomial.coeff_derivative]
  have hs : (C ((i + 1 : Nat) : Rat)).natDegree ≤ 0 :=
    (Polynomial.natDegree_C _).le
  simpa using Polynomial.natDegree_mul_le_of_le (hp (i + 1)) hs

theorem cell0PFull_innerDegree : cell0InnerDegreeLe 3 cell0PFull := by
  intro i
  rw [cell0PFull_coeff_eq_PCoeff, cell0PCoeff]
  split_ifs
  · exact cell0PRow_natDegree i
  · simp

theorem cell0QFull_innerDegree : cell0InnerDegreeLe 4 cell0QFull := by
  intro i
  rw [cell0QFull_coeff_eq_QCoeff, cell0QCoeff]
  split_ifs
  · exact cell0QRow_natDegree i
  · simp

theorem cell0SignedCurvature_innerDegree :
    cell0InnerDegreeLe 11 cell0SignedCurvature := by
  have hp1 : cell0InnerDegreeLe 3 cell0PFull.derivative :=
    cell0InnerDegreeLe_derivative cell0PFull_innerDegree
  have hp2 : cell0InnerDegreeLe 3 cell0PFull.derivative.derivative :=
    cell0InnerDegreeLe_derivative hp1
  have hq1 : cell0InnerDegreeLe 4 cell0QFull.derivative :=
    cell0InnerDegreeLe_derivative cell0QFull_innerDegree
  have hq2 : cell0InnerDegreeLe 4 cell0QFull.derivative.derivative :=
    cell0InnerDegreeLe_derivative hq1
  have hc (a : Rat) : cell0InnerDegreeLe 0 (cell0Constant a) := by
    intro i
    rw [cell0Constant_outer_coeff]
    by_cases hi : i = 0 <;> simp [cell0OuterConst, hi]
  have hneg : cell0InnerDegreeLe 0 (cell0Constant (-1)) := hc (-1 : Rat)
  have h1 : cell0InnerDegreeLe 11
      (cell0PFull.derivative.derivative * cell0QFull ^ 2) := by
    simpa [pow_two] using cell0InnerDegreeLe_mul hp2
      (cell0InnerDegreeLe_mul cell0QFull_innerDegree cell0QFull_innerDegree)
  have h2 : cell0InnerDegreeLe 11
      (cell0Constant 2 * cell0PFull.derivative * cell0QFull * cell0QFull.derivative) := by
    simpa using cell0InnerDegreeLe_mul
      (cell0InnerDegreeLe_mul (cell0InnerDegreeLe_mul (hc 2) hp1) cell0QFull_innerDegree) hq1
  have h3 : cell0InnerDegreeLe 11
      (cell0Constant 2 * cell0PFull * cell0QFull.derivative ^ 2) := by
    simpa [pow_two] using cell0InnerDegreeLe_mul
      (cell0InnerDegreeLe_mul (hc 2) cell0PFull_innerDegree)
      (cell0InnerDegreeLe_mul hq1 hq1)
  have h4 : cell0InnerDegreeLe 11
      (cell0PFull * cell0QFull * cell0QFull.derivative.derivative) := by
    simpa using cell0InnerDegreeLe_mul
      (cell0InnerDegreeLe_mul cell0PFull_innerDegree cell0QFull_innerDegree) hq2
  have hraw : cell0InnerDegreeLe 11
      (cell0PFull.derivative.derivative * cell0QFull ^ 2 -
        cell0Constant 2 * cell0PFull.derivative * cell0QFull * cell0QFull.derivative +
        cell0Constant 2 * cell0PFull * cell0QFull.derivative ^ 2 -
        cell0PFull * cell0QFull * cell0QFull.derivative.derivative) :=
    cell0InnerDegreeLe_sub
      (cell0InnerDegreeLe_add (cell0InnerDegreeLe_sub h1 h2) h3) h4
  have hprod : cell0InnerDegreeLe 11
      (cell0Constant (-1) *
        (cell0PFull.derivative.derivative * cell0QFull ^ 2 -
          cell0Constant 2 * cell0PFull.derivative * cell0QFull * cell0QFull.derivative +
          cell0Constant 2 * cell0PFull * cell0QFull.derivative ^ 2 -
          cell0PFull * cell0QFull * cell0QFull.derivative.derivative)) :=
    cell0InnerDegreeLe_mul hneg hraw
  simpa only [cell0SignedCurvature, cell0RationalPolynomials_eq_full] using hprod

theorem cell0PCoeff_natDegree (i : Nat) : (cell0PCoeff i).natDegree ≤ 3 := by
  rw [← cell0PFull_coeff_eq_PCoeff]
  exact cell0PFull_innerDegree i

theorem cell0QCoeff_natDegree (i : Nat) : (cell0QCoeff i).natDegree ≤ 4 := by
  rw [← cell0QFull_coeff_eq_QCoeff]
  exact cell0QFull_innerDegree i

theorem cell0PDerivCoeff_natDegree (i : Nat) :
    (cell0PDerivCoeff i).natDegree ≤ 3 := by
  rw [← cell0PFull_deriv_coeff]
  exact (cell0InnerDegreeLe_derivative cell0PFull_innerDegree) i

theorem cell0QDerivCoeff_natDegree (i : Nat) :
    (cell0QDerivCoeff i).natDegree ≤ 4 := by
  rw [← cell0QFull_deriv_coeff]
  exact (cell0InnerDegreeLe_derivative cell0QFull_innerDegree) i

theorem cell0TwoPdCoeff_natDegree (i : Nat) :
    (cell0TwoPdCoeff i).natDegree ≤ 3 := by
  rw [cell0TwoPdCoeff]
  simpa using Polynomial.natDegree_mul_le_of_le (m := 0) (n := 3)
    (Polynomial.natDegree_C _).le (cell0PDerivCoeff_natDegree i)

theorem cell0TwoPCoeff_natDegree (i : Nat) :
    (cell0TwoPCoeff i).natDegree ≤ 3 := by
  rw [cell0TwoPCoeff]
  simpa using Polynomial.natDegree_mul_le_of_le (m := 0) (n := 3)
    (Polynomial.natDegree_C _).le (cell0PCoeff_natDegree i)

theorem cell0OuterConv_natDegree
    (p q : Nat → Polynomial Rat) (m n : Nat)
    (hp : ∀ i, (p i).natDegree ≤ m) (hq : ∀ i, (q i).natDegree ≤ n)
    (k : Nat) : (cell0OuterConv p q k).natDegree ≤ m + n := by
  rw [cell0OuterConv]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro a ha
  exact Polynomial.natDegree_mul_le_of_le (hp a.1) (hq a.2)

theorem cell0StageProductRow_natDegree (s k : Nat) :
    (cell0StageProductRow s k).natDegree ≤ 8 := by
  rcases s with (_ | _ | _ | _ | s)
  · simpa [cell0StageProductRow] using cell0OuterConv_natDegree
      cell0QCoeff cell0QCoeff 4 4 cell0QCoeff_natDegree cell0QCoeff_natDegree k
  · simpa [cell0StageProductRow] using
      ((cell0OuterConv_natDegree cell0TwoPdCoeff cell0QCoeff 3 4
        cell0TwoPdCoeff_natDegree cell0QCoeff_natDegree k).trans (by norm_num))
  · simpa [cell0StageProductRow] using cell0OuterConv_natDegree
      cell0QDerivCoeff cell0QDerivCoeff 4 4 cell0QDerivCoeff_natDegree
      cell0QDerivCoeff_natDegree k
  · simpa [cell0StageProductRow] using
      ((cell0OuterConv_natDegree cell0PCoeff cell0QCoeff 3 4
        cell0PCoeff_natDegree cell0QCoeff_natDegree k).trans (by norm_num))
  · simp [cell0StageProductRow]

end SectionSixFirstLowCentralLargeAboveCell0Certificate
end
end PrimesRestrictedDigits
