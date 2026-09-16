import Mathlib.Tactic.IntervalCases
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell0SignedKernel
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell0StagePQCertificate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell0StageQQCertificate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell0StageQdQdCertificate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell0StageTwoPdQCertificate
/-!
# Cached signed-row assembly for Cell0

This module joins the four independently checked product stages without
replaying their coordinate arithmetic.  The outer negation is retained in the
definition, and the support lemmas isolate both outer and inner high tails.
-/
open scoped BigOperators Polynomial
namespace PrimesRestrictedDigits
noncomputable section
namespace SectionSixFirstLowCentralLargeAboveCell0Certificate

def cell0CachedQQRow (k : Nat) : Polynomial Rat :=
  if k < 17 then cell0QQRow k else 0

def cell0CachedTwoPdQRow (k : Nat) : Polynomial Rat :=
  if k < 15 then cell0TwoPdQRow k else 0

def cell0CachedQdQdRow (k : Nat) : Polynomial Rat :=
  if k < 15 then cell0QdQdRow k else 0

def cell0CachedPQRow (k : Nat) : Polynomial Rat :=
  if k < 16 then cell0PQRow k else 0

theorem cell0StageQQ_eq_cached (k : Nat) (hk : k < 22) :
    cell0StageProductRow 0 k = cell0CachedQQRow k := by
  interval_cases k <;> simp [cell0CachedQQRow]

theorem cell0StageTwoPdQ_eq_cached (k : Nat) (hk : k < 22) :
    cell0StageProductRow 1 k = cell0CachedTwoPdQRow k := by
  interval_cases k <;> simp [cell0CachedTwoPdQRow]

theorem cell0StageQdQd_eq_cached (k : Nat) (hk : k < 22) :
    cell0StageProductRow 2 k = cell0CachedQdQdRow k := by
  interval_cases k <;> simp [cell0CachedQdQdRow]

theorem cell0StagePQ_eq_cached (k : Nat) (hk : k < 22) :
    cell0StageProductRow 3 k = cell0CachedPQRow k := by
  interval_cases k <;> simp [cell0CachedPQRow]

theorem cell0OuterConv_congr_le
    {p p' q q' : Nat → Polynomial Rat} {k : Nat}
    (hp : ∀ i ≤ k, p i = p' i) (hq : ∀ i ≤ k, q i = q' i) :
    cell0OuterConv p q k = cell0OuterConv p' q' k := by
  rw [cell0OuterConv, cell0OuterConv]
  apply Finset.sum_congr rfl
  intro a ha
  have hs := Finset.mem_antidiagonal.mp ha
  have ha1 : a.1 ≤ k := by
    calc
      a.1 ≤ a.1 + a.2 := Nat.le_add_right _ _
      _ = k := hs
  have ha2 : a.2 ≤ k := by
    calc
      a.2 ≤ a.1 + a.2 := Nat.le_add_left _ _
      _ = k := hs
  rw [hp a.1 ha1, hq a.2 ha2]

def cell0CachedSignedOuterRow (k : Nat) : Polynomial Rat :=
  -(cell0OuterConv cell0PDeriv2Coeff cell0CachedQQRow k -
    cell0OuterConv cell0CachedTwoPdQRow cell0QDerivCoeff k +
    cell0OuterConv cell0TwoPCoeff cell0CachedQdQdRow k -
    cell0OuterConv cell0CachedPQRow cell0QDeriv2Coeff k)

theorem cell0SignedOuterRow_eq_cached (k : Nat) (hk : k < 22) :
    cell0SignedOuterRow k = cell0CachedSignedOuterRow k := by
  have h0 :
      cell0OuterConv cell0PDeriv2Coeff (cell0StageProductRow 0) k =
        cell0OuterConv cell0PDeriv2Coeff cell0CachedQQRow k := by
    apply cell0OuterConv_congr_le
    · intro i hi
      rfl
    · intro i hi
      exact cell0StageQQ_eq_cached i (lt_of_le_of_lt hi hk)
  have h1 :
      cell0OuterConv (cell0StageProductRow 1) cell0QDerivCoeff k =
        cell0OuterConv cell0CachedTwoPdQRow cell0QDerivCoeff k := by
    apply cell0OuterConv_congr_le
    · intro i hi
      exact cell0StageTwoPdQ_eq_cached i (lt_of_le_of_lt hi hk)
    · intro i hi
      rfl
  have h2 :
      cell0OuterConv cell0TwoPCoeff (cell0StageProductRow 2) k =
        cell0OuterConv cell0TwoPCoeff cell0CachedQdQdRow k := by
    apply cell0OuterConv_congr_le
    · intro i hi
      rfl
    · intro i hi
      exact cell0StageQdQd_eq_cached i (lt_of_le_of_lt hi hk)
  have h3 :
      cell0OuterConv (cell0StageProductRow 3) cell0QDeriv2Coeff k =
        cell0OuterConv cell0CachedPQRow cell0QDeriv2Coeff k := by
    apply cell0OuterConv_congr_le
    · intro i hi
      exact cell0StagePQ_eq_cached i (lt_of_le_of_lt hi hk)
    · intro i hi
      rfl
  unfold cell0SignedOuterRow cell0CachedSignedOuterRow
  rw [h0, h1, h2, h3]

theorem cell0SignedCurvature_coeff_cached (k : Nat) (hk : k < 22) :
    cell0SignedCurvature.coeff k = cell0CachedSignedOuterRow k := by
  rw [cell0SignedCurvature_coeff_formula, cell0SignedOuterRow_eq_cached k hk]

theorem cell0CachedSignedOuterRow_natDegree (k : Nat) (hk : k < 22) :
    (cell0CachedSignedOuterRow k).natDegree ≤ 11 := by
  rw [← cell0SignedCurvature_coeff_cached k hk]
  exact cell0SignedCurvature_innerDegree k

theorem cell0CachedSignedOuterRow_coeff_zero
    (k l : Nat) (hk : k < 22) (hl : 12 ≤ l) :
    (cell0CachedSignedOuterRow k).coeff l = 0 := by
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt
    ((cell0CachedSignedOuterRow_natDegree k hk).trans_lt (Nat.lt_of_succ_le hl))]

theorem cell0PowerRow_coeff_if (k l : Nat) :
    (cell0PowerRow k).coeff l = if l < 12 then cell0PowerCoeff k l else 0 := by
  simpa only [cell0PowerRow] using
    cell0FinitePolynomial_coeff 12 l (cell0PowerCoeff k)

theorem cell0PowerRow_natDegree (k : Nat) : (cell0PowerRow k).natDegree ≤ 11 := by
  rw [cell0PowerRow]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro l hl
  exact (Polynomial.natDegree_mul_le_of_le (m := 0) (n := l)
    (Polynomial.natDegree_C _).le (Polynomial.natDegree_X_pow_le l)).trans
    (by simpa using (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)))

theorem cell0SignedCurvature_coeff_zero (k : Nat) (hk : 22 ≤ k) :
    cell0SignedCurvature.coeff k = 0 := by
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt
    (cell0SignedCurvature_natDegree.trans_lt (Nat.lt_of_succ_le hk))]

end SectionSixFirstLowCentralLargeAboveCell0Certificate
end
end PrimesRestrictedDigits
