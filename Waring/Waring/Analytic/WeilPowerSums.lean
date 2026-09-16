import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Tactic

/-!
# Formal power sums of the roots of a monic polynomial

This file defines the first five Newton power-sum expressions in the reversed
coefficients of a polynomial and proves that they are additive under products
of monic polynomials. This is the coefficient algebra used in the pure
additive Artin `L`-function construction from COCHRANE-PINNER2006, Section 2.
-/

namespace Waring.Analytic

open Polynomial
open scoped BigOperators

namespace Weil

variable {R : Type*} [CommRing R]

/-- The coefficient counted down from the leading term of a polynomial. -/
noncomputable def reverseCoeff (F : R[X]) (k : Nat) : R :=
  F.reverse.coeff k

/-- The formal `k`th root power sum for `1 <= k <= 5`, expressed through
Newton's identities in the reversed coefficients. It is zero outside that
range. -/
noncomputable def formalRootPowerSum (k : Nat) (F : R[X]) : R :=
  match k with
  | 1 => -reverseCoeff F 1
  | 2 => reverseCoeff F 1 ^ 2 - 2 * reverseCoeff F 2
  | 3 =>
      -reverseCoeff F 1 ^ 3 + 3 * reverseCoeff F 1 * reverseCoeff F 2 -
        3 * reverseCoeff F 3
  | 4 =>
      reverseCoeff F 1 ^ 4 - 4 * reverseCoeff F 1 ^ 2 * reverseCoeff F 2 +
        2 * reverseCoeff F 2 ^ 2 + 4 * reverseCoeff F 1 * reverseCoeff F 3 -
        4 * reverseCoeff F 4
  | 5 =>
      -reverseCoeff F 1 ^ 5 + 5 * reverseCoeff F 1 ^ 3 * reverseCoeff F 2 -
        5 * reverseCoeff F 1 * reverseCoeff F 2 ^ 2 -
        5 * reverseCoeff F 1 ^ 2 * reverseCoeff F 3 +
        5 * reverseCoeff F 2 * reverseCoeff F 3 +
        5 * reverseCoeff F 1 * reverseCoeff F 4 - 5 * reverseCoeff F 5
  | _ => 0

/-- The leading reversed coefficient of a monic polynomial is one. -/
@[simp]
theorem reverseCoeff_zero_of_monic {F : R[X]} (hF : F.Monic) :
    reverseCoeff F 0 = 1 := by
  simp [reverseCoeff, hF.leadingCoeff]

/-- Reversed coefficients of a product are given by the finite convolution sum. -/
theorem reverseCoeff_mul [IsDomain R] (F G : R[X]) (k : Nat) :
    reverseCoeff (F * G) k =
      ∑ i ∈ Finset.range (k + 1), reverseCoeff F i * reverseCoeff G (k - i) := by
  rw [reverseCoeff, Polynomial.reverse_mul_of_domain, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rfl

/-- The first five formal root power sums are additive when two monic
polynomials are multiplied. -/
theorem formalRootPowerSum_mul_of_monic [IsDomain R]
    {F G : R[X]} (hF : F.Monic)
    (hG : G.Monic) {k : Nat} (hkPos : 0 < k) (hk : k <= 5) :
    formalRootPowerSum k (F * G) =
      formalRootPowerSum k F + formalRootPowerSum k G := by
  interval_cases k <;>
    simp_all [formalRootPowerSum, reverseCoeff_mul,
      Finset.sum_range_succ, reverseCoeff_zero_of_monic hF,
      reverseCoeff_zero_of_monic hG] <;>
    ring

/-- Reversed coefficients of a monic polynomial commute with a ring map into
a nontrivial ring. -/
theorem reverseCoeff_map {S : Type*} [CommRing S] [Nontrivial S] (f : R →+* S)
    {F : R[X]} (hF : F.Monic) (k : Nat) :
    reverseCoeff (F.map f) k = f (reverseCoeff F k) := by
  simp [reverseCoeff, Polynomial.coeff_reverse, hF.natDegree_map f,
    Polynomial.coeff_map]

/-- The first five formal root power sums commute with a ring map on monic
polynomials. -/
theorem formalRootPowerSum_map {S : Type*} [CommRing S] [Nontrivial S]
    (f : R →+* S)
    {F : R[X]} (hF : F.Monic) {k : Nat} (hkPos : 0 < k) (hk : k ≤ 5) :
    formalRootPowerSum k (F.map f) = f (formalRootPowerSum k F) := by
  interval_cases k <;>
    simp_all [formalRootPowerSum, reverseCoeff_map f hF, map_ofNat]

/-- On a monic linear polynomial, the formal root power sum is the
corresponding power of its root. -/
theorem formalRootPowerSum_X_sub_C [IsDomain R] (a : R) {k : Nat}
    (hkPos : 0 < k) (hk : k <= 5) :
    formalRootPowerSum k (X - C a) = a ^ k := by
  have hDegree : (X - C a : R[X]).natDegree = 1 := natDegree_X_sub_C a
  have hOne : reverseCoeff (X - C a) 1 = -a := by
    simp [reverseCoeff, Polynomial.coeff_reverse, hDegree, Polynomial.revAt]
  have hTwo : reverseCoeff (X - C a) 2 = 0 := by
    simp [reverseCoeff, Polynomial.coeff_reverse, hDegree, Polynomial.revAt,
      Polynomial.coeff_X]
  have hThree : reverseCoeff (X - C a) 3 = 0 := by
    simp [reverseCoeff, Polynomial.coeff_reverse, hDegree, Polynomial.revAt,
      Polynomial.coeff_X]
  have hFour : reverseCoeff (X - C a) 4 = 0 := by
    simp [reverseCoeff, Polynomial.coeff_reverse, hDegree, Polynomial.revAt,
      Polynomial.coeff_X]
  have hFive : reverseCoeff (X - C a) 5 = 0 := by
    simp [reverseCoeff, Polynomial.coeff_reverse, hDegree, Polynomial.revAt,
      Polynomial.coeff_X]
  interval_cases k <;>
    simp_all [formalRootPowerSum] <;>
    ring

/-- The formal root power sums of the constant monic polynomial vanish. -/
theorem formalRootPowerSum_one [IsDomain R] {k : Nat} (hkPos : 0 < k)
    (hk : k <= 5) :
    formalRootPowerSum k (1 : R[X]) = 0 := by
  interval_cases k <;>
    simp_all [formalRootPowerSum, reverseCoeff, Polynomial.coeff_reverse,
      Polynomial.revAt, Polynomial.coeff_one]

/-- The formal power sum of a product of monic linear factors is the sum of
the corresponding powers, with multiplicity. -/
theorem formalRootPowerSum_multisetProd_X_sub_C [IsDomain R]
    (s : Multiset R) {k : Nat} (hkPos : 0 < k) (hk : k <= 5) :
    formalRootPowerSum k (s.map (fun a => X - C a)).prod =
      (s.map (fun a => a ^ k)).sum := by
  induction s using Multiset.induction_on with
  | empty =>
      simpa using formalRootPowerSum_one (R := R) hkPos hk
  | cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons,
        formalRootPowerSum_mul_of_monic (monic_X_sub_C a)
          (monic_multisetProd_X_sub_C s) hkPos hk,
        formalRootPowerSum_X_sub_C a hkPos hk, Multiset.map_cons,
        Multiset.sum_cons, ih]

/-- For a split monic polynomial, the formal root power sum is the sum of the
powers of its roots, counted with multiplicity. -/
theorem formalRootPowerSum_eq_sum_roots [IsDomain R]
    {F : R[X]} (hF : F.Monic) (hSplit : F.Splits) {k : Nat}
    (hkPos : 0 < k) (hk : k <= 5) :
    formalRootPowerSum k F = (F.roots.map (fun a => a ^ k)).sum := by
  have hFactor := hSplit.eq_prod_roots_of_monic hF
  calc
    formalRootPowerSum k F =
        formalRootPowerSum k (F.roots.map (fun a => X - C a)).prod :=
      congrArg (formalRootPowerSum k) hFactor
    _ = (F.roots.map (fun a => a ^ k)).sum :=
      formalRootPowerSum_multisetProd_X_sub_C F.roots hkPos hk

-- The domain hypothesis remains in the constant-polynomial base case to keep
-- its checked signature uniform with the multiplicative power-sum theorems.
attribute [nolint unusedArguments] formalRootPowerSum_one

end Weil

end Waring.Analytic
