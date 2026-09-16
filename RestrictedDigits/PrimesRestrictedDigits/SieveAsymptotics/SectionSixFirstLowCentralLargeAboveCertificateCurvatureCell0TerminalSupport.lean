import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell0SignedCoeffSupport

/-!
# Static terminal support for the Cell0 signed certificate

This module names the four unsigned outer products in the cached signed row.
The terminal certificates replace each product by a static exact-rational row.
-/
open scoped BigOperators Polynomial

namespace PrimesRestrictedDigits

noncomputable section

namespace SectionSixFirstLowCentralLargeAboveCell0Certificate

def cell0CachedTerm1Row (k : Nat) : Polynomial Rat :=
  cell0OuterConv cell0PDeriv2Coeff cell0CachedQQRow k

def cell0CachedTerm2Row (k : Nat) : Polynomial Rat :=
  cell0OuterConv cell0CachedTwoPdQRow cell0QDerivCoeff k

def cell0CachedTerm3Row (k : Nat) : Polynomial Rat :=
  cell0OuterConv cell0TwoPCoeff cell0CachedQdQdRow k

def cell0CachedTerm4Row (k : Nat) : Polynomial Rat :=
  cell0OuterConv cell0CachedPQRow cell0QDeriv2Coeff k

theorem cell0CachedSignedOuterRow_staged (k : Nat) :
    cell0CachedSignedOuterRow k =
      -(cell0CachedTerm1Row k - cell0CachedTerm2Row k +
        cell0CachedTerm3Row k - cell0CachedTerm4Row k) := by
  rfl

theorem cell0PDeriv2Coeff_natDegree (i : Nat) :
    (cell0PDeriv2Coeff i).natDegree ≤ 3 := by
  rw [← cell0PFull_deriv2_coeff]
  exact (cell0InnerDegreeLe_derivative
    (cell0InnerDegreeLe_derivative cell0PFull_innerDegree)) i

theorem cell0QDeriv2Coeff_natDegree (i : Nat) :
    (cell0QDeriv2Coeff i).natDegree ≤ 4 := by
  rw [← cell0QFull_deriv2_coeff]
  exact (cell0InnerDegreeLe_derivative
    (cell0InnerDegreeLe_derivative cell0QFull_innerDegree)) i

theorem cell0CachedQQRow_natDegree (i : Nat) :
    (cell0CachedQQRow i).natDegree ≤ 8 := by
  rw [cell0CachedQQRow]
  split_ifs
  · exact cell0QQRow_natDegree i
  · simpa only [Polynomial.natDegree_zero] using (Nat.zero_le 8)

theorem cell0CachedTwoPdQRow_natDegree (i : Nat) :
    (cell0CachedTwoPdQRow i).natDegree ≤ 7 := by
  rw [cell0CachedTwoPdQRow]
  split_ifs
  · exact cell0TwoPdQRow_natDegree i
  · simpa only [Polynomial.natDegree_zero] using (Nat.zero_le 7)

theorem cell0CachedQdQdRow_natDegree (i : Nat) :
    (cell0CachedQdQdRow i).natDegree ≤ 8 := by
  rw [cell0CachedQdQdRow]
  split_ifs
  · exact cell0QdQdRow_natDegree i
  · simpa only [Polynomial.natDegree_zero] using (Nat.zero_le 8)

theorem cell0CachedPQRow_natDegree (i : Nat) :
    (cell0CachedPQRow i).natDegree ≤ 7 := by
  rw [cell0CachedPQRow]
  split_ifs
  · exact cell0PQRow_natDegree i
  · simpa only [Polynomial.natDegree_zero] using (Nat.zero_le 7)

theorem cell0CachedTerm1Row_natDegree (k : Nat) :
    (cell0CachedTerm1Row k).natDegree ≤ 11 := by
  simpa [cell0CachedTerm1Row] using cell0OuterConv_natDegree
    cell0PDeriv2Coeff cell0CachedQQRow 3 8
    cell0PDeriv2Coeff_natDegree cell0CachedQQRow_natDegree k

theorem cell0CachedTerm2Row_natDegree (k : Nat) :
    (cell0CachedTerm2Row k).natDegree ≤ 11 := by
  simpa [cell0CachedTerm2Row] using cell0OuterConv_natDegree
    cell0CachedTwoPdQRow cell0QDerivCoeff 7 4
    cell0CachedTwoPdQRow_natDegree cell0QDerivCoeff_natDegree k

theorem cell0CachedTerm3Row_natDegree (k : Nat) :
    (cell0CachedTerm3Row k).natDegree ≤ 11 := by
  simpa [cell0CachedTerm3Row] using cell0OuterConv_natDegree
    cell0TwoPCoeff cell0CachedQdQdRow 3 8
    cell0TwoPCoeff_natDegree cell0CachedQdQdRow_natDegree k

theorem cell0CachedTerm4Row_natDegree (k : Nat) :
    (cell0CachedTerm4Row k).natDegree ≤ 11 := by
  simpa [cell0CachedTerm4Row] using cell0OuterConv_natDegree
    cell0CachedPQRow cell0QDeriv2Coeff 7 4
    cell0CachedPQRow_natDegree cell0QDeriv2Coeff_natDegree k

end SectionSixFirstLowCentralLargeAboveCell0Certificate

end

end PrimesRestrictedDigits
