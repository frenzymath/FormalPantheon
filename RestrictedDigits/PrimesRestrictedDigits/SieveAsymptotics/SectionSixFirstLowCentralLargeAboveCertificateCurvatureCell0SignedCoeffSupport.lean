import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell0SignedAssembly
/-!
# Coefficient support for the cached Cell0 signed replay

The four stage rows are already checked in their own modules.  This file only
exposes their cached coefficient formulas and the outer signed contraction;
coordinate leaves can therefore replay a small rational expression without
unfolding the original tensor definitions.
-/
open scoped BigOperators Polynomial
namespace PrimesRestrictedDigits
noncomputable section
namespace SectionSixFirstLowCentralLargeAboveCell0Certificate

@[simp] theorem cell0CachedQQRow_coeff_if (i l : Nat) :
    (cell0CachedQQRow i).coeff l =
      if i < 17 then (if l < 9 then cell0QQValue i l else 0) else 0 := by
  by_cases hi : i < 17 <;> simp [cell0CachedQQRow, cell0QQRow_coeff, hi]

@[simp] theorem cell0CachedTwoPdQRow_coeff_if (i l : Nat) :
    (cell0CachedTwoPdQRow i).coeff l =
      if i < 15 then (if l < 8 then cell0TwoPdQValue i l else 0) else 0 := by
  by_cases hi : i < 15 <;> simp [cell0CachedTwoPdQRow, cell0TwoPdQRow_coeff, hi]

@[simp] theorem cell0CachedQdQdRow_coeff_if (i l : Nat) :
    (cell0CachedQdQdRow i).coeff l =
      if i < 15 then (if l < 9 then cell0QdQdValue i l else 0) else 0 := by
  by_cases hi : i < 15 <;> simp [cell0CachedQdQdRow, cell0QdQdRow_coeff, hi]

@[simp] theorem cell0CachedPQRow_coeff_if (i l : Nat) :
    (cell0CachedPQRow i).coeff l =
      if i < 16 then (if l < 8 then cell0PQValue i l else 0) else 0 := by
  by_cases hi : i < 16 <;> simp [cell0CachedPQRow, cell0PQRow_coeff, hi]

theorem cell0CachedSignedOuterRow_coeff (k l : Nat) :
    (cell0CachedSignedOuterRow k).coeff l =
      -(cell0ScalarConv (fun i j => (cell0PDeriv2Coeff i).coeff j)
          (fun i j => (cell0CachedQQRow i).coeff j) k l -
        cell0ScalarConv (fun i j => (cell0CachedTwoPdQRow i).coeff j)
          (fun i j => (cell0QDerivCoeff i).coeff j) k l +
        cell0ScalarConv (fun i j => (cell0TwoPCoeff i).coeff j)
          (fun i j => (cell0CachedQdQdRow i).coeff j) k l -
        cell0ScalarConv (fun i j => (cell0CachedPQRow i).coeff j)
          (fun i j => (cell0QDeriv2Coeff i).coeff j) k l) := by
  simp only [cell0CachedSignedOuterRow, Polynomial.coeff_neg,
    Polynomial.coeff_sub, Polynomial.coeff_add, cell0OuterConv_coeff]

end SectionSixFirstLowCentralLargeAboveCell0Certificate
end
end PrimesRestrictedDigits
