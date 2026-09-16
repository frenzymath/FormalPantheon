import PrimesRestrictedDigits.SieveDecomposition.RoughSmoothFactorization
import PrimesRestrictedDigits.TypeI.ModulusAggregation

/-!
# Rough/smooth products in the Type I modulus carrier

This supplies the exact cutoff and decimal-coprimality bridge used when the proof of Maynard's
Lemma 7.4 puts `q = d * e`.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- The strict outer and inner source cutoffs multiply to the modulus cutoff
used in the Type I estimate. -/
theorem rough_smooth_product_mem_typeIModuliBelow
    {X epsilon z : Real} {d e : Nat}
    (hX : 0 < X)
    (hdBound : (d : Real) < X ^ (50 / 77 - epsilon))
    (heBound : (e : Real) < X ^ (epsilon / 2))
    (hz : 5 ≤ z) (hdRough : strictRoughPredicate z d)
    (heTen : e.Coprime 10) :
    d * e ∈ typeIModuliBelow (X ^ (50 / 77 - epsilon / 2)) := by
  have hproductBound :
      ((d * e : Nat) : Real) < X ^ (50 / 77 - epsilon / 2) := by
    rw [Nat.cast_mul]
    calc
      (d : Real) * (e : Real) <
          X ^ (50 / 77 - epsilon) * X ^ (epsilon / 2) := by
        gcongr
      _ = X ^ ((50 / 77 - epsilon) + epsilon / 2) :=
        (Real.rpow_add hX _ _).symm
      _ = X ^ (50 / 77 - epsilon / 2) := by ring_nf
  have hdTen : d.Coprime 10 :=
    strictRoughPredicate_coprime_ten hz hdRough
  rw [typeIModuliBelow, Finset.mem_filter, Finset.mem_range, Nat.lt_ceil]
  exact ⟨hproductBound, Nat.coprime_mul_iff_left.mpr ⟨hdTen, heTen⟩⟩

/-- The complete nonnegative rough/smooth double sum injects into the exact
Type I modulus carrier without multiplicity. -/
theorem sum_rough_smooth_products_le_typeIModuliBelow
    {D E : Finset Nat} {X epsilon z : Real} {f : Nat → Real}
    (hX : 0 < X) (hz : 5 ≤ z)
    (hDPos : ∀ d, d ∈ D → 0 < d)
    (hDBound : ∀ d, d ∈ D →
      (d : Real) < X ^ (50 / 77 - epsilon))
    (hDrough : ∀ d, d ∈ D → strictRoughPredicate z d)
    (hEBound : ∀ e, e ∈ E → (e : Real) < X ^ (epsilon / 2))
    (hEsmooth : ∀ e, e ∈ E → weakSmoothPredicate z e)
    (hETen : ∀ e, e ∈ E → e.Coprime 10)
    (hf : ∀ q, q ∈ typeIModuliBelow
      (X ^ (50 / 77 - epsilon / 2)) → 0 ≤ f q) :
    (∑ d ∈ D, ∑ e ∈ E, f (d * e)) ≤
      ∑ q ∈ typeIModuliBelow
        (X ^ (50 / 77 - epsilon / 2)), f q := by
  apply sum_rough_smooth_products_le hDPos hDrough hEsmooth
  · intro d hd e he
    exact rough_smooth_product_mem_typeIModuliBelow hX
      (hDBound d hd) (hEBound e he) hz (hDrough d hd) (hETen e he)
  · exact hf

end PrimesRestrictedDigits
