import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-!
# Fixed-rank LLL reduction

This records the reduction conditions from `LLL-1982-CWI`, equations
(1.2)--(1.5), with Lovasz parameter `3/4`. Existence of a reduced integral
basis is a separate theorem; this file only defines the analytic predicate.
-/

namespace PrimesRestrictedDigits

open InnerProductSpace

/-- The Gram--Schmidt coefficient of `b i` along the `j`th orthogonalized
vector. Its intended use has `j < i`. -/
noncomputable def lllCoefficient {n : Nat} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace Real E]
    (b : Fin n -> E) (i j : Fin n) : Real :=
  inner Real (gramSchmidt Real b j) (b i) /
    ‖gramSchmidt Real b j‖ ^ 2

theorem eq_gramSchmidt_add_sum {n : Nat} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace Real E]
    (b : Fin n -> E) (i : Fin n) :
    b i = gramSchmidt Real b i +
      ∑ j ∈ Finset.Iio i,
        lllCoefficient b i j • gramSchmidt Real b j := by
  simpa [lllCoefficient] using
    (InnerProductSpace.gramSchmidt_def'' Real b i)

/-- LLL reduction with size bound `1/2` and Lovasz parameter `3/4`. -/
structure IsLLLReduced {n : Nat} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace Real E]
    (b : Fin n -> E) : Prop where
  linearIndependent : LinearIndependent Real b
  coefficient_bound :
    ∀ i j, j < i -> |lllCoefficient b i j| <= 1 / 2
  lovasz :
    ∀ (i : Fin n) (hi : i.val + 1 < n),
      (3 / 4 : Real) * ‖gramSchmidt Real b i‖ ^ 2 <=
        ‖gramSchmidt Real b ⟨i.val + 1, hi⟩ +
            lllCoefficient b ⟨i.val + 1, hi⟩ i •
              gramSchmidt Real b i‖ ^ 2

theorem IsLLLReduced.gramSchmidt_ne_zero
    {n : Nat} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace Real E] {b : Fin n -> E}
    (hb : IsLLLReduced b) (i : Fin n) :
    gramSchmidt Real b i ≠ 0 :=
  InnerProductSpace.gramSchmidt_ne_zero i hb.linearIndependent

end PrimesRestrictedDigits
