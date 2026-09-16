import Waring.Analytic.WeilEulerCoefficients
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# The finite-degree Artin polynomial

The coefficient of degree `n` is the total formal-root weight over all monic
degree-`n` polynomials.  Coefficient cancellation makes this a polynomial of
degree below the highest phase exponent.  Its constant term is one, so its
reverse is monic; over `Complex`, reversing the root factorization expresses
the original polynomial as a product of the factors `1 - alpha * X`.
-/

namespace Waring.Analytic

open Polynomial
open scoped BigOperators

namespace Weil

variable {K : Type*} [Field K] [Fintype K]

/-- The total formal-root weight over monic polynomials of one fixed degree. -/
noncomputable def monicFormalRootWeightSum
    (character : AddChar K Complex) (b : Fin 5 → K) (n : Nat) : Complex :=
  ∑ F : {F : K[X] // F.Monic ∧ F.natDegree = n},
    formalRootWeight character b F.1

/-- The degree-bounded Artin coefficient polynomial. -/
noncomputable def artinLPolynomial
    (character : AddChar K Complex) (b : Fin 5 → K) (d : Nat) : Complex[X] :=
  ∑ n ∈ Finset.range d,
    monomial n (monicFormalRootWeightSum character b n)

/-- The only monic polynomial of degree zero has formal-root weight one. -/
theorem monicFormalRootWeightSum_zero
    (character : AddChar K Complex) (b : Fin 5 → K) :
    monicFormalRootWeightSum character b 0 = 1 := by
  let oneMonic : {F : K[X] // F.Monic ∧ F.natDegree = 0} :=
    ⟨1, monic_one, natDegree_one⟩
  letI : Unique {F : K[X] // F.Monic ∧ F.natDegree = 0} :=
    { default := oneMonic
      uniq := by
        intro F
        apply Subtype.ext
        exact eq_one_of_monic_natDegree_zero F.2.1 F.2.2 }
  rw [monicFormalRootWeightSum, Fintype.sum_unique]
  exact formalRootWeight_multiset_prod character b 0 (by simp)

/-- Coefficients below `d` are the monic weight sums and all later
coefficients vanish. -/
theorem coeff_artinLPolynomial
    (character : AddChar K Complex) (b : Fin 5 → K) (d n : Nat) :
    (artinLPolynomial character b d).coeff n =
      if n < d then monicFormalRootWeightSum character b n else 0 := by
  simp [artinLPolynomial, coeff_monomial]

/-- The Artin coefficient polynomial has constant coefficient one. -/
theorem coeff_zero_artinLPolynomial
    (character : AddChar K Complex) (b : Fin 5 → K) {d : Nat}
    (hdpos : 0 < d) :
    (artinLPolynomial character b d).coeff 0 = 1 := by
  rw [coeff_artinLPolynomial, if_pos hdpos,
    monicFormalRootWeightSum_zero]

/-- The Artin coefficient polynomial is nonzero. -/
theorem artinLPolynomial_ne_zero
    (character : AddChar K Complex) (b : Fin 5 → K) {d : Nat}
    (hdpos : 0 < d) :
    artinLPolynomial character b d ≠ 0 := by
  intro hzero
  have hcoeff := coeff_zero_artinLPolynomial character b hdpos
  rw [hzero, coeff_zero] at hcoeff
  exact zero_ne_one hcoeff

/-- The Artin coefficient polynomial has degree strictly below the highest
phase exponent. -/
theorem natDegree_artinLPolynomial_lt
    (character : AddChar K Complex) (b : Fin 5 → K) {d : Nat}
    (hdpos : 0 < d) :
    (artinLPolynomial character b d).natDegree < d := by
  rw [natDegree_lt_iff_degree_lt
    (artinLPolynomial_ne_zero character b hdpos),
    degree_lt_iff_coeff_zero]
  intro n hn
  rw [coeff_artinLPolynomial, if_neg (not_lt_of_ge hn)]

/-- A polynomial with nonzero constant coefficient is recovered by reversing
twice. -/
theorem reverse_reverse_of_coeff_zero_ne_zero
    {R : Type*} [Semiring R] {A : R[X]} (hA0 : A.coeff 0 ≠ 0) :
    A.reverse.reverse = A := by
  have htrail : A.natTrailingDegree = 0 :=
    natTrailingDegree_eq_zero.mpr (Or.inr hA0)
  rw [reverse, reverse_natDegree, htrail, Nat.sub_zero]
  exact reflect_reflect

/-- The reverse of the Artin coefficient polynomial is monic. -/
theorem monic_reverse_artinLPolynomial
    (character : AddChar K Complex) (b : Fin 5 → K) {d : Nat}
    (hdpos : 0 < d) :
    (artinLPolynomial character b d).reverse.Monic := by
  rw [Monic, reverse_leadingCoeff,
    trailingCoeff_eq_coeff_zero (by
      rw [coeff_zero_artinLPolynomial character b hdpos]
      exact one_ne_zero),
    coeff_zero_artinLPolynomial character b hdpos]

/-- Reversal commutes with a finite multiset product over an integral
domain. -/
theorem reverse_multiset_prod_of_domain
    {R : Type*} [CommRing R] [IsDomain R] (s : Multiset R[X]) :
    s.prod.reverse = (s.map reverse).prod := by
  induction s using Multiset.induction_on with
  | empty => simp [reverse]
  | cons F s ih => simp [reverse_mul_of_domain, ih]

/-- Reversing a monic linear factor gives a reciprocal linear factor. -/
theorem reverse_X_sub_C (a : Complex) :
    (X - C a : Complex[X]).reverse = 1 - C a * X := by
  rw [reverse, natDegree_X_sub_C, reflect_sub, reflect_one_X,
    reflect_C, pow_one]

/-- Over `Complex`, the Artin coefficient polynomial is the product of
`1 - alpha * X` over the roots of its monic reverse. -/
theorem artinLPolynomial_eq_prod_roots
    (character : AddChar K Complex) (b : Fin 5 → K) {d : Nat}
    (hdpos : 0 < d) :
    artinLPolynomial character b d =
      ((artinLPolynomial character b d).reverse.roots.map
        (fun a ↦ 1 - C a * X)).prod := by
  let A := artinLPolynomial character b d
  let Q := A.reverse
  have hA0 : A.coeff 0 ≠ 0 := by
    change (artinLPolynomial character b d).coeff 0 ≠ 0
    rw [coeff_zero_artinLPolynomial character b hdpos]
    exact one_ne_zero
  have hQmonic : Q.Monic := monic_reverse_artinLPolynomial character b hdpos
  have hsplit : Q.Splits := IsAlgClosed.splits Q
  have hfactor := hsplit.eq_prod_roots_of_monic hQmonic
  have hreversed := congrArg reverse hfactor
  rw [reverse_reverse_of_coeff_zero_ne_zero hA0] at hreversed
  rw [reverse_multiset_prod_of_domain] at hreversed
  simpa only [Q, A, Multiset.map_map, Function.comp_apply,
    reverse_X_sub_C] using hreversed

/-- The reciprocal-root multiset has cardinality below the phase degree. -/
theorem card_roots_reverse_artinLPolynomial_lt
    (character : AddChar K Complex) (b : Fin 5 → K) {d : Nat}
    (hdpos : 0 < d) :
    Multiset.card (artinLPolynomial character b d).reverse.roots < d := by
  rw [Polynomial.splits_iff_card_roots.mp
    (IsAlgClosed.splits (artinLPolynomial character b d).reverse)]
  exact (reverse_natDegree_le _).trans_lt
    (natDegree_artinLPolynomial_lt character b hdpos)

end Weil

end Waring.Analytic
