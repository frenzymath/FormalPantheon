import Waring.Analytic.StepanovAuxiliaryPolynomial
import Waring.Analytic.StepanovFiberParameters

/-!
# Nonvanishing and degree of the Stepanov auxiliary polynomial

The high half of the trace polynomial has exact degree

`d * p ^ (2 * h + 5)`

when the phase has positive degree `d`.  Thus every nonzero summand of the
auxiliary polynomial has the degree label from
`StepanovDegreeSeparation.lean`.  Filtering out zero coefficient polynomials
and applying degree separation proves that a nonzero coefficient family
produces a nonzero auxiliary polynomial.

-/

namespace Waring.Analytic

open Polynomial
open scoped BigOperators

namespace Stepanov

/-- For a positive-degree phase, the last Frobenius transform is the unique
top-degree summand of the low trace half. -/
theorem natDegree_lowTracePolynomial_eq
    {E : Type*} [Field E] {p h d : Nat} (hp : 1 < p)
    (hdpos : 0 < d) {f : E[X]} (hf : f.natDegree = d) :
    (lowTracePolynomial p (h + 3) f).natDegree =
      d * p ^ (h + 2) := by
  have hprefix :
      (lowTracePolynomial p (h + 2) f).natDegree <=
        d * p ^ ((h + 2) - 1) :=
    natDegree_lowTracePolynomial_le hp.pos (by omega) hf.le
  have hprefix' :
      (lowTracePolynomial p (h + 2) f).natDegree <
        d * p ^ (h + 2) := by
    refine hprefix.trans_lt ?_
    rw [show h + 2 - 1 = h + 1 by omega]
    exact Nat.mul_lt_mul_of_pos_left
      (Nat.pow_lt_pow_right hp (by omega)) hdpos
  rw [lowTracePolynomial,
    show h + 3 = (h + 2) + 1 by omega,
    Finset.sum_range_succ]
  change
    (lowTracePolynomial p (h + 2) f +
      expand E (p ^ (h + 2)) f).natDegree = _
  calc
    _ = (expand E (p ^ (h + 2)) f).natDegree :=
      Polynomial.natDegree_add_eq_right_of_natDegree_lt (by
        simpa only [Polynomial.natDegree_expand, hf] using hprefix')
    _ = d * p ^ (h + 2) := by
      rw [Polynomial.natDegree_expand, hf]

/-- The high trace half has the exact degree used in the mixed degree
labels. -/
theorem natDegree_highTracePolynomial_eq
    {E : Type*} [Field E] {p h d : Nat} (hp : 1 < p)
    (hdpos : 0 < d) {f : E[X]} (hf : f.natDegree = d) :
    (highTracePolynomial p (h + 3) f).natDegree =
      d * degreeBase p h := by
  rw [highTracePolynomial, Polynomial.natDegree_expand,
    natDegree_lowTracePolynomial_eq hp hdpos hf, degreeBase]
  simp only [Nat.mul_assoc, ← pow_add]
  congr 2
  omega

/-- A nonzero coefficient family has at least one nonzero encoded coefficient
polynomial. -/
theorem exists_auxiliaryCoefficientPolynomial_ne_zero
    {E : Type*} [Field E] {p h : Nat}
    {a : AuxiliaryCoefficients E p h} (ha : a ≠ 0) :
    ∃ i : Fin p, ∃ k : Fin (K p h + 1),
      auxiliaryCoefficientPolynomial a i k ≠ 0 := by
  by_contra hall
  push Not at hall
  apply ha
  funext i k
  change a i k = 0
  apply (degreeLTEquiv E (S p h)).symm.injective
  rw [map_zero]
  apply Subtype.ext
  exact hall i k

/-- If `0 < d < p`, a nonzero coefficient family produces a nonzero
Stepanov auxiliary polynomial for every phase of exact degree `d`. -/
theorem auxiliaryPolynomial_ne_zero
    {E : Type*} [Field E] {p h d : Nat} (hp : p.Prime)
    (hdpos : 0 < d) (hdp : d < p) {f : E[X]}
    (hf : f.natDegree = d) {a : AuxiliaryCoefficients E p h}
    (ha : a ≠ 0) :
    auxiliaryPolynomial p h f a ≠ 0 := by
  classical
  let I := Fin p × Fin (K p h + 1)
  let term : I → E[X] := fun z =>
    (auxiliaryCoefficientPolynomial a z.1 z.2 *
      highTracePolynomial p (h + 3) f ^ (z.1 : Nat)) *
        X ^ (p ^ (2 * (h + 3)) * (z.2 : Nat))
  let u : Finset I := Finset.univ.filter fun z =>
    auxiliaryCoefficientPolynomial a z.1 z.2 ≠ 0
  have hhighDegree :
      (highTracePolynomial p (h + 3) f).natDegree =
        d * degreeBase p h :=
    natDegree_highTracePolynomial_eq hp.one_lt hdpos hf
  have hhighNe : highTracePolynomial p (h + 3) f ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.natDegree_zero] at hhighDegree
    have hpositive : 0 < d * degreeBase p h :=
      Nat.mul_pos hdpos (Nat.pow_pos hp.pos)
    omega
  have hQ : p ^ (2 * (h + 3)) = degreeBase p h * p := by
    rw [degreeBase,
      show 2 * (h + 3) = (2 * h + 5) + 1 by omega,
      pow_succ]
  obtain ⟨i, k, hik⟩ := exists_auxiliaryCoefficientPolynomial_ne_zero ha
  have hu : u.Nonempty := by
    refine Finset.filter_nonempty_iff.mpr
      ⟨(i, k), Finset.mem_univ _, hik⟩
  have htermNe : ∀ z ∈ u, term z ≠ 0 := by
    intro z hz
    have he : auxiliaryCoefficientPolynomial a z.1 z.2 ≠ 0 :=
      (Finset.mem_filter.mp hz).2
    exact mul_ne_zero (mul_ne_zero he (pow_ne_zero _ hhighNe))
      (pow_ne_zero _ Polynomial.X_ne_zero)
  have hs : ∀ z ∈ u,
      (auxiliaryCoefficientPolynomial a z.1 z.2).natDegree < S p h := by
    intro z hz
    exact natDegree_auxiliaryCoefficientPolynomial_lt hp.pos a z.1 z.2
  have hi : ∀ z ∈ u, (z.1 : Nat) < p := by
    intro z hz
    exact z.1.isLt
  have htermDegree : ∀ z ∈ u,
      (term z).natDegree = degreeLabel p h d
        (auxiliaryCoefficientPolynomial a z.1 z.2).natDegree z.1 z.2 := by
    intro z hz
    have he : auxiliaryCoefficientPolynomial a z.1 z.2 ≠ 0 :=
      (Finset.mem_filter.mp hz).2
    simp only [term]
    rw [Polynomial.natDegree_mul_X_pow _
      (mul_ne_zero he (pow_ne_zero _ hhighNe)),
      Polynomial.natDegree_mul he (pow_ne_zero _ hhighNe),
      Polynomial.natDegree_pow, hhighDegree, hQ]
    unfold degreeLabel
    ring
  have hcoordinates : Set.InjOn
      (fun z : I =>
        ((auxiliaryCoefficientPolynomial a z.1 z.2).natDegree,
          (z.1 : Nat), (z.2 : Nat))) (u : Set I) := by
    intro z hz w hw hzw
    have hiNat : (z.1 : Nat) = (w.1 : Nat) :=
      congrArg (fun q : Nat × Nat × Nat => q.2.1) hzw
    have hkNat : (z.2 : Nat) = (w.2 : Nat) :=
      congrArg (fun q : Nat × Nat × Nat => q.2.2) hzw
    exact Prod.ext (Fin.ext hiNat) (Fin.ext hkNat)
  have hnonzero : (∑ z ∈ u, term z) ≠ 0 :=
    polynomial_sum_ne_zero_of_degreeLabel hp hdpos hdp
      (fun z : I =>
        (auxiliaryCoefficientPolynomial a z.1 z.2).natDegree)
      (fun z : I => (z.1 : Nat)) (fun z : I => (z.2 : Nat))
      hu htermNe hs hi htermDegree hcoordinates
  have hsum : (∑ z ∈ u, term z) = auxiliaryPolynomial p h f a := by
    rw [auxiliaryPolynomial]
    change (∑ z ∈ u, term z) =
      ∑ i : Fin p, ∑ k : Fin (K p h + 1), term (i, k)
    rw [← Fintype.sum_prod_type]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro z hzuniv hznot
    have hezero : auxiliaryCoefficientPolynomial a z.1 z.2 = 0 := by
      by_contra he
      exact hznot (Finset.mem_filter.mpr ⟨hzuniv, he⟩)
    simp [term, hezero]
  rw [← hsum]
  exact hnonzero

end Stepanov

end Waring.Analytic
