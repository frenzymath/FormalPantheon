import Waring.Analytic.StepanovAuxiliaryLinear

/-!
# The pure-additive Stepanov auxiliary polynomial

This file turns the nonzero kernel coefficient family into the auxiliary
polynomial and proves that all Hasse derivatives below `R` vanish on the
prescribed full-trace fiber.  Nonvanishing of the auxiliary polynomial itself
is handled separately by its distinct top degrees.
-/

namespace Waring.Analytic

open Polynomial
open scoped BigOperators

namespace Stepanov

/-- Every reduced condition polynomial has degree below `D`. -/
theorem natDegree_reducedAuxiliaryConditionPolynomial_lt_D
    {E : Type*} [Field E] {p h d r : Nat} (hp : 0 < p)
    (c : E) {f : E[X]} (hf : f.natDegree ≤ d)
    (a : AuxiliaryCoefficients E p h) :
    (reducedAuxiliaryConditionPolynomial p h c r f a).natDegree <
      D p h d := by
  have hDpos : 0 < D p h d := by
    exact Nat.add_pos_left (Nat.add_pos_left (Nat.pow_pos hp) _) _
  have hterm (i : Fin p) (k : Fin (K p h + 1)) :
      (reducedAuxiliaryTerm p h c r i k
        (auxiliaryCoefficientPolynomial a i k) f).natDegree < D p h d :=
    natDegree_reducedAuxiliaryTerm_lt_D hp c
      (natDegree_auxiliaryCoefficientPolynomial_lt hp a i k)
      hf i.isLt (by omega)
  have hinner (i : Fin p) :
      (∑ k : Fin (K p h + 1),
        reducedAuxiliaryTerm p h c r i k
          (auxiliaryCoefficientPolynomial a i k) f).natDegree ≤
        D p h d - 1 := by
    apply natDegree_sum_le_of_forall_le
    intro k hk
    exact Nat.le_pred_of_lt (hterm i k)
  unfold reducedAuxiliaryConditionPolynomial
  refine (natDegree_sum_le_of_forall_le _ _ ?_).trans_lt
    (Nat.pred_lt (Nat.ne_of_gt hDpos))
  intro i hi
  exact hinner i

/-- A coefficient family in the linear kernel makes every reduced condition
polynomial vanish. -/
theorem reducedAuxiliaryConditionPolynomial_eq_zero_of_linear_eq_zero
    {E : Type*} [Field E] {p h d : Nat} (hp : 0 < p)
    (c : E) {f : E[X]} (hf : f.natDegree ≤ d)
    {a : AuxiliaryCoefficients E p h}
    (ha : reducedAuxiliaryConditionLinear p h d c f a = 0)
    {r : Nat} (hr : r < R p h) :
    reducedAuxiliaryConditionPolynomial p h c r f a = 0 := by
  let F := reducedAuxiliaryConditionPolynomial p h c r f a
  have hdegree : F.natDegree < D p h d :=
    natDegree_reducedAuxiliaryConditionPolynomial_lt_D hp c hf a
  ext j
  by_cases hj : j < D p h d
  · have hcoeff := congrFun (congrFun ha ⟨r, hr⟩) ⟨j, hj⟩
    change (reducedAuxiliaryConditionPolynomial p h c r f a).coeff j = 0 at hcoeff
    exact hcoeff
  · rw [coeff_eq_zero_of_natDegree_lt (hdegree.trans_le (Nat.le_of_not_gt hj)),
      coeff_zero]

/-- The auxiliary polynomial built from a coefficient family. -/
noncomputable def auxiliaryPolynomial
    {E : Type*} [Field E] (p h : Nat) (f : E[X])
    (a : AuxiliaryCoefficients E p h) : E[X] :=
  ∑ i : Fin p, ∑ k : Fin (K p h + 1),
    (auxiliaryCoefficientPolynomial a i k *
      highTracePolynomial p (h + 3) f ^ (i : Nat)) *
        X ^ (p ^ (2 * (h + 3)) * (k : Nat))

/-- On a full-trace fiber, a low Hasse derivative of the auxiliary polynomial
is the corresponding reduced condition polynomial. -/
theorem eval_hasseDeriv_auxiliaryPolynomial_eq_reduced
    {E : Type*} [Field E] {p h r : Nat} [Fact p.Prime]
    [CharP E p] (hp : 1 < p) (x c : E) (f : E[X])
    (a : AuxiliaryCoefficients E p h)
    (hr : r < p ^ (h + 3))
    (hxpow : x ^ (p ^ (2 * (h + 3))) = x)
    (hxtrace : (fullTracePolynomial p (h + 3) f).eval x = c) :
    (hasseDeriv r (auxiliaryPolynomial p h f a)).eval x =
      (reducedAuxiliaryConditionPolynomial p h c r f a).eval x := by
  change (evalRingHom x)
      (hasseDeriv r (auxiliaryPolynomial p h f a)) =
    (evalRingHom x)
      (reducedAuxiliaryConditionPolynomial p h c r f a)
  simp only [auxiliaryPolynomial, reducedAuxiliaryConditionPolynomial,
    map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  exact eval_hasseDeriv_auxiliaryTerm_eq_reduced hp x c
    (auxiliaryCoefficientPolynomial a i k) f hr hxpow hxtrace

/-- A kernel coefficient family gives all required Hasse vanishings on the
trace fiber. -/
theorem hasseDeriv_auxiliaryPolynomial_eval_eq_zero_of_linear_eq_zero
    {E : Type*} [Field E] {p h d : Nat} [Fact p.Prime]
    [CharP E p] (hp : 1 < p) (c : E) {f : E[X]}
    (hf : f.natDegree ≤ d) {a : AuxiliaryCoefficients E p h}
    (ha : reducedAuxiliaryConditionLinear p h d c f a = 0)
    {x : E} (hxpow : x ^ (p ^ (2 * (h + 3))) = x)
    (hxtrace : (fullTracePolynomial p (h + 3) f).eval x = c)
    {r : Nat} (hr : r < R p h) :
    (hasseDeriv r (auxiliaryPolynomial p h f a)).eval x = 0 := by
  have hrpow : r < p ^ (h + 3) := hr.trans (R_lt_pow hp)
  rw [eval_hasseDeriv_auxiliaryPolynomial_eq_reduced hp x c f a
    hrpow hxpow hxtrace,
    reducedAuxiliaryConditionPolynomial_eq_zero_of_linear_eq_zero
      hp.pos c hf ha hr,
    eval_zero]

/-- There is a nonzero coefficient family whose auxiliary polynomial has all
required low Hasse derivatives zero on the trace fiber. -/
theorem exists_auxiliaryCoefficients_hasse_vanish
    {E : Type*} [Field E] {p h d : Nat} [Fact p.Prime]
    [CharP E p] (hp : 1 < p) (hd : d < p) (c : E) {f : E[X]}
    (hf : f.natDegree ≤ d) :
    ∃ a : AuxiliaryCoefficients E p h,
      a ≠ 0 ∧
        ∀ x : E,
          x ^ (p ^ (2 * (h + 3))) = x →
          (fullTracePolynomial p (h + 3) f).eval x = c →
          ∀ r < R p h,
            (hasseDeriv r (auxiliaryPolynomial p h f a)).eval x = 0 := by
  obtain ⟨a, hane, ha⟩ :=
    exists_nonzero_auxiliaryCoefficients hp hd c f
  refine ⟨a, hane, ?_⟩
  intro x hxpow hxtrace r hr
  exact hasseDeriv_auxiliaryPolynomial_eval_eq_zero_of_linear_eq_zero
    hp c hf ha hxpow hxtrace hr

end Stepanov

end Waring.Analytic
