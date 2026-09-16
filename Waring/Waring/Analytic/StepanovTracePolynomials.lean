import Waring.Analytic.StepanovHasseFrobenius
import Waring.Analytic.StepanovParameters

/-!
# Trace polynomials for the pure-additive Stepanov construction

For an even extension degree `2 * m`, the low trace polynomial contains the
first `m` Frobenius transforms of the phase.  Its expansion by `p ^ m` is the
high half.  Low Hasse derivatives treat that high half as a constant.
-/

namespace Waring.Analytic

open Polynomial
open scoped BigOperators

namespace Stepanov

/-- The first `m` Frobenius-spaced transforms of a polynomial. -/
noncomputable def lowTracePolynomial
    {E : Type*} [CommRing E] (p m : Nat) (f : E[X]) : E[X] :=
  ∑ t ∈ Finset.range m, expand E (p ^ t) f

/-- The second half of the even trace polynomial. -/
noncomputable def highTracePolynomial
    {E : Type*} [CommRing E] (p m : Nat) (f : E[X]) : E[X] :=
  expand E (p ^ m) (lowTracePolynomial p m f)

/-- The full two-half trace polynomial. -/
noncomputable def fullTracePolynomial
    {E : Type*} [CommRing E] (p m : Nat) (f : E[X]) : E[X] :=
  lowTracePolynomial p m f + highTracePolynomial p m f

/-- Evaluation of the high trace half is evaluation of the low half at a
Frobenius power. -/
theorem eval_highTracePolynomial
    {E : Type*} [CommRing E] (p m : Nat) (f : E[X]) (x : E) :
    (highTracePolynomial p m f).eval x =
      (lowTracePolynomial p m f).eval (x ^ (p ^ m)) := by
  exact expand_eval (p ^ m) (lowTracePolynomial p m f) x

/-- Evaluation of the full trace polynomial is the sum of its two halves. -/
theorem eval_fullTracePolynomial
    {E : Type*} [CommRing E] (p m : Nat) (f : E[X]) (x : E) :
    (fullTracePolynomial p m f).eval x =
      (lowTracePolynomial p m f).eval x +
        (lowTracePolynomial p m f).eval (x ^ (p ^ m)) := by
  rw [fullTracePolynomial, eval_add, eval_highTracePolynomial]

/-- A degree bound for the low trace half. -/
theorem natDegree_lowTracePolynomial_le
    {E : Type*} [CommRing E] {p m d : Nat} (hp : 0 < p) (hm : 0 < m)
    {f : E[X]} (hf : f.natDegree ≤ d) :
    (lowTracePolynomial p m f).natDegree ≤ d * p ^ (m - 1) := by
  rw [lowTracePolynomial]
  apply natDegree_sum_le_of_forall_le
  intro t ht
  rw [Finset.mem_range] at ht
  rw [natDegree_expand]
  have ht' : t ≤ m - 1 := by omega
  exact Nat.mul_le_mul hf (Nat.pow_le_pow_right hp ht')

/-- Below order `p ^ m`, the high trace power is constant for Hasse
differentiation. -/
theorem eval_hasseDeriv_mul_highTracePolynomial_pow
    {E : Type*} [CommRing E] {p m r i : Nat} [Fact p.Prime]
    [CharP E p] (hp : 0 < p) (x : E) (e f : E[X])
    (hr : r < p ^ m) :
    (hasseDeriv r (e * highTracePolynomial p m f ^ i)).eval x =
      (hasseDeriv r e).eval x *
        ((lowTracePolynomial p m f).eval (x ^ (p ^ m))) ^ i := by
  rw [highTracePolynomial, ← map_pow]
  simpa only [eval_pow] using
    eval_hasseDeriv_mul_expand_pow hp x e
      (lowTracePolynomial p m f ^ i) hr

/-- On a full-trace fiber, the constant high half can be replaced by the
fiber value minus the low half. -/
theorem eval_hasseDeriv_mul_highTracePolynomial_pow_of_eval_fullTrace
    {E : Type*} [CommRing E] {p m r i : Nat} [Fact p.Prime]
    [CharP E p] (hp : 0 < p) (x c : E) (e f : E[X])
    (hr : r < p ^ m)
    (hx : (fullTracePolynomial p m f).eval x = c) :
    (hasseDeriv r (e * highTracePolynomial p m f ^ i)).eval x =
      (hasseDeriv r e).eval x *
        (c - (lowTracePolynomial p m f).eval x) ^ i := by
  rw [eval_hasseDeriv_mul_highTracePolynomial_pow hp x e f hr]
  congr 2
  rw [eval_fullTracePolynomial] at hx
  rw [add_comm] at hx
  exact eq_sub_of_add_eq hx

end Stepanov

end Waring.Analytic
