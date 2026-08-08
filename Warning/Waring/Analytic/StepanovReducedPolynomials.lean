import Waring.Analytic.StepanovTracePolynomials

/-!
# Reduced Stepanov derivative conditions

On a full-trace fiber, a low Hasse derivative of one auxiliary term is the
evaluation of a polynomial of degree below `D`.  These reduced polynomials
are the homogeneous linear conditions imposed on the auxiliary coefficients.
-/

namespace Waring.Analytic

open Polynomial

namespace Stepanov

/-- The polynomial obtained after reducing one Hasse-derivative term on a
full-trace fiber. -/
noncomputable def reducedAuxiliaryTerm
    {E : Type*} [CommRing E] (p h : Nat) (c : E) (r i k : Nat)
    (e f : E[X]) : E[X] :=
  hasseDeriv r e *
    (C c - lowTracePolynomial p (h + 3) f) ^ i * X ^ k

/-- Evaluation of one auxiliary Hasse derivative agrees with its reduced
polynomial on a full-trace fiber. -/
theorem eval_hasseDeriv_auxiliaryTerm_eq_reduced
    {E : Type*} [CommRing E] {p h r i k : Nat} [Fact p.Prime]
    [CharP E p] (hp : 1 < p) (x c : E) (e f : E[X])
    (hr : r < p ^ (h + 3))
    (hxpow : x ^ (p ^ (2 * (h + 3))) = x)
    (hxtrace : (fullTracePolynomial p (h + 3) f).eval x = c) :
    (hasseDeriv r
      ((e * highTracePolynomial p (h + 3) f ^ i) *
        X ^ (p ^ (2 * (h + 3)) * k))).eval x =
      (reducedAuxiliaryTerm p h c r i k e f).eval x := by
  have hrFull : r < p ^ (2 * (h + 3)) := by
    exact hr.trans_le (Nat.pow_le_pow_right hp.le (by omega))
  rw [eval_hasseDeriv_mul_X_pow_pow_mul hp.pos x hxpow
    (e * highTracePolynomial p (h + 3) f ^ i) hrFull]
  rw [eval_hasseDeriv_mul_highTracePolynomial_pow_of_eval_fullTrace
    hp.pos x c e f hr hxtrace]
  simp [reducedAuxiliaryTerm, mul_assoc]

/-- Every reduced derivative condition has degree strictly below the
parameter `D`. -/
theorem natDegree_reducedAuxiliaryTerm_lt_D
    {E : Type*} [CommRing E] {p h d r i k : Nat} (hp : 0 < p)
    (c : E) {e f : E[X]} (he : e.natDegree < S p h)
    (hf : f.natDegree ≤ d) (hi : i < p) (hk : k ≤ K p h) :
    (reducedAuxiliaryTerm p h c r i k e f).natDegree < D p h d := by
  have hm : 0 < h + 3 := by omega
  have hlow :
      (lowTracePolynomial p (h + 3) f).natDegree ≤
        d * p ^ (h + 2) := by
    simpa only [show h + 3 - 1 = h + 2 by omega] using
      natDegree_lowTracePolynomial_le hp hm hf
  have hsub :
      (C c - lowTracePolynomial p (h + 3) f).natDegree ≤
        d * p ^ (h + 2) := by
    exact (natDegree_sub_le _ _).trans <| by
      apply max_le
      · simp
      · exact hlow
  have hderiv : (hasseDeriv r e).natDegree ≤ e.natDegree :=
    (natDegree_hasseDeriv_le e r).trans (Nat.sub_le _ _)
  have hpow :
      ((C c - lowTracePolynomial p (h + 3) f) ^ i).natDegree ≤
        i * (d * p ^ (h + 2)) :=
    natDegree_pow_le_of_le i hsub
  have hdegree :
      (reducedAuxiliaryTerm p h c r i k e f).natDegree ≤
        e.natDegree + i * (d * p ^ (h + 2)) + k := by
    unfold reducedAuxiliaryTerm
    calc
      (hasseDeriv r e *
          (C c - lowTracePolynomial p (h + 3) f) ^ i * X ^ k).natDegree ≤
          (hasseDeriv r e).natDegree +
            ((C c - lowTracePolynomial p (h + 3) f) ^ i).natDegree +
              (X ^ k : E[X]).natDegree := by
        exact natDegree_mul_le.trans
          (Nat.add_le_add natDegree_mul_le le_rfl)
      _ ≤ e.natDegree + i * (d * p ^ (h + 2)) + k := by
        simpa using Nat.add_le_add (Nat.add_le_add hderiv hpow)
          (natDegree_X_pow_le k)
  have hi' : i ≤ p - 1 := by omega
  have hphase :
      i * (d * p ^ (h + 2)) ≤
        (p - 1) * (d * p ^ (h + 2)) :=
    Nat.mul_le_mul_right _ hi'
  have htotal :
      e.natDegree + i * (d * p ^ (h + 2)) + k <
        S p h + (p - 1) * (d * p ^ (h + 2)) + K p h := by
    omega
  refine hdegree.trans_lt (htotal.trans_eq ?_)
  simp only [D, A]
  ring

end Stepanov

end Waring.Analytic
