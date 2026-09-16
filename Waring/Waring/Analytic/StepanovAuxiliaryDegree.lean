import Waring.Analytic.StepanovAuxiliaryPolynomial
import Waring.Analytic.StepanovFiberParameters

/-!
# Degree bound for the Stepanov auxiliary polynomial

This file bounds the full auxiliary polynomial independently of the later
top-degree argument proving that it is nonzero.
 -/

namespace Waring.Analytic

open Polynomial
open scoped BigOperators

namespace Stepanov

/-- The high trace half has the degree bound used in the auxiliary sum. -/
theorem natDegree_highTracePolynomial_le_degreeBase
    {E : Type*} [CommRing E] {p h d : Nat} (hp : 0 < p)
    {f : E[X]} (hf : f.natDegree ≤ d) :
    (highTracePolynomial p (h + 3) f).natDegree ≤
      d * degreeBase p h := by
  rw [highTracePolynomial, natDegree_expand]
  have hlow :
      (lowTracePolynomial p (h + 3) f).natDegree ≤
        d * p ^ (h + 2) := by
    have hlow' := natDegree_lowTracePolynomial_le
      (m := h + 3) (d := d) hp (by omega) hf
    rw [show h + 3 - 1 = h + 2 by omega] at hlow'
    exact hlow'
  calc
    (lowTracePolynomial p (h + 3) f).natDegree * p ^ (h + 3) ≤
        (d * p ^ (h + 2)) * p ^ (h + 3) :=
      Nat.mul_le_mul_right _ hlow
    _ = d * degreeBase p h := by
      rw [mul_assoc, ← pow_add]
      unfold degreeBase
      rw [show h + 2 + (h + 3) = 2 * h + 5 by omega]

/-- Each summand of the auxiliary polynomial lies strictly below the common
degree bound. -/
theorem natDegree_auxiliarySummand_lt
    {E : Type*} [Field E] {p h d i k : Nat} (hp : 0 < p)
    {e f : E[X]} (he : e.natDegree < S p h)
    (hf : f.natDegree ≤ d) (hi : i < p) (hk : k ≤ K p h) :
    ((e * highTracePolynomial p (h + 3) f ^ i) *
        X ^ (p ^ (2 * (h + 3)) * k)).natDegree <
      auxiliaryDegreeBound p h d := by
  have hhigh :=
    natDegree_highTracePolynomial_le_degreeBase (h := h) hp hf
  have hhighPow :
      (highTracePolynomial p (h + 3) f ^ i).natDegree ≤
        i * (d * degreeBase p h) :=
    natDegree_pow_le_of_le i hhigh
  have hdegree :
      ((e * highTracePolynomial p (h + 3) f ^ i) *
          X ^ (p ^ (2 * (h + 3)) * k)).natDegree ≤
        e.natDegree + i * (d * degreeBase p h) +
          p ^ (2 * (h + 3)) * k := by
    calc
      ((e * highTracePolynomial p (h + 3) f ^ i) *
          X ^ (p ^ (2 * (h + 3)) * k)).natDegree ≤
          (e * highTracePolynomial p (h + 3) f ^ i).natDegree +
            (X ^ (p ^ (2 * (h + 3)) * k) : E[X]).natDegree :=
        natDegree_mul_le
      _ ≤ e.natDegree + i * (d * degreeBase p h) +
          p ^ (2 * (h + 3)) * k := by
        exact Nat.add_le_add
          (natDegree_mul_le.trans (Nat.add_le_add_left hhighPow _))
          (natDegree_X_pow_le _)
  have hi' : i ≤ p - 1 := by omega
  have hphase :
      i * (d * degreeBase p h) ≤
        degreeBase p h * (d * (p - 1)) := by
    calc
      i * (d * degreeBase p h) ≤
          (p - 1) * (d * degreeBase p h) :=
        Nat.mul_le_mul_right _ hi'
      _ = degreeBase p h * (d * (p - 1)) := by ring
  have hpow :
      p ^ (2 * (h + 3)) = degreeBase p h * p := by
    unfold degreeBase
    rw [← pow_succ]
    congr 1
  have hmonomial :
      p ^ (2 * (h + 3)) * k ≤
        degreeBase p h * (p * K p h) := by
    rw [hpow]
    simpa only [mul_assoc] using
      Nat.mul_le_mul_left (degreeBase p h) (Nat.mul_le_mul_left p hk)
  have htotal :
      e.natDegree + i * (d * degreeBase p h) +
          p ^ (2 * (h + 3)) * k <
        auxiliaryDegreeBound p h d := by
    have hsum :
        e.natDegree + i * (d * degreeBase p h) +
            p ^ (2 * (h + 3)) * k <
          S p h + degreeBase p h * (d * (p - 1)) +
            degreeBase p h * (p * K p h) := by
      omega
    refine hsum.trans_eq ?_
    unfold auxiliaryDegreeBound
    rw [Nat.mul_add]
    exact Nat.add_assoc _ _ _
  exact hdegree.trans_lt htotal

/-- The complete auxiliary polynomial lies strictly below the common degree
bound. -/
theorem natDegree_auxiliaryPolynomial_lt
    {E : Type*} [Field E] {p h d : Nat} (hp : 0 < p)
    {f : E[X]} (hf : f.natDegree ≤ d)
    (a : AuxiliaryCoefficients E p h) :
    (auxiliaryPolynomial p h f a).natDegree <
      auxiliaryDegreeBound p h d := by
  have hboundPos : 0 < auxiliaryDegreeBound p h d := by
    unfold auxiliaryDegreeBound
    exact Nat.add_pos_left (Nat.pow_pos hp) _
  have hterm (i : Fin p) (k : Fin (K p h + 1)) :
      ((auxiliaryCoefficientPolynomial a i k *
          highTracePolynomial p (h + 3) f ^ (i : Nat)) *
            X ^ (p ^ (2 * (h + 3)) * (k : Nat))).natDegree <
        auxiliaryDegreeBound p h d :=
    natDegree_auxiliarySummand_lt hp
      (natDegree_auxiliaryCoefficientPolynomial_lt hp a i k) hf
      i.isLt (by omega)
  have hinner (i : Fin p) :
      (∑ k : Fin (K p h + 1),
        (auxiliaryCoefficientPolynomial a i k *
          highTracePolynomial p (h + 3) f ^ (i : Nat)) *
            X ^ (p ^ (2 * (h + 3)) * (k : Nat))).natDegree ≤
        auxiliaryDegreeBound p h d - 1 := by
    apply natDegree_sum_le_of_forall_le
    intro k hk
    exact Nat.le_pred_of_lt (hterm i k)
  unfold auxiliaryPolynomial
  refine (natDegree_sum_le_of_forall_le _ _ ?_).trans_lt
    (Nat.pred_lt hboundPos.ne')
  intro i hi
  exact hinner i

end Stepanov

end Waring.Analytic
