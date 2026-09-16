import Waring.Analytic.StepanovAuxiliaryDegree
import Waring.Analytic.StepanovRootCount

/-!
# From Stepanov vanishings to a trace-fiber count

The Hasse root-multiplicity inequality and the exact parameter factorization
turn the auxiliary polynomial into the required point count.
 -/

namespace Waring.Analytic

open Polynomial

namespace Stepanov

/-- Any point set carrying the required auxiliary Hasse vanishings has size
strictly below the trace-fiber bound. -/
theorem card_lt_traceFiberBound_of_auxiliary
    {E : Type*} [Field E] {p h d : Nat} (hp : 0 < p)
    {f : E[X]} (hf : f.natDegree ≤ d)
    (a : AuxiliaryCoefficients E p h) (ha : auxiliaryPolynomial p h f a ≠ 0)
    (points : Finset E)
    (hvanish : ∀ x ∈ points, ∀ r < R p h,
      (hasseDeriv r (auxiliaryPolynomial p h f a)).eval x = 0) :
    points.card < traceFiberBound p h d := by
  have hroot :
      R p h * points.card ≤ (auxiliaryPolynomial p h f a).natDegree :=
    mul_card_le_natDegree_of_hasseDeriv_eval_eq_zero
      (points := points) (r := R p h) ha hvanish
  have hdegree := natDegree_auxiliaryPolynomial_lt hp hf a
  have hproduct :
      R p h * points.card < R p h * traceFiberBound p h d := by
    calc
      R p h * points.card ≤
          (auxiliaryPolynomial p h f a).natDegree := hroot
      _ < auxiliaryDegreeBound p h d := hdegree
      _ = R p h * traceFiberBound p h d :=
        auxiliaryDegreeBound_eq_R_mul_traceFiberBound p h d
  exact (Nat.mul_lt_mul_left (Nat.pow_pos hp)).mp hproduct

/-- The weak form convenient for subsequent real-valued estimates. -/
theorem card_le_traceFiberBound_of_auxiliary
    {E : Type*} [Field E] {p h d : Nat} (hp : 0 < p)
    {f : E[X]} (hf : f.natDegree ≤ d)
    (a : AuxiliaryCoefficients E p h) (ha : auxiliaryPolynomial p h f a ≠ 0)
    (points : Finset E)
    (hvanish : ∀ x ∈ points, ∀ r < R p h,
      (hasseDeriv r (auxiliaryPolynomial p h f a)).eval x = 0) :
    points.card ≤ traceFiberBound p h d :=
  (card_lt_traceFiberBound_of_auxiliary hp hf a ha points hvanish).le

end Stepanov

end Waring.Analytic
