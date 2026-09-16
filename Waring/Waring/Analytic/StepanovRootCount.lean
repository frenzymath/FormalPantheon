import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Root counting for the Stepanov auxiliary polynomial

The Stepanov construction imposes the vanishing of the first `r` Hasse
derivatives of an auxiliary polynomial at every point being counted.  Taylor's
formula identifies those values with the first `r` coefficients after
translation to the point.  Hence every counted point is a root of multiplicity
at least `r`.  Summing the corresponding counts in the root multiset gives the
standard inequality

`r * card(points) <= natDegree(auxiliary polynomial)`.

The use of Hasse derivatives is essential in positive characteristic: unlike
ordinary iterated derivatives, they retain the Taylor coefficients when
factorials vanish.
-/

namespace Waring.Analytic

open Polynomial

namespace Stepanov

/-- If the first `r` Hasse derivatives of a nonzero polynomial vanish at `x`,
then `x` is a root of multiplicity at least `r`.

This statement is valid in every commutative domain and in arbitrary
characteristic. -/
theorem le_rootMultiplicity_of_hasseDeriv_eval_eq_zero
    {K : Type*} [CommRing K] [IsDomain K] {F : K[X]} {x : K} {r : Nat}
    (hF : F ≠ 0)
    (hvanish : (k : Nat) -> k < r -> (hasseDeriv k F).eval x = 0) :
    r <= F.rootMultiplicity x := by
  rw [Polynomial.rootMultiplicity_eq_natTrailingDegree]
  apply Polynomial.le_natTrailingDegree
  · exact (Polynomial.taylor_eq_zero x F).not.mpr hF
  · intro k hk
    change (Polynomial.taylor x F).coeff k = 0
    rw [Polynomial.taylor_coeff]
    exact hvanish k hk

/-- A nonzero polynomial whose first `r` Hasse derivatives vanish on a finite
set has degree at least `r` times the cardinality of that set. -/
theorem mul_card_le_natDegree_of_hasseDeriv_eval_eq_zero
    {K : Type*} [CommRing K] [IsDomain K] {F : K[X]} {points : Finset K}
    {r : Nat} (hF : F ≠ 0)
    (hvanish : (x : K) -> x ∈ points -> (k : Nat) -> k < r ->
      (hasseDeriv k F).eval x = 0) :
    r * points.card <= F.natDegree := by
  classical
  by_cases hr : r = 0
  · simp [hr]
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr
  have hmult : (x : K) -> x ∈ points -> r <= F.rootMultiplicity x := by
    intro x hx
    exact le_rootMultiplicity_of_hasseDeriv_eval_eq_zero hF
      (hvanish x hx)
  have hsubset : points <= F.roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, ← Multiset.count_pos]
    rw [Polynomial.count_roots]
    exact hrpos.trans_le (hmult x hx)
  calc
    r * points.card = ∑ x ∈ points, r := by
      simp [Nat.mul_comm]
    _ <= ∑ x ∈ points, F.rootMultiplicity x :=
      Finset.sum_le_sum hmult
    _ = ∑ x ∈ points, F.roots.count x := by
      simp only [Polynomial.count_roots]
    _ <= ∑ x ∈ F.roots.toFinset, F.roots.count x :=
      Finset.sum_le_sum_of_subset hsubset
    _ = F.roots.card := Multiset.toFinset_sum_count_eq F.roots
    _ <= F.natDegree := Polynomial.card_roots' F

-- The domain instance is kept in this characteristic-independent root lemma
-- to preserve the reviewed algebraic contract used by its consumers.
attribute [nolint unusedArguments]
  le_rootMultiplicity_of_hasseDeriv_eval_eq_zero

end Stepanov

end Waring.Analytic
