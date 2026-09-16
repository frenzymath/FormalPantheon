import Waring.Analytic.RestrictedTripleFiberCauchy
import Waring.Analytic.WeylQuadraticBound

/-!
# Quadratic sums grouped by restricted triple-product fibers

This file applies the fourth-difference estimate to each decoded restricted
triple and then invokes the direct product-fiber Cauchy bound.
-/

namespace Waring.Analytic

open scoped BigOperators

/-- The linear frequency depends on the first three shifts only through their
product `z`. -/
def fifthProductFrequency {q : Nat} (a : ZMod q) (z l : Nat) : ZMod q :=
  a * (120 * (z : ZMod q) * (l : ZMod q))

/-- Chen's zero-safe product majorant after the fourth difference. -/
noncomputable def fifthProductMajorant {q : Nat} [NeZero q]
    (a : ZMod q) (P z : Nat) : Real :=
  P + 2 * ∑ h ∈ Finset.range P,
    diophantineMinWeight q P (-fifthProductFrequency a z (h + 1))

/-- The norm of the quadratic sum attached to one decoded restricted triple. -/
noncomputable def restrictedQuadraticValue {q : Nat} [NeZero q]
    (a : ZMod q) (P z : Nat) (x : Sigma fun _ : Nat ↦ Nat) : Real :=
  ‖∑ y ∈ Finset.range (P - (x.2 + x.1 / x.2 + z / x.1)),
    fifthQuadraticChar a x.2 (x.1 / x.2) (z / x.1) (y + 1)‖

/-- The product-only quadratic majorant is nonnegative. -/
theorem fifthProductMajorant_nonneg {q : Nat} [NeZero q]
    (a : ZMod q) (P z : Nat) :
    0 ≤ fifthProductMajorant a P z := by
  unfold fifthProductMajorant
  exact add_nonneg (by positivity) (mul_nonneg (by norm_num)
    (Finset.sum_nonneg fun h _ ↦
      diophantineMinWeight_nonneg q P (-fifthProductFrequency a z (h + 1))))

/-- Equation (13) gives the product-only majorant for every member of a
restricted fiber. -/
theorem restrictedQuadraticValue_sq_le {q : Nat} [NeZero q]
    (a : ZMod q) (P z : Nat) (x : Sigma fun _ : Nat ↦ Nat)
    (hx : x ∈ restrictedTripleDivisorChoices P z) :
    (restrictedQuadraticValue a P z x) ^ 2 ≤
      fifthProductMajorant a P z := by
  have hproduct := restrictedTripleDivisorChoice_product hx
  have hproductZ :
      (x.2 : ZMod q) * (x.1 / x.2 : Nat) * (z / x.1 : Nat) = (z : ZMod q) := by
    have hcast := congrArg (fun t : Nat ↦ (t : ZMod q)) hproduct
    push_cast at hcast
    exact hcast
  have hfrequency (l : Nat) :
    fifthQuadraticFrequency a x.2 (x.1 / x.2) (z / x.1) l =
        fifthProductFrequency a z l := by
    unfold fifthQuadraticFrequency fifthProductFrequency
    calc
      a * (120 * (x.2 : ZMod q) * (x.1 / x.2 : Nat) *
          (z / x.1 : Nat) * (l : ZMod q)) =
          a * (120 * ((x.2 : ZMod q) * (x.1 / x.2 : Nat) *
            (z / x.1 : Nat)) * (l : ZMod q)) := by ring
      _ = a * (120 * (z : ZMod q) * (l : ZMod q)) := by rw [hproductZ]
  have hbound := norm_fifthQuadraticSum_sq_le_full a x.2
    (x.1 / x.2) (z / x.1)
    (P - (x.2 + x.1 / x.2 + z / x.1)) P (Nat.sub_le _ _)
  simp_rw [hfrequency] at hbound
  simpa only [restrictedQuadraticValue, fifthProductMajorant] using hbound

/-- The complete sum over restricted quadratic fibers is controlled by the
support-scaled second moment and the sum of product majorants. -/
theorem sq_sum_restrictedQuadraticValue_le {q : Nat} [NeZero q]
    (a : ZMod q) {P : Nat} (hP : 3 ≤ P) :
    (∑ z ∈ Finset.Icc 1 (P ^ 3 / 27),
        ∑ x ∈ restrictedTripleDivisorChoices P z,
          restrictedQuadraticValue a P z x) ^ 2 ≤
      ((81 : Real) / 16 * (P : Real) ^ 3 *
          (Real.log P + 2) ^ 8) *
        ∑ z ∈ Finset.Icc 1 (P ^ 3 / 27),
          fifthProductMajorant a P z := by
  exact sq_sum_restrictedTripleFiber_le hP
    (restrictedQuadraticValue a P) (fifthProductMajorant a P)
    (fun z _ ↦ fifthProductMajorant_nonneg a P z)
    (fun z _ x hx ↦ restrictedQuadraticValue_sq_le a P z x hx)

end Waring.Analytic
