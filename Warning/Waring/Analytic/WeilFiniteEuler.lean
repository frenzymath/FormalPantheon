import Waring.Analytic.PowerSeriesRecurrence
import Waring.Analytic.WeilEulerCoefficients

/-!
# Division-free logarithmic derivatives of finite Euler products

This file packages the bounded Euler product and its division-free
logarithmic derivative.  The identity `X L' = L B` is proved directly from
the corresponding local identities, without inverting either a power series
or a natural-number coefficient.
-/

namespace Waring.Analytic

open Polynomial

namespace Weil

variable {K R : Type*} [Field K] [Fintype K] [CommRing R] {N n : Nat}

/-- The Euler product over monic irreducibles of degree at most `N`. -/
noncomputable def finiteEulerProduct
    (w : MonicIrreducibleLE K N → R) : PowerSeries R :=
  ∏ P : MonicIrreducibleLE K N,
    localEuler P.poly.natDegree (w P)

/-- The division-free logarithmic derivative series associated to the
bounded Euler product.  Its `P`-term is `deg(P) (L_P - 1)`. -/
noncomputable def finiteEulerLogDerivative
    (w : MonicIrreducibleLE K N → R) : PowerSeries R :=
  ∑ P : MonicIrreducibleLE K N,
    PowerSeries.C (P.poly.natDegree : R) *
      (localEuler P.poly.natDegree (w P) - 1)

private theorem X_mul_derivativeFun_prod_localEuler
    {I : Type*} [Fintype I] (e : I → Nat) (he : ∀ i, e i ≠ 0)
    (z : I → R) :
    PowerSeries.X * PowerSeries.derivativeFun
        (∏ i : I, localEuler (e i) (z i)) =
      (∏ i : I, localEuler (e i) (z i)) *
        (∑ i : I, PowerSeries.C (e i : R) *
          (localEuler (e i) (z i) - 1)) := by
  classical
  let s : Finset I := Finset.univ
  change PowerSeries.X * PowerSeries.derivativeFun
      (∏ i ∈ s, localEuler (e i) (z i)) =
    (∏ i ∈ s, localEuler (e i) (z i)) *
      (∑ i ∈ s, PowerSeries.C (e i : R) *
        (localEuler (e i) (z i) - 1))
  induction s using Finset.induction_on with
  | empty => simp [PowerSeries.derivativeFun_one]
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        PowerSeries.derivativeFun_mul]
      simp only [smul_eq_mul]
      have hlocal := X_mul_derivativeFun_localEuler (z a) (he a)
      linear_combination
        localEuler (e a) (z a) * ih +
          (∏ i ∈ s, localEuler (e i) (z i)) * hlocal

/-- The finite Euler product satisfies its division-free logarithmic
derivative identity `X L' = L B`. -/
theorem X_mul_derivativeFun_finiteEulerProduct
    (w : MonicIrreducibleLE K N → R) :
    PowerSeries.X *
        PowerSeries.derivativeFun (finiteEulerProduct w) =
      finiteEulerProduct w * finiteEulerLogDerivative w := by
  rw [finiteEulerProduct, finiteEulerLogDerivative]
  exact X_mul_derivativeFun_prod_localEuler
    (fun P : MonicIrreducibleLE K N ↦ P.poly.natDegree)
    (fun P ↦ P.natDegree_pos.ne') w

/-- A positive-degree coefficient of the division-free logarithmic
derivative is the expected sum over irreducibles whose degrees divide the
coefficient index. -/
theorem coeff_finiteEulerLogDerivative (hn : n ≠ 0)
    (w : MonicIrreducibleLE K N → R) :
    PowerSeries.coeff n (finiteEulerLogDerivative w) =
      ∑ P : MonicIrreducibleLE K N,
        if P.poly.natDegree ∣ n then
          (P.poly.natDegree : R) *
            w P ^ (n / P.poly.natDegree)
        else 0 := by
  classical
  rw [finiteEulerLogDerivative, map_sum]
  apply Finset.sum_congr rfl
  intro P hP
  rw [PowerSeries.coeff_C_mul, map_sub,
    coeff_localEuler (w P) P.natDegree_pos.ne',
    PowerSeries.coeff_one, if_neg hn]
  simp only [sub_zero]
  split_ifs <;> simp

/-- The division-free logarithmic derivative has zero constant
coefficient. -/
theorem constantCoeff_finiteEulerLogDerivative
    (w : MonicIrreducibleLE K N → R) :
    PowerSeries.constantCoeff (finiteEulerLogDerivative w) = 0 := by
  classical
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    finiteEulerLogDerivative, map_sum]
  apply Finset.sum_eq_zero
  intro P hP
  rw [PowerSeries.coeff_C_mul, map_sub,
    coeff_localEuler (w P) P.natDegree_pos.ne',
    PowerSeries.coeff_one]
  simp

/-- The coefficient recurrence supplied by the finite Euler product, with
only positive-degree coefficients of its logarithmic derivative present. -/
theorem nat_mul_coeff_finiteEulerProduct_eq_sum_positive
    (w : MonicIrreducibleLE K N → R) (n : Nat) :
    (n : R) * PowerSeries.coeff n (finiteEulerProduct w) =
      ∑ i ∈ Finset.range n,
        PowerSeries.coeff (n - (i + 1)) (finiteEulerProduct w) *
          PowerSeries.coeff (i + 1) (finiteEulerLogDerivative w) := by
  exact nat_mul_coeff_eq_sum_positive_of_X_mul_derivativeFun_eq_mul
    (X_mul_derivativeFun_finiteEulerProduct w)
    (constantCoeff_finiteEulerLogDerivative w) n

end Weil

end Waring.Analytic
