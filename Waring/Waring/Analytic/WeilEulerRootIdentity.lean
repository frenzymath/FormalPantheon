import Waring.Analytic.WeilReciprocalRoots

/-!
# Euler coefficients as reciprocal-root power sums

The bounded Euler product and the Artin coefficient polynomial have the same
coefficients through the Euler cutoff.  Their division-free logarithmic
derivative identities therefore have the same coefficients through that
cutoff.  This identifies the irreducible-polynomial sum with the negative
power sum of the reciprocal roots of the fixed Artin polynomial.
-/

namespace Waring.Analytic

open Polynomial PowerSeries
open scoped BigOperators PowerSeries

namespace Weil

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- Through the cutoff `N`, the bounded Euler product has exactly the
coefficients of the fixed Artin coefficient polynomial. -/
theorem coeff_finiteEulerProduct_eq_coeff_artinLPolynomial
    (character : AddChar K Complex) (hcharacter : character ≠ 1)
    (b : Fin 5 → K) {N d j : Nat}
    (hdpos : 0 < d) (hd5 : d ≤ 5)
    (hbtop : b ⟨d - 1, by omega⟩ ≠ 0)
    (hb : ∀ i : Fin 5, d < i.val + 1 → b i = 0)
    (hdcast : (d : K) ≠ 0) (hjN : j ≤ N) :
    PowerSeries.coeff j
        (finiteEulerProduct
          (fun P : MonicIrreducibleLE K N ↦
            formalRootWeight character b P.poly)) =
      PowerSeries.coeff j
        (artinLPolynomial character b d : PowerSeries Complex) := by
  by_cases hjd : j < d
  · rw [finiteEulerProduct,
      coeff_finiteEulerProduct_formalRootWeight_eq_sum_monic hjN,
      Polynomial.coeff_coe, coeff_artinLPolynomial, if_pos hjd]
    rfl
  · have hdj : d ≤ j := Nat.le_of_not_gt hjd
    rw [finiteEulerProduct,
      coeff_finiteEulerProduct_formalRootWeight_eq_zero hjN character
        hcharacter b hdpos hd5 hdj hbtop hb hdcast,
      Polynomial.coeff_coe, coeff_artinLPolynomial, if_neg hjd]

/-- A bounded Euler product of formal-root weights has constant coefficient
one. -/
theorem coeff_zero_finiteEulerProduct_formalRootWeight
    (character : AddChar K Complex) (b : Fin 5 → K) {N : Nat} :
    PowerSeries.coeff 0
        (finiteEulerProduct
          (fun P : MonicIrreducibleLE K N ↦
            formalRootWeight character b P.poly)) = 1 := by
  rw [finiteEulerProduct,
    coeff_finiteEulerProduct_formalRootWeight_eq_sum_monic (Nat.zero_le N)]
  exact monicFormalRootWeightSum_zero character b

/-- The logarithmic derivative coefficient of the bounded Euler product is
the negative power sum of the reciprocal roots. -/
theorem coeff_finiteEulerLogDerivative_formalRootWeight_eq_neg_powerSum
    (character : AddChar K Complex) (hcharacter : character ≠ 1)
    (b : Fin 5 → K) {N d n : Nat}
    (hdpos : 0 < d) (hd5 : d ≤ 5)
    (hbtop : b ⟨d - 1, by omega⟩ ≠ 0)
    (hb : ∀ i : Fin 5, d < i.val + 1 → b i = 0)
    (hdcast : (d : K) ≠ 0) (hnN : n ≤ N) (hn : n ≠ 0) :
    PowerSeries.coeff n
        (finiteEulerLogDerivative
          (fun P : MonicIrreducibleLE K N ↦
            formalRootWeight character b P.poly)) =
      -((artinLPolynomial character b d).reverse.roots.map
        (fun a ↦ a ^ n)).sum := by
  let w : MonicIrreducibleLE K N → Complex :=
    fun P ↦ formalRootWeight character b P.poly
  calc
    PowerSeries.coeff n (finiteEulerLogDerivative w) =
        PowerSeries.coeff n (reciprocalRootLogDerivative
          (artinLPolynomial character b d).reverse.roots) := by
      exact coeff_logDerivative_eq_of_coeff_eq_up_to
        (X_mul_derivativeFun_finiteEulerProduct w)
        (X_mul_derivativeFun_artinLPolynomial character b hdpos)
        (constantCoeff_finiteEulerLogDerivative w)
        (constantCoeff_reciprocalRootLogDerivative _)
        (coeff_zero_finiteEulerProduct_formalRootWeight character b)
        (fun j hj ↦
          coeff_finiteEulerProduct_eq_coeff_artinLPolynomial
            character hcharacter b hdpos hd5 hbtop hb hdcast hj)
        hnN
    _ = -((artinLPolynomial character b d).reverse.roots.map
        (fun a ↦ a ^ n)).sum :=
      coeff_reciprocalRootLogDerivative _ hn

/-- Explicit Euler form of the reciprocal-root power-sum identity. -/
theorem irreducible_sum_eq_neg_artinRootPowerSum
    (character : AddChar K Complex) (hcharacter : character ≠ 1)
    (b : Fin 5 → K) {N d n : Nat}
    (hdpos : 0 < d) (hd5 : d ≤ 5)
    (hbtop : b ⟨d - 1, by omega⟩ ≠ 0)
    (hb : ∀ i : Fin 5, d < i.val + 1 → b i = 0)
    (hdcast : (d : K) ≠ 0) (hnN : n ≤ N) (hn : n ≠ 0) :
    (∑ P : MonicIrreducibleLE K N,
      if P.poly.natDegree ∣ n then
        (P.poly.natDegree : Complex) *
          formalRootWeight character b P.poly ^
            (n / P.poly.natDegree)
      else 0) =
      -((artinLPolynomial character b d).reverse.roots.map
        (fun a ↦ a ^ n)).sum := by
  rw [← coeff_finiteEulerLogDerivative hn]
  exact coeff_finiteEulerLogDerivative_formalRootWeight_eq_neg_powerSum
    character hcharacter b hdpos hd5 hbtop hb hdcast hnN hn

end Weil

end Waring.Analytic
