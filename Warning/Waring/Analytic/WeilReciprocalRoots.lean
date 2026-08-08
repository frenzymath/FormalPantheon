import Waring.Analytic.WeilArtinPolynomial
import Waring.Analytic.WeilFiniteEuler

/-!
# Logarithmic derivatives and reciprocal-root power sums

For a multiset `s` of complex numbers, this file packages the product
`prod (1 - a X)` and proves its division-free logarithmic derivative
identity.  The positive-degree coefficients of that logarithmic derivative
are exactly the negatives of the power sums of `s`, with multiplicity.
-/

namespace Waring.Analytic

open PowerSeries
open scoped BigOperators PowerSeries

namespace Weil

/-- One reciprocal-root factor `1 - a X`. -/
noncomputable def reciprocalRootFactor (a : Complex) : PowerSeries Complex :=
  1 - PowerSeries.C a * PowerSeries.X

/-- The local logarithmic derivative term
`-a X / (1 - a X)`. -/
noncomputable def reciprocalRootLogTerm (a : Complex) : PowerSeries Complex :=
  PowerSeries.C (-a) * PowerSeries.X * localEuler 1 a

/-- The product of the reciprocal-root factors, with multiplicity. -/
noncomputable def reciprocalRootProduct
    (s : Multiset Complex) : PowerSeries Complex :=
  (s.map reciprocalRootFactor).prod

/-- The sum of the local reciprocal-root logarithmic derivatives. -/
noncomputable def reciprocalRootLogDerivative
    (s : Multiset Complex) : PowerSeries Complex :=
  (s.map reciprocalRootLogTerm).sum

/-- Prepending a reciprocal root factors the product by its local factor. -/
@[simp]
theorem reciprocalRootProduct_cons (a : Complex) (s : Multiset Complex) :
    reciprocalRootProduct (a ::ₘ s) =
      reciprocalRootFactor a * reciprocalRootProduct s := by
  simp [reciprocalRootProduct]

/-- Prepending a reciprocal root adds its local logarithmic term. -/
@[simp]
theorem reciprocalRootLogDerivative_cons
    (a : Complex) (s : Multiset Complex) :
    reciprocalRootLogDerivative (a ::ₘ s) =
      reciprocalRootLogTerm a + reciprocalRootLogDerivative s := by
  simp [reciprocalRootLogDerivative]

/-- Division-free logarithmic derivative identity for one reciprocal-root
factor. -/
theorem X_mul_derivativeFun_reciprocalRootFactor (a : Complex) :
    PowerSeries.X *
        PowerSeries.derivativeFun (reciprocalRootFactor a) =
      reciprocalRootFactor a * reciprocalRootLogTerm a := by
  have hinverse : localEuler 1 a * reciprocalRootFactor a = 1 := by
    simpa only [reciprocalRootFactor, pow_one] using
      (localEuler_mul_one_sub (R := Complex) a (e := 1) one_ne_zero)
  have hderivative :
      PowerSeries.derivativeFun (reciprocalRootFactor a) =
        PowerSeries.C (-a) := by
    change PowerSeries.derivative Complex
      (1 - PowerSeries.C a * PowerSeries.X) = _
    rw [map_sub, ← map_one (PowerSeries.C (R := Complex)),
      PowerSeries.derivative_C, Derivation.leibniz,
      PowerSeries.derivative_C, PowerSeries.derivative_X]
    simp only [smul_eq_mul, mul_zero, add_zero, mul_one, zero_sub, map_neg]
  rw [hderivative]
  calc
    PowerSeries.X * PowerSeries.C (-a) =
        PowerSeries.C (-a) * PowerSeries.X := mul_comm _ _
    _ = PowerSeries.C (-a) * PowerSeries.X *
        (localEuler 1 a * reciprocalRootFactor a) := by
      rw [hinverse, mul_one]
    _ = reciprocalRootFactor a * reciprocalRootLogTerm a := by
      simp only [reciprocalRootLogTerm]
      ac_rfl

/-- A positive-degree coefficient of one local root term is `-a^n`. -/
theorem coeff_reciprocalRootLogTerm (a : Complex) {n : Nat}
    (hn : n ≠ 0) :
    PowerSeries.coeff n (reciprocalRootLogTerm a) = -(a ^ n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [reciprocalRootLogTerm]
  rw [show PowerSeries.C (-a) * PowerSeries.X * localEuler 1 a =
      PowerSeries.C (-a) * (PowerSeries.X * localEuler 1 a) by
        rw [mul_assoc]]
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
    coeff_localEuler a one_ne_zero, if_pos (one_dvd k)]
  simp only [Nat.div_one]
  rw [pow_succ]
  ring

/-- The reciprocal-root product satisfies `X A' = A C`. -/
theorem X_mul_derivativeFun_reciprocalRootProduct
    (s : Multiset Complex) :
    PowerSeries.X * PowerSeries.derivativeFun (reciprocalRootProduct s) =
      reciprocalRootProduct s * reciprocalRootLogDerivative s := by
  induction s using Multiset.induction_on with
  | empty =>
      simp [reciprocalRootProduct, reciprocalRootLogDerivative,
        PowerSeries.derivativeFun_one]
  | cons a s ih =>
      rw [reciprocalRootProduct_cons,
        reciprocalRootLogDerivative_cons]
      rw [PowerSeries.derivativeFun_mul]
      simp only [smul_eq_mul]
      calc
        PowerSeries.X *
            (reciprocalRootFactor a *
                PowerSeries.derivativeFun (reciprocalRootProduct s) +
              reciprocalRootProduct s *
                PowerSeries.derivativeFun (reciprocalRootFactor a)) =
            reciprocalRootFactor a *
                (PowerSeries.X *
                  PowerSeries.derivativeFun (reciprocalRootProduct s)) +
              reciprocalRootProduct s *
                (PowerSeries.X *
                  PowerSeries.derivativeFun (reciprocalRootFactor a)) := by
          rw [mul_add]
          congr 1 <;> ac_rfl
        _ = reciprocalRootFactor a *
              (reciprocalRootProduct s * reciprocalRootLogDerivative s) +
            reciprocalRootProduct s *
              (reciprocalRootFactor a * reciprocalRootLogTerm a) := by
          rw [ih, X_mul_derivativeFun_reciprocalRootFactor]
        _ = reciprocalRootFactor a * reciprocalRootProduct s *
            (reciprocalRootLogTerm a + reciprocalRootLogDerivative s) := by
          rw [mul_add]
          ac_rfl

/-- Positive-degree coefficients of the root logarithmic derivative are the
negative power sums of the reciprocal roots. -/
theorem coeff_reciprocalRootLogDerivative
    (s : Multiset Complex) {n : Nat} (hn : n ≠ 0) :
    PowerSeries.coeff n (reciprocalRootLogDerivative s) =
      -(s.map (fun a ↦ a ^ n)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [reciprocalRootLogDerivative]
  | cons a s ih =>
      rw [reciprocalRootLogDerivative_cons, Multiset.map_cons,
        Multiset.sum_cons]
      change PowerSeries.coeff n
          (reciprocalRootLogTerm a + reciprocalRootLogDerivative s) =
        -(a ^ n + (s.map (fun z ↦ z ^ n)).sum)
      rw [map_add, coeff_reciprocalRootLogTerm a hn, ih]
      rw [neg_add]

/-- The reciprocal-root logarithmic derivative has zero constant
coefficient. -/
theorem constantCoeff_reciprocalRootLogDerivative
    (s : Multiset Complex) :
    PowerSeries.constantCoeff (reciprocalRootLogDerivative s) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  induction s using Multiset.induction_on with
  | empty => simp [reciprocalRootLogDerivative]
  | cons a s ih =>
      rw [reciprocalRootLogDerivative_cons, map_add, ih, add_zero,
        reciprocalRootLogTerm]
      rw [show PowerSeries.C (-a) * PowerSeries.X * localEuler 1 a =
          PowerSeries.C (-a) * (PowerSeries.X * localEuler 1 a) by
        rw [mul_assoc], PowerSeries.coeff_C_mul,
        PowerSeries.coeff_zero_X_mul, mul_zero]

/-- The Artin coefficient polynomial, viewed as a power series, is its
reciprocal-root product. -/
theorem coe_artinLPolynomial_eq_reciprocalRootProduct
    {K : Type*} [Field K] [Fintype K]
    (character : AddChar K Complex) (b : Fin 5 → K) {d : Nat}
    (hdpos : 0 < d) :
    (artinLPolynomial character b d : PowerSeries Complex) =
      reciprocalRootProduct
        (artinLPolynomial character b d).reverse.roots := by
  let s := (artinLPolynomial character b d).reverse.roots
  calc
    (artinLPolynomial character b d : PowerSeries Complex) =
        (((s.map
          (fun a ↦ 1 - Polynomial.C a * Polynomial.X)).prod :
            Polynomial Complex) : PowerSeries Complex) :=
      congrArg (fun F : Polynomial Complex ↦ (F : PowerSeries Complex))
        (artinLPolynomial_eq_prod_roots character b hdpos)
    _ = (s.map
          (fun a ↦ ((1 - Polynomial.C a * Polynomial.X :
            Polynomial Complex) : PowerSeries Complex))).prod := by
      simpa only [Polynomial.coeToPowerSeries.ringHom_apply,
        Multiset.map_map, Function.comp_apply] using
        (map_multiset_prod Polynomial.coeToPowerSeries.ringHom
          (s.map (fun a ↦ 1 - Polynomial.C a * Polynomial.X)))
    _ = reciprocalRootProduct s := by
      simp [reciprocalRootProduct, reciprocalRootFactor]

/-- The Artin coefficient polynomial satisfies the reciprocal-root
logarithmic derivative identity. -/
theorem X_mul_derivativeFun_artinLPolynomial
    {K : Type*} [Field K] [Fintype K]
    (character : AddChar K Complex) (b : Fin 5 → K) {d : Nat}
    (hdpos : 0 < d) :
    PowerSeries.X * PowerSeries.derivativeFun
        (artinLPolynomial character b d : PowerSeries Complex) =
      (artinLPolynomial character b d : PowerSeries Complex) *
        reciprocalRootLogDerivative
          (artinLPolynomial character b d).reverse.roots := by
  rw [coe_artinLPolynomial_eq_reciprocalRootProduct character b hdpos]
  exact X_mul_derivativeFun_reciprocalRootProduct _

end Weil

end Waring.Analytic
