import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.FieldTheory.Finite.Basic

/-!
# Low Hasse derivatives of Frobenius-spaced monomials

At an element of a degree-`n` finite-field extension, `x ^ (p ^ n) = x`.
Consequently a factor `X ^ (p ^ n * k)` behaves as the constant `x ^ k`
under every Hasse derivative of order below `p ^ n`.  This is the derivative
reduction used in the pure-additive Stepanov auxiliary polynomial.
-/

namespace Waring.Analytic

open Polynomial

namespace Stepanov

private theorem coeff_mul_eq_mul_coeff_zero_of_right_low_coeff_eq_zero
    {R : Type*} [CommSemiring R] {F G : R[X]} {r : Nat}
    (hG : ∀ j, 0 < j → j ≤ r → G.coeff j = 0) :
    (F * G).coeff r = F.coeff r * G.coeff 0 := by
  classical
  rw [coeff_mul, Finset.sum_eq_single (r, 0)]
  · intro ij hij hne
    have hijsum : ij.1 + ij.2 = r := Finset.mem_antidiagonal.mp hij
    have hjle : ij.2 ≤ r := by omega
    have hjpos : 0 < ij.2 := by
      by_contra hj
      have hjzero : ij.2 = 0 := Nat.eq_zero_of_not_pos hj
      have hizero : ij.1 = r := by omega
      exact hne (Prod.ext hizero hjzero)
    rw [hG ij.2 hjpos hjle, mul_zero]
  · simp

/-- Taylor expansion of a Frobenius-spaced monomial at a fixed point. -/
theorem taylor_X_pow_pow_mul
    {E : Type*} [CommRing E] {p n k : Nat} [Fact p.Prime]
    [CharP E p] (x : E)
    (hx : x ^ (p ^ n) = x) :
    taylor x (X ^ (p ^ n * k)) =
      expand E (p ^ n) ((X + C x) ^ k) := by
  rw [taylor_X_pow, pow_mul, add_pow_char_pow]
  simp only [map_pow, map_add, expand_X, expand_C]
  rw [← map_pow, hx]

/-- Positive coefficients below the Frobenius spacing vanish in the Taylor
expansion of a Frobenius-spaced monomial. -/
theorem coeff_taylor_X_pow_pow_mul_eq_zero
    {E : Type*} [CommRing E] {p n k r : Nat} [Fact p.Prime]
    [CharP E p]
    (hp : 0 < p) (x : E) (hx : x ^ (p ^ n) = x)
    (hrpos : 0 < r) (hr : r < p ^ n) :
    (taylor x (X ^ (p ^ n * k))).coeff r = 0 := by
  rw [taylor_X_pow_pow_mul x hx, coeff_expand (Nat.pow_pos hp)]
  rw [if_neg (Nat.not_dvd_of_pos_of_lt hrpos hr)]

/-- The constant Taylor coefficient of a Frobenius-spaced monomial is the
corresponding ordinary power of the fixed point. -/
theorem coeff_zero_taylor_X_pow_pow_mul
    {E : Type*} [CommRing E] {p n k : Nat} [Fact p.Prime]
    [CharP E p]
    (hp : 0 < p) (x : E) (hx : x ^ (p ^ n) = x) :
    (taylor x (X ^ (p ^ n * k))).coeff 0 = x ^ k := by
  rw [taylor_X_pow_pow_mul x hx, coeff_expand (Nat.pow_pos hp),
    if_pos (dvd_zero (p ^ n))]
  simp [coeff_zero_eq_eval_zero]

/-- Below order `p ^ n`, the Frobenius-spaced monomial is constant for Hasse
differentiation at an extension-field point. -/
theorem eval_hasseDeriv_mul_X_pow_pow_mul
    {E : Type*} [CommRing E] {p n k r : Nat} [Fact p.Prime]
    [CharP E p]
    (hp : 0 < p) (x : E) (hx : x ^ (p ^ n) = x)
    (e : E[X]) (hr : r < p ^ n) :
    (hasseDeriv r (e * X ^ (p ^ n * k))).eval x =
      (hasseDeriv r e).eval x * x ^ k := by
  rw [← taylor_coeff, taylor_mul]
  calc
    (taylor x e * taylor x (X ^ (p ^ n * k))).coeff r =
        (taylor x e).coeff r *
          (taylor x (X ^ (p ^ n * k))).coeff 0 := by
      apply coeff_mul_eq_mul_coeff_zero_of_right_low_coeff_eq_zero
      intro j hjpos hjr
      exact coeff_taylor_X_pow_pow_mul_eq_zero hp x hx hjpos
        (hjr.trans_lt hr)
    _ = (taylor x e).coeff r * x ^ k := by
      rw [coeff_zero_taylor_X_pow_pow_mul hp x hx]
    _ = (hasseDeriv r e).eval x * x ^ k := by
      rw [taylor_coeff]

/-- Taylor expansion commutes with polynomial expansion after applying the
same Frobenius power to the center. -/
theorem taylor_expand_pow
    {E : Type*} [CommRing E] {p n : Nat} [Fact p.Prime]
    [CharP E p] (x : E) (g : E[X]) :
  taylor x (expand E (p ^ n) g) =
      expand E (p ^ n) (taylor (x ^ (p ^ n)) g) := by
  simp only [taylor_apply, expand_eq_comp_X_pow, comp_assoc, X_pow_comp,
    add_comp, X_comp, C_comp]
  rw [add_pow_char_pow]
  rw [← map_pow]

/-- Positive Taylor coefficients below the expansion spacing vanish. -/
theorem coeff_taylor_expand_pow_eq_zero
    {E : Type*} [CommRing E] {p n r : Nat} [Fact p.Prime]
    [CharP E p] (hp : 0 < p) (x : E) (g : E[X])
    (hrpos : 0 < r) (hr : r < p ^ n) :
    (taylor x (expand E (p ^ n) g)).coeff r = 0 := by
  rw [taylor_expand_pow x g, coeff_expand (Nat.pow_pos hp),
    if_neg (Nat.not_dvd_of_pos_of_lt hrpos hr)]

/-- The constant Taylor coefficient of an expanded polynomial is its value
at the Frobenius power of the center. -/
theorem coeff_zero_taylor_expand_pow
    {E : Type*} [CommRing E] {p n : Nat} [Fact p.Prime]
    [CharP E p] (hp : 0 < p) (x : E) (g : E[X]) :
    (taylor x (expand E (p ^ n) g)).coeff 0 =
      g.eval (x ^ (p ^ n)) := by
  rw [taylor_expand_pow x g, coeff_expand (Nat.pow_pos hp),
    if_pos (dvd_zero (p ^ n))]
  simp

/-- An expanded factor is constant for Hasse differentiation below its
spacing. -/
theorem eval_hasseDeriv_mul_expand_pow
    {E : Type*} [CommRing E] {p n r : Nat} [Fact p.Prime]
    [CharP E p] (hp : 0 < p) (x : E) (e g : E[X])
    (hr : r < p ^ n) :
    (hasseDeriv r (e * expand E (p ^ n) g)).eval x =
      (hasseDeriv r e).eval x * g.eval (x ^ (p ^ n)) := by
  rw [← taylor_coeff, taylor_mul]
  calc
    (taylor x e * taylor x (expand E (p ^ n) g)).coeff r =
        (taylor x e).coeff r *
          (taylor x (expand E (p ^ n) g)).coeff 0 := by
      apply coeff_mul_eq_mul_coeff_zero_of_right_low_coeff_eq_zero
      intro j hjpos hjr
      exact coeff_taylor_expand_pow_eq_zero hp x g hjpos
        (hjr.trans_lt hr)
    _ = (taylor x e).coeff r * g.eval (x ^ (p ^ n)) := by
      rw [coeff_zero_taylor_expand_pow hp x g]
    _ = (hasseDeriv r e).eval x * g.eval (x ^ (p ^ n)) := by
      rw [taylor_coeff]

end Stepanov

end Waring.Analytic
