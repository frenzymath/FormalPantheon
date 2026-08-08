import Waring.Analytic.ChenTenSingularCoefficientMultiplicativity
import Waring.Analytic.ChenTenSingularSeries
import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# Euler product for Chen's singular series

Absolute convergence and the normalized-CRT multiplicativity formula identify
Chen's singular series with the product of its prime-power local factors
[CHEN1964-EN, pp. 1565-1567, equations (39)-(41); CHEN1964-ZH, pp. 731-733].
-/

namespace Waring.Analytic

open scoped ComplexConjugate

/-- The zero-extended singular coefficient is multiplicative on all coprime
natural moduli, including the boundary pairs `(0, 1)` and `(1, 0)`. -/
theorem chenTenSingularCoefficientNat_mul {m q : Nat}
    (hcoprime : m.Coprime q) (N : Nat) :
    chenTenSingularCoefficientNat N (m * q) =
      chenTenSingularCoefficientNat N m *
        chenTenSingularCoefficientNat N q := by
  by_cases hm : m = 0
  · subst m
    have hq : q = 1 := q.coprime_zero_left.mp hcoprime
    subst q
    simp
  · by_cases hq : q = 0
    · subst q
      have hm_one : m = 1 := m.coprime_zero_right.mp hcoprime
      subst m
      simp
    · letI : NeZero m := ⟨hm⟩
      letI : NeZero q := ⟨hq⟩
      have hmq : m * q ≠ 0 := Nat.mul_ne_zero hm hq
      simp only [chenTenSingularCoefficientNat, dif_neg hm, dif_neg hq,
        dif_neg hmq]
      exact chenTenSingularCoefficient_mul hcoprime N

/-- Complex conjugation fixes the zero-extended singular coefficient. -/
theorem conj_chenTenSingularCoefficientNat (N q : Nat) :
    conj (chenTenSingularCoefficientNat N q) =
      chenTenSingularCoefficientNat N q := by
  by_cases hq : q = 0
  · subst q
    simp
  · simp [chenTenSingularCoefficientNat, hq,
      @conj_chenTenSingularCoefficient q ⟨hq⟩ N]

/-- The norms of Chen's zero-extended coefficients are summable. -/
theorem summable_norm_chenTenSingularCoefficientNat (N : Nat) :
    Summable (fun q : Nat => ‖chenTenSingularCoefficientNat N q‖) :=
  (summable_chenTenSingularCoefficientNat N).norm

/-- The coefficient series restricted to powers of one prime is summable. -/
theorem summable_chenTenSingularCoefficientNat_primePower
    (N : Nat) {p : Nat} (hp : p.Prime) :
    Summable (fun e : Nat =>
      chenTenSingularCoefficientNat N (p ^ e)) :=
  (summable_chenTenSingularCoefficientNat N).comp_injective
    (Nat.pow_right_injective hp.one_lt)

/-- The coefficient norms restricted to powers of one prime are summable. -/
theorem summable_norm_chenTenSingularCoefficientNat_primePower
    (N : Nat) {p : Nat} (hp : p.Prime) :
    Summable (fun e : Nat =>
      ‖chenTenSingularCoefficientNat N (p ^ e)‖) :=
  (summable_norm_chenTenSingularCoefficientNat N).comp_injective
    (Nat.pow_right_injective hp.one_lt)

/-- Chen's prime-power local factor `phi(p, N)`. -/
noncomputable def chenTenPrimeLocalFactor (p N : Nat) : Complex :=
  ∑' e : Nat, chenTenSingularCoefficientNat N (p ^ e)

/-- A prime-power coefficient family sums to its local factor. -/
theorem hasSum_chenTenPrimeLocalFactor (N : Nat) {p : Nat}
    (hp : p.Prime) :
    HasSum (fun e : Nat => chenTenSingularCoefficientNat N (p ^ e))
      (chenTenPrimeLocalFactor p N) :=
  (summable_chenTenSingularCoefficientNat_primePower N hp).hasSum

/-- Every prime-power local factor is fixed by complex conjugation. -/
theorem conj_chenTenPrimeLocalFactor (p N : Nat) :
    conj (chenTenPrimeLocalFactor p N) = chenTenPrimeLocalFactor p N := by
  unfold chenTenPrimeLocalFactor
  rw [Complex.conj_tsum]
  exact tsum_congr fun e => conj_chenTenSingularCoefficientNat N (p ^ e)

/-- Every prime-power local factor is real-valued. -/
theorem chenTenPrimeLocalFactor_im_eq_zero (p N : Nat) :
    (chenTenPrimeLocalFactor p N).im = 0 :=
  Complex.conj_eq_iff_im.mp (conj_chenTenPrimeLocalFactor p N)

/-- The local factors have a convergent Euler product equal to Chen's singular
series. -/
theorem hasProd_chenTenPrimeLocalFactor (N : Nat) :
    HasProd (fun p : Nat.Primes => chenTenPrimeLocalFactor p N)
      (chenTenSingularSeries N) := by
  simpa [chenTenPrimeLocalFactor, chenTenSingularSeries] using
    (EulerProduct.eulerProduct_hasProd
      (f := chenTenSingularCoefficientNat N)
      (chenTenSingularCoefficientNat_one N)
      (fun hcoprime => chenTenSingularCoefficientNat_mul hcoprime N)
      (summable_norm_chenTenSingularCoefficientNat N)
      (chenTenSingularCoefficientNat_zero N))

/-- Chen's singular series is the value of the product of its prime-power
local factors. -/
theorem tprod_chenTenPrimeLocalFactor_eq_chenTenSingularSeries (N : Nat) :
    (∏' p : Nat.Primes, chenTenPrimeLocalFactor p N) =
      chenTenSingularSeries N :=
  (hasProd_chenTenPrimeLocalFactor N).tprod_eq

end Waring.Analytic
