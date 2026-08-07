import BoundedGaps.BombieriVinogradov.Analytic.InducingEulerProduct
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.JensenFormula

/-!
# Local divisor mass of the inducing Euler product

This file applies pinned Mathlib's Jensen inequality directly to the finite
Euler product from SEM-506. After the separately reviewed factor-zero geometry
bridge, the resulting radius-three divisor mass will control the additional
imprimitive zeros near a later contour height, with multiplicity.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 110,
equation (11.2), and printed pp. 112--113. The exact Euclidean-disk bound and
constant are project-derived. Semantic review: `SEM-507`.
-/

namespace BoundedGaps.Maynard

open Complex Metric

noncomputable section

private lemma three_fourths_le_norm_inducingEulerFactor_center
    {d : ℕ} (psi : DirichletCharacter ℂ d)
    (p : ℕ) (hp : p.Prime) (t : ℝ) :
    (3 / 4 : ℝ) ≤
      ‖(1 : ℂ) - psi p * (p : ℂ) ^
        (-((2 : ℂ) + t * I))‖ := by
  let w : ℂ := psi p * (p : ℂ) ^ (-((2 : ℂ) + t * I))
  change (3 / 4 : ℝ) ≤ ‖(1 : ℂ) - w‖
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpow : (p : ℝ) ^ (-2 : ℝ) ≤ (1 / 4 : ℝ) := by
    calc
      (p : ℝ) ^ (-2 : ℝ) ≤ (2 : ℝ) ^ (-2 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by norm_num)
      _ = (1 / 4 : ℝ) := by
        rw [Real.rpow_neg (by norm_num), Real.rpow_two]
        norm_num
  have hterm : ‖w‖ ≤ (1 / 4 : ℝ) := by
    dsimp only [w]
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp.pos, neg_re]
    calc
      ‖psi p‖ * (p : ℝ) ^ (-((2 : ℂ) + t * I).re) ≤
          1 * (p : ℝ) ^ (-((2 : ℂ) + t * I).re) :=
        mul_le_mul_of_nonneg_right (psi.norm_le_one p)
          (Real.rpow_nonneg (Nat.cast_nonneg p) _)
      _ = (p : ℝ) ^ (-2 : ℝ) := by simp
      _ ≤ (1 / 4 : ℝ) := hpow
  have hreverse : (1 : ℝ) - ‖w‖ ≤ ‖(1 : ℂ) - w‖ := by
    simpa using norm_sub_norm_le (1 : ℂ) w
  linarith

private lemma norm_inducingEulerFactor_sphere_le_cube_mul_center
    {d : ℕ} (psi : DirichletCharacter ℂ d)
    (p : ℕ) (hp : p.Prime) (t : ℝ) {z : ℂ}
    (hz : z ∈ sphere ((2 : ℂ) + t * I) 4) :
    ‖(1 : ℂ) - psi p * (p : ℂ) ^ (-z)‖ ≤
      (p : ℝ) ^ 3 *
        ‖(1 : ℂ) - psi p * (p : ℂ) ^
          (-((2 : ℂ) + t * I))‖ := by
  let c : ℂ := (2 : ℂ) + t * I
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : (1 : ℝ) ≤ p := one_le_two.trans hp2
  have hreAbs : |z.re - 2| ≤ 4 := by
    calc
      |z.re - 2| = |(z - c).re| := by simp [c]
      _ ≤ ‖z - c‖ := Complex.abs_re_le_norm _
      _ = dist z c := by rw [Complex.dist_eq]
      _ = 4 := mem_sphere.mp hz
  have hzre : -2 ≤ z.re := by
    have hneg := neg_abs_le (z.re - 2)
    linarith
  have hpow : (p : ℝ) ^ (-z.re) ≤ (p : ℝ) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  have hterm : ‖psi p * (p : ℂ) ^ (-z)‖ ≤ (p : ℝ) ^ 2 := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp.pos, neg_re]
    calc
      ‖psi p‖ * (p : ℝ) ^ (-z.re) ≤
          1 * (p : ℝ) ^ (-z.re) :=
        mul_le_mul_of_nonneg_right (psi.norm_le_one p)
          (Real.rpow_nonneg (Nat.cast_nonneg p) _)
      _ ≤ (p : ℝ) ^ (2 : ℝ) := by simpa using hpow
      _ = (p : ℝ) ^ 2 := Real.rpow_two _
  have hpSq4 : (4 : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
  have hpoly : (1 : ℝ) + (p : ℝ) ^ 2 ≤
      (3 / 4 : ℝ) * (p : ℝ) ^ 3 := by
    calc
      (1 : ℝ) + (p : ℝ) ^ 2 ≤ (5 / 4 : ℝ) * (p : ℝ) ^ 2 := by
        nlinarith
      _ ≤ ((3 / 4 : ℝ) * (p : ℝ)) * (p : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)
      _ = (3 / 4 : ℝ) * (p : ℝ) ^ 3 := by ring
  have hcenter := three_fourths_le_norm_inducingEulerFactor_center
    psi p hp t
  calc
    ‖(1 : ℂ) - psi p * (p : ℂ) ^ (-z)‖ ≤
        ‖(1 : ℂ)‖ + ‖psi p * (p : ℂ) ^ (-z)‖ := norm_sub_le _ _
    _ ≤ (1 : ℝ) + (p : ℝ) ^ 2 := by
      norm_num
      simpa [norm_mul] using hterm
    _ ≤ (3 / 4 : ℝ) * (p : ℝ) ^ 3 := hpoly
    _ ≤ (p : ℝ) ^ 3 *
        ‖(1 : ℂ) - psi p * (p : ℂ) ^
          (-((2 : ℂ) + t * I))‖ := by
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_left hcenter (pow_nonneg (Nat.cast_nonneg p) 3)

/-- The complete divisor mass of the inducing finite Euler product in the
radius-three disk has an explicit modulus-logarithmic bound. -/
theorem finsum_divisor_inducingEulerProduct_radiusThree_le
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (t : ℝ) :
    ((∑ᶠ rho : ℂ,
        MeromorphicOn.divisor (inducingEulerProduct chi)
          (closedBall ((2 : ℂ) + t * I) 3) rho : ℤ) : ℝ) ≤
      12 * Real.log (q : ℝ) := by
  let c : ℂ := (2 : ℂ) + t * I
  let Q : ℝ := ∏ p ∈ q.primeFactors, (p : ℝ) ^ 3
  let M : ℝ := Q * ‖inducingEulerProduct chi c‖
  have hc : inducingEulerProduct chi c ≠ 0 := by
    apply inducingEulerProduct_ne_zero_of_re_pos chi
    simp [c]
  have hM_eq : M = ∏ p ∈ q.primeFactors,
      (p : ℝ) ^ 3 *
        ‖(1 : ℂ) - chi.primitiveCharacter p *
          (p : ℂ) ^ (-c)‖ := by
    simp only [M, Q, inducingEulerProduct, norm_prod]
    rw [Finset.prod_mul_distrib]
  have hM : 1 ≤ M := by
    rw [hM_eq]
    apply Finset.one_le_prod
    intro p hp
    have hpPrime := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpPrime.two_le
    have hp3 : (8 : ℝ) ≤ (p : ℝ) ^ 3 := by
      have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hp2 3
      norm_num at h ⊢
      exact h
    have hcenter : (3 / 4 : ℝ) ≤
        ‖(1 : ℂ) - chi.primitiveCharacter p *
          (p : ℂ) ^ (-c)‖ := by
      simpa [c] using three_fourths_le_norm_inducingEulerFactor_center
        chi.primitiveCharacter p hpPrime t
    have hmul := mul_le_mul hp3 hcenter
      (by norm_num : (0 : ℝ) ≤ 3 / 4) (by positivity : (0 : ℝ) ≤ (p : ℝ) ^ 3)
    nlinarith
  have hf : AnalyticOnNhd ℂ (inducingEulerProduct chi)
      (closedBall c |(4 : ℝ)|) :=
    fun z _ => (differentiable_inducingEulerProduct chi).analyticAt z
  have hbound : ∀ z ∈ sphere c |(4 : ℝ)|,
      ‖inducingEulerProduct chi z‖ ≤ M := by
    intro z hz
    rw [hM_eq]
    simp only [inducingEulerProduct, norm_prod]
    apply Finset.prod_le_prod
    · intro p hp
      exact norm_nonneg _
    · intro p hp
      exact norm_inducingEulerFactor_sphere_le_cube_mul_center
        chi.primitiveCharacter p (Nat.prime_of_mem_primeFactors hp) t
          (by simpa [c] using hz)
  have hjensen := hf.sum_divisor_le
    (r := (3 : ℝ)) (R := (4 : ℝ)) (M := M)
    (by norm_num) (by norm_num) hM hc hbound
  rw [show |(3 : ℝ)| = 3 by norm_num] at hjensen
  norm_num at hjensen
  have hratio : M / ‖inducingEulerProduct chi c‖ = Q := by
    dsimp [M]
    exact mul_div_cancel_right₀ Q (norm_ne_zero_iff.mpr hc)
  let S : ℝ := ∑ p ∈ q.primeFactors, Real.log p
  have hSnonneg : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun p hp =>
      Real.log_nonneg (by exact_mod_cast
        (Nat.prime_of_mem_primeFactors hp).one_le)
  have hlogQ : Real.log Q = 3 * S := by
    dsimp [Q, S]
    rw [Finset.prod_pow, Real.log_pow, Real.log_prod]
    · ring
    · intro p hp
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hSle : S ≤ Real.log (q : ℝ) := by
    let P : ℕ := ∏ p ∈ q.primeFactors, p
    have hPpos : 0 < P := by
      dsimp [P]
      exact Finset.prod_pos fun p hp =>
        (Nat.prime_of_mem_primeFactors hp).pos
    have hPle : P ≤ q :=
      Nat.le_of_dvd (NeZero.pos q)
        (by simpa [P] using Nat.prod_primeFactors_dvd q)
    have hcast : (P : ℝ) =
        ∏ p ∈ q.primeFactors, (p : ℝ) := by
      simp [P]
    have hlogProd :
        Real.log (∏ p ∈ q.primeFactors, (p : ℝ)) = S := by
      dsimp [S]
      rw [Real.log_prod]
      intro p hp
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    rw [← hlogProd, ← hcast]
    exact Real.log_le_log (by exact_mod_cast hPpos)
      (by exact_mod_cast hPle)
  have hlogQnonneg : 0 ≤ Real.log Q := by
    rw [hlogQ]
    positivity
  have hlog43 : (1 / 4 : ℝ) < Real.log ((4 : ℝ) / 3) := by
    rw [Real.log_div (by norm_num : (4 : ℝ) ≠ 0)
      (by norm_num : (3 : ℝ) ≠ 0), Real.log_four_eq]
    nlinarith [Real.log_two_gt_d9, Real.log_three_lt_d9]
  have hquot :
      Real.log Q / Real.log ((4 : ℝ) / 3) ≤ 4 * Real.log Q := by
    apply (div_le_iff₀ (lt_trans (by norm_num) hlog43)).2
    nlinarith
  calc
    ((∑ᶠ rho : ℂ,
        MeromorphicOn.divisor (inducingEulerProduct chi)
          (closedBall ((2 : ℂ) + t * I) 3) rho : ℤ) : ℝ) ≤
        Real.log (M / ‖inducingEulerProduct chi c‖) /
          Real.log ((4 : ℝ) / 3) := by
      simpa [c] using hjensen
    _ = Real.log Q / Real.log ((4 : ℝ) / 3) := by rw [hratio]
    _ ≤ 4 * Real.log Q := hquot
    _ = 12 * S := by rw [hlogQ]; ring
    _ ≤ 12 * Real.log (q : ℝ) := by linarith

end

end BoundedGaps.Maynard
