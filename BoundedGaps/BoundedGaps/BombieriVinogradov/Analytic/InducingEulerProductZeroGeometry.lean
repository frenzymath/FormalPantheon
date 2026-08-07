import BoundedGaps.BombieriVinogradov.Analytic.InducingEulerProduct

/-!
# Zero geometry of the inducing Euler product

Every zero of the finite product from SEM-506 lies on the imaginary axis.
Consequently, a zero in a closed unit ordinate window lies in the closed
radius-three disk used by SEM-508.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 110,
equation (11.2), and printed pp. 112--113. Semantic review: `SEM-509`.
-/

namespace BoundedGaps.Maynard

open Complex Metric

noncomputable section

private theorem re_eq_zero_of_inducingEulerFactor_eq_zero
    {d : ℕ} (psi : DirichletCharacter ℂ d)
    (p : ℕ) (hp : p.Prime) (s : ℂ)
    (hzero : (1 : ℂ) - psi p * (p : ℂ) ^ (-s) = 0) :
    s.re = 0 := by
  have hprod : psi p * (p : ℂ) ^ (-s) = 1 :=
    (sub_eq_zero.mp hzero).symm
  have hpsi : psi p ≠ 0 := by
    intro h
    rw [h, zero_mul] at hprod
    exact zero_ne_one hprod
  have hpUnit : IsUnit (p : ZMod d) :=
    MulChar.apply_ne_zero_iff.mp hpsi
  have hpsiNorm : ‖psi p‖ = 1 := by
    rw [psi.toUnitHom_eq_char' hpUnit]
    exact psi.unit_norm_eq_one hpUnit.unit
  have hnorm := congrArg norm hprod
  rw [norm_mul, hpsiNorm, one_mul, norm_one,
    Complex.norm_natCast_cpow_of_pos hp.pos, neg_re] at hnorm
  have hpow : (p : ℝ) ^ (-s.re) = (p : ℝ) ^ (0 : ℝ) := by
    simpa using hnorm
  have hbasePos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hbaseNeOne : (p : ℝ) ≠ 1 := by exact_mod_cast hp.ne_one
  have : -s.re = 0 :=
    (Real.rpow_right_inj hbasePos hbaseNeOne).mp hpow
  linarith

/-- Every zero of the finite inducing product lies on the imaginary axis. -/
theorem re_eq_zero_of_inducingEulerProduct_eq_zero
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {rho : ℂ}
    (hzero : inducingEulerProduct chi rho = 0) :
    rho.re = 0 := by
  rw [inducingEulerProduct, Finset.prod_eq_zero_iff] at hzero
  obtain ⟨p, hpMem, hpZero⟩ := hzero
  exact re_eq_zero_of_inducingEulerFactor_eq_zero chi.primitiveCharacter p
    (Nat.prime_of_mem_primeFactors hpMem) rho hpZero

/-- A product zero in a closed unit ordinate window lies in the closed
radius-three disk used by SEM-508. -/
theorem inducingEulerProduct_zero_mem_closedBall_radiusThree
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {rho : ℂ} (t : ℝ)
    (hzero : inducingEulerProduct chi rho = 0)
    (hheight : |rho.im - t| ≤ 1) :
    rho ∈ closedBall ((2 : ℂ) + t * I) 3 := by
  have hre : rho.re = 0 :=
    re_eq_zero_of_inducingEulerProduct_eq_zero chi hzero
  have hx : (rho.re - 2) ^ 2 ≤ (2 : ℝ) ^ 2 := by
    rw [hre]
    norm_num
  have hy : (rho.im - t) ^ 2 ≤ (1 : ℝ) ^ 2 :=
    sq_le_sq.mpr (by simpa using hheight)
  rw [mem_closedBall, Complex.dist_eq, Complex.norm_def, Real.sqrt_le_iff]
  constructor
  · norm_num
  · rw [Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_one, sub_zero, Complex.sub_im, Complex.add_im]
    norm_num
    nlinarith

end

end BoundedGaps.Maynard
