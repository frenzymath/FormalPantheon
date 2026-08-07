import BoundedGaps.BombieriVinogradov.Analytic.PrimitiveFunctionalEquation
import BoundedGaps.BombieriVinogradov.Analytic.PrimitiveLFunctionSelectedSubdivisor

/-!
# Primitive Dirichlet L-function nontrivial-zero selections

This file identifies primitive completed zeros with ordinary L-function zeros
in the open critical strip, then embeds every multiplicity-bounded local-height
selection into the ordinary radius-six subdivisor interface from SEM-480.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 111--114,
equation (11.3), Theorem 11.1, and Lemma 11.4, and printed pp. 119--120,
Lemma 12.2. Semantic review: `SEM-481`.
-/

namespace BoundedGaps.Maynard

open Complex Metric

noncomputable section

/-- A source-level nontrivial zero for a primitive Dirichlet L-function of
modulus greater than one. Mathlib's completed function differs from the
source normalization by a nowhere-zero power of the modulus. -/
def IsPrimitiveNontrivialLFunctionZero
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (rho : ℂ) : Prop :=
  1 < q ∧ chi.IsPrimitive ∧
    DirichletCharacter.completedLFunction chi rho = 0

private lemma gammaFactor_ne_zero_of_re_pos
    {q : ℕ} (chi : DirichletCharacter ℂ q) {rho : ℂ}
    (hrho : 0 < rho.re) :
    DirichletCharacter.gammaFactor chi rho ≠ 0 := by
  rcases chi.even_or_odd with heven | hodd
  · rw [heven.gammaFactor_def]
    exact Gammaℝ_ne_zero_of_re_pos hrho
  · rw [hodd.gammaFactor_def]
    exact Gammaℝ_ne_zero_of_re_pos (by simp; linarith)

/-- A primitive completed zero of modulus greater than one is an ordinary
L-function zero. The division-form Mathlib identity remains valid at Gamma
poles. -/
theorem IsPrimitiveNontrivialLFunctionZero.LFunction_eq_zero
    {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q} {rho : ℂ}
    (hrho : IsPrimitiveNontrivialLFunctionZero chi rho) :
    DirichletCharacter.LFunction chi rho = 0 := by
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor chi rho
    (.inr (Nat.ne_of_gt hrho.1)), hrho.2.2, zero_div]

/-- A primitive nontrivial L-function zero lies strictly to the right of the
line `Re(s)=0`. -/
theorem IsPrimitiveNontrivialLFunctionZero.re_pos
    {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q} {rho : ℂ}
    (hrho : IsPrimitiveNontrivialLFunctionZero chi rho) :
    0 < rho.re := by
  by_contra hrhoRe
  have hchi_ne : chi ≠ 1 :=
    character_ne_one_of_isPrimitive hrho.1 chi hrho.2.1
  have hq0 : (q : ℂ) ≠ 0 := by
    exact_mod_cast NeZero.ne q
  have hroot : DirichletCharacter.rootNumber chi ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [norm_rootNumber_of_isPrimitive chi hrho.2.1]
    exact one_ne_zero
  have hfun := hrho.2.1.completedLFunction_one_sub (1 - rho)
  have hinvzero :
      DirichletCharacter.completedLFunction chi⁻¹ (1 - rho) = 0 := by
    rw [show 1 - (1 - rho) = rho by ring] at hfun
    rw [show 1 - rho - 1 / 2 = 1 / 2 - rho by ring] at hfun
    have hpow : (q : ℂ) ^ ((1 / 2 : ℂ) - rho) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (.inl hq0)
    exact (mul_eq_zero.mp (hfun.symm.trans hrho.2.2)).resolve_left
      (mul_ne_zero hpow hroot)
  have hLzero : DirichletCharacter.LFunction chi⁻¹ (1 - rho) = 0 := by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor chi⁻¹
      (1 - rho) (.inr (Nat.ne_of_gt hrho.1)), hinvzero, zero_div]
  exact ((chi⁻¹).LFunction_ne_zero_of_one_le_re
    (.inl (inv_ne_one.mpr hchi_ne)) (by simp; linarith)) hLzero

/-- A primitive nontrivial L-function zero lies strictly to the left of the
line `Re(s)=1`. -/
theorem IsPrimitiveNontrivialLFunctionZero.re_lt_one
    {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q} {rho : ℂ}
    (hrho : IsPrimitiveNontrivialLFunctionZero chi rho) :
    rho.re < 1 :=
  LFunction_zero_re_lt_one_of_isPrimitive hrho.1 chi hrho.2.1
    hrho.LFunction_eq_zero

/-- For primitive modulus greater than one, completed zeros are exactly the
ordinary L-function zeros in the open critical strip. -/
theorem isPrimitiveNontrivialLFunctionZero_iff
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (rho : ℂ) :
    IsPrimitiveNontrivialLFunctionZero chi rho ↔
      1 < q ∧ chi.IsPrimitive ∧
        DirichletCharacter.LFunction chi rho = 0 ∧
          0 < rho.re ∧ rho.re < 1 := by
  constructor
  · intro hrho
    exact ⟨hrho.1, hrho.2.1, hrho.LFunction_eq_zero,
      hrho.re_pos, hrho.re_lt_one⟩
  · rintro ⟨hq, hchi, hL, hre0, hre1⟩
    refine ⟨hq, hchi, ?_⟩
    have hgamma := gammaFactor_ne_zero_of_re_pos chi hre0
    have hquot :
        DirichletCharacter.completedLFunction chi rho /
            DirichletCharacter.gammaFactor chi rho = 0 :=
      (DirichletCharacter.LFunction_eq_completed_div_gammaFactor chi rho
        (.inr (Nat.ne_of_gt hq))).symm.trans hL
    exact (div_eq_zero_iff.mp hquot).resolve_right hgamma

/-- A local-height primitive nontrivial zero lies in the closed radius-six
disk used by the fixed-disk logarithmic-derivative estimate. -/
theorem IsPrimitiveNontrivialLFunctionZero.dist_two_add_mul_I_le_six
    {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q} {rho : ℂ}
    (hrho : IsPrimitiveNontrivialLFunctionZero chi rho)
    {t : ℝ} (hheight : |rho.im - t| ≤ 1) :
    dist rho ((2 : ℂ) + t * I) ≤ 6 := by
  have hre0 : 0 ≤ rho.re := hrho.re_pos.le
  have hre1 : rho.re < 1 := hrho.re_lt_one
  have hxabs : |rho.re - 2| ≤ (2 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith
  have hx : (rho.re - 2) ^ 2 ≤ (2 : ℝ) ^ 2 :=
    sq_le_sq.mpr (by simpa using hxabs)
  have hy : (rho.im - t) ^ 2 ≤ (1 : ℝ) ^ 2 :=
    sq_le_sq.mpr (by simpa using hheight)
  rw [Complex.dist_eq, Complex.norm_def, Real.sqrt_le_iff]
  constructor
  · norm_num
  · rw [Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_one, sub_zero, Complex.sub_im, Complex.add_im]
    norm_num
    nlinarith

/-- Every multiplicity-bounded local selection of primitive nontrivial zeros
is a subdivisor of the ordinary closed radius-six divisor. -/
theorem selectedPrimitiveNontrivialZeros_le_radiusSix_analyticOrder
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (t : ℝ) (Z : ℂ →₀ ℕ)
    (hZ : ∀ rho ∈ Z.support,
      IsPrimitiveNontrivialLFunctionZero chi rho ∧
        |rho.im - t| ≤ 1)
    (hmult : ∀ rho : ℂ,
      Z rho ≤ analyticOrderNatAt
        (DirichletCharacter.LFunction chi) rho) :
    ∀ rho : ℂ,
      Z rho ≤
        if dist rho ((2 : ℂ) + t * I) ≤ 6 then
          analyticOrderNatAt (DirichletCharacter.LFunction chi) rho
        else 0 := by
  intro rho
  by_cases hzero : Z rho = 0
  · simp [hzero]
  · have hmem : rho ∈ Z.support := Finsupp.mem_support_iff.mpr hzero
    have hdisk : dist rho ((2 : ℂ) + t * I) ≤ 6 :=
      (hZ rho hmem).1.dist_two_add_mul_I_le_six (hZ rho hmem).2
    rw [if_pos hdisk]
    exact hmult rho

/-- The primitive selected-nontrivial-zero lower bound with the exact SEM-480
residual and explicit ordinary multiplicity premise. -/
theorem exists_nat_selectedPrimitiveNontrivialZeros_sum_sub_le_re_logDeriv_LFunction :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (q : ℕ) [NeZero q], 1 < q →
        ∀ (chi : DirichletCharacter ℂ q), chi.IsPrimitive →
          ∀ (t sigma : ℝ) (Z : ℂ →₀ ℕ),
            1 ≤ sigma → sigma ≤ 2 →
              DirichletCharacter.LFunction chi
                  ((sigma : ℂ) + t * I) ≠ 0 →
                (∀ rho ∈ Z.support,
                  IsPrimitiveNontrivialLFunctionZero chi rho ∧
                    |rho.im - t| ≤ 1) →
                  (∀ rho : ℂ,
                    Z rho ≤ analyticOrderNatAt
                      (DirichletCharacter.LFunction chi) rho) →
                    Z.sum (fun rho m =>
                        (m : ℝ) *
                          ((((sigma : ℂ) + t * I) - rho)⁻¹).re) -
                        16 * ((A : ℝ) *
                          Real.log ((q : ℝ) * (|t| + 2))) / 3 ≤
                      (logDeriv (DirichletCharacter.LFunction chi)
                        ((sigma : ℂ) + t * I)).re := by
  obtain ⟨A, hA, hselected⟩ :=
    exists_nat_selected_radiusSix_subdivisor_sum_sub_le_re_logDeriv_LFunction
  refine ⟨A, hA, ?_⟩
  intro q _ hq chi hchi t sigma Z hsigma1 hsigma2 hLs hZ hmult
  exact hselected q hq chi hchi t sigma Z hsigma1 hsigma2 hLs
    (selectedPrimitiveNontrivialZeros_le_radiusSix_analyticOrder
      chi t Z hZ hmult)

end

end BoundedGaps.Maynard
