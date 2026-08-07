import BoundedGaps.BombieriVinogradov.Analytic.InducingEulerProduct
import BoundedGaps.BombieriVinogradov.Analytic.PrimitiveLFunctionNontrivialSelection

/-!
# Imprimitive Dirichlet L-function transport

The L-function of a nonprincipal character is its inducing primitive
L-function times a finite Euler product. The extra factors are nonzero on
`Re(s) > 0`, preserve open-strip zero multiplicities, and cost at most
`log q` in logarithmic derivative on `Re(s) >= 1`.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 110,
equation (11.2), pp. 112--114, and p. 119, equation (12.1) and Lemma 12.2.
Semantic review: `SEM-483`.
-/

noncomputable section

namespace BoundedGaps.Maynard

open Complex Filter
open scoped Topology

private local instance conductorNeZero
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) :
    NeZero chi.conductor :=
  ⟨chi.conductor_ne_zero⟩

private lemma primitiveCharacter_ne_one_of_ne_one
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1) :
    chi.primitiveCharacter ≠ 1 := by
  intro hpsi
  apply hchi
  rw [← chi.changeLevel_primitiveCharacter]
  exact (DirichletCharacter.changeLevel_eq_one_iff
    chi.conductor_dvd_level).2 hpsi

private lemma one_lt_conductor_of_ne_one
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1) :
    1 < chi.conductor := by
  have hzero : chi.conductor ≠ 0 := chi.conductor_ne_zero
  have hone : chi.conductor ≠ 1 := by
    intro hc
    exact hchi (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr hc)
  omega

private lemma norm_character_mul_cpow_lt_one
    {d : ℕ} (psi : DirichletCharacter ℂ d)
    (p : ℕ) (hp : p.Prime) (s : ℂ) (hs : 0 < s.re) :
    ‖psi p * (p : ℂ) ^ (-s)‖ < 1 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp.pos, neg_re]
  calc
    ‖psi p‖ * (p : ℝ) ^ (-s.re) ≤
        1 * (p : ℝ) ^ (-s.re) :=
      mul_le_mul_of_nonneg_right (psi.norm_le_one p)
        (Real.rpow_nonneg (Nat.cast_nonneg p) _)
    _ < 1 := by
      simpa using
        Real.rpow_lt_one_of_one_lt_of_neg hp1 (neg_neg_of_pos hs)

private lemma inducingEulerFactor_ne_zero_of_re_pos
    {d : ℕ} (psi : DirichletCharacter ℂ d)
    (p : ℕ) (hp : p.Prime) (s : ℂ) (hs : 0 < s.re) :
    (1 : ℂ) - psi p * (p : ℂ) ^ (-s) ≠ 0 := by
  intro hzero
  have hw : psi p * (p : ℂ) ^ (-s) = 1 :=
    (sub_eq_zero.mp hzero).symm
  have hnorm := norm_character_mul_cpow_lt_one psi p hp s hs
  rw [hw, norm_one] at hnorm
  exact (lt_irrefl 1) hnorm

private lemma differentiableAt_inducingEulerFactor
    {d : ℕ} (psi : DirichletCharacter ℂ d)
    (p : ℕ) (hp : p.Prime) (s : ℂ) :
    DifferentiableAt ℂ
      (fun z : ℂ => 1 - psi p * (p : ℂ) ^ (-z)) s :=
  ((hasDerivAt_const s (1 : ℂ)).sub
    (((hasDerivAt_neg' s).const_cpow
      (Or.inl (Nat.cast_ne_zero.mpr hp.ne_zero))).const_mul
        (psi p))).differentiableAt

private lemma norm_character_mul_cpow_neg_le_half
    {d : ℕ} (psi : DirichletCharacter ℂ d)
    (p : ℕ) (hp : p.Prime) (s : ℂ) (hs : 1 ≤ s.re) :
    ‖psi p * (p : ℂ) ^ (-s)‖ ≤ (1 / 2 : ℝ) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : (1 : ℝ) ≤ p := one_le_two.trans hp2
  have hpow : (2 : ℝ) ≤ (p : ℝ) ^ s.re := by
    calc
      (2 : ℝ) ≤ p := hp2
      _ = (p : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ (p : ℝ) ^ s.re :=
        Real.rpow_le_rpow_of_exponent_le hp1 hs
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp.pos, neg_re,
    Real.rpow_neg (Nat.cast_nonneg p)]
  calc
    ‖psi p‖ * ((p : ℝ) ^ s.re)⁻¹ ≤
        1 * ((p : ℝ) ^ s.re)⁻¹ :=
      mul_le_mul_of_nonneg_right (psi.norm_le_one p)
        (inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg p) _))
    _ ≤ (1 / 2 : ℝ) := by
      simpa [one_div] using
        (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hpow)

private lemma norm_logDeriv_inducingEulerFactor_le_log
    {d : ℕ} (psi : DirichletCharacter ℂ d)
    (p : ℕ) (hp : p.Prime) (s : ℂ) (hs : 1 ≤ s.re) :
    ‖logDeriv (fun z : ℂ =>
        1 - psi p * (p : ℂ) ^ (-z)) s‖ ≤ Real.log p := by
  let w : ℂ := psi p * (p : ℂ) ^ (-s)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hwNorm : ‖w‖ ≤ (1 / 2 : ℝ) :=
    norm_character_mul_cpow_neg_le_half psi p hp s hs
  have hden : (1 / 2 : ℝ) ≤ ‖(1 : ℂ) - w‖ := by
    have hreverse := norm_sub_norm_le (1 : ℂ) w
    norm_num at hreverse
    linarith
  have hdenPos : 0 < ‖(1 : ℂ) - w‖ := by linarith
  have hpowDeriv :=
    (hasDerivAt_neg' s).const_cpow (c := (p : ℂ))
      (Or.inl (Nat.cast_ne_zero.mpr hp.ne_zero))
  have hfactorDeriv := (hasDerivAt_const s (1 : ℂ)).sub
    (hpowDeriv.const_mul (psi p))
  have hderiv :
      deriv (fun z : ℂ => 1 - psi p * (p : ℂ) ^ (-z)) s =
        psi p * (p : ℂ) ^ (-s) * Complex.log p := by
    have hd := hfactorDeriv.deriv
    change deriv (fun z : ℂ => 1 - psi p * (p : ℂ) ^ (-z)) s = _ at hd
    calc
      _ = 0 - psi p * ((p : ℂ) ^ (-s) * Complex.log p * -1) := hd
      _ = _ := by ring
  have hlogNorm : ‖Complex.log (p : ℂ)‖ = Real.log p := by
    rw [show (p : ℂ) = ((p : ℝ) : ℂ) by norm_cast,
      ← Complex.ofReal_log (Nat.cast_nonneg p), Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg]
    exact Real.log_nonneg hp1
  rw [logDeriv_apply, hderiv, norm_div, norm_mul, hlogNorm]
  change ‖w‖ * Real.log p / ‖(1 : ℂ) - w‖ ≤ Real.log p
  apply (div_le_iff₀ hdenPos).2
  have hwDen : ‖w‖ ≤ ‖(1 : ℂ) - w‖ := hwNorm.trans hden
  simpa [mul_comm] using
    mul_le_mul_of_nonneg_right hwDen (Real.log_nonneg hp1)

private lemma norm_logDeriv_inducingEulerProduct_le_log
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (s : ℂ) (hs : 1 ≤ s.re) :
    ‖logDeriv (inducingEulerProduct chi) s‖ ≤ Real.log q := by
  change ‖logDeriv (fun z : ℂ =>
    ∏ p ∈ q.primeFactors,
      (1 - chi.primitiveCharacter p * (p : ℂ) ^ (-z))) s‖ ≤ _
  rw [logDeriv_prod]
  · calc
      ‖∑ p ∈ q.primeFactors,
          logDeriv (fun z : ℂ =>
            1 - chi.primitiveCharacter p * (p : ℂ) ^ (-z)) s‖ ≤
          ∑ p ∈ q.primeFactors,
            ‖logDeriv (fun z : ℂ =>
              1 - chi.primitiveCharacter p * (p : ℂ) ^ (-z)) s‖ :=
        norm_sum_le _ _
      _ ≤ ∑ p ∈ q.primeFactors, Real.log p := by
        exact Finset.sum_le_sum fun p hp =>
          norm_logDeriv_inducingEulerFactor_le_log
            chi.primitiveCharacter p (Nat.prime_of_mem_primeFactors hp) s hs
      _ = Real.log (∏ p ∈ q.primeFactors, (p : ℝ)) := by
        rw [Real.log_prod]
        intro p hp
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
      _ ≤ Real.log q := by
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
        rw [← hcast]
        exact Real.log_le_log (by exact_mod_cast hPpos)
          (by exact_mod_cast hPle)
  · intro p hp
    exact inducingEulerFactor_ne_zero_of_re_pos chi.primitiveCharacter p
      (Nat.prime_of_mem_primeFactors hp) s (zero_lt_one.trans_le hs)
  · intro p hp
    exact differentiableAt_inducingEulerFactor chi.primitiveCharacter p
      (Nat.prime_of_mem_primeFactors hp) s

/-- A nontrivial zero inherited from the inducing primitive character of a
nonprincipal character. Principal zeta zeros are intentionally separate. -/
def IsNonprincipalNontrivialLFunctionZero
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (rho : ℂ) : Prop :=
  chi ≠ 1 ∧
    DirichletCharacter.completedLFunction chi.primitiveCharacter rho = 0

/-- The inducing-primitive definition is exactly ordinary imprimitive
vanishing in the open critical strip. -/
theorem isNonprincipalNontrivialLFunctionZero_iff
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (rho : ℂ) :
    IsNonprincipalNontrivialLFunctionZero chi rho ↔
      chi ≠ 1 ∧
        DirichletCharacter.LFunction chi rho = 0 ∧
          0 < rho.re ∧ rho.re < 1 := by
  constructor
  · rintro ⟨hchi, hcompleted⟩
    have hprimitive :
        IsPrimitiveNontrivialLFunctionZero chi.primitiveCharacter rho :=
      ⟨one_lt_conductor_of_ne_one chi hchi,
        chi.primitiveCharacter_isPrimitive, hcompleted⟩
    have hordinary :=
      (isPrimitiveNontrivialLFunctionZero_iff
        chi.primitiveCharacter rho).1 hprimitive
    refine ⟨hchi, ?_, hordinary.2.2.2.1, hordinary.2.2.2.2⟩
    rw [LFunction_eq_inducingPrimitive_mul_inducingEulerProduct chi
      (.inl hchi),
      hordinary.2.2.1, zero_mul]
  · rintro ⟨hchi, hzero, hre0, hre1⟩
    have hprimitiveZero :
        DirichletCharacter.LFunction chi.primitiveCharacter rho = 0 := by
      rw [LFunction_eq_inducingPrimitive_mul_inducingEulerProduct chi
        (.inl hchi)] at hzero
      exact (mul_eq_zero.mp hzero).resolve_right
        (inducingEulerProduct_ne_zero_of_re_pos chi hre0)
    have hprimitive :
        IsPrimitiveNontrivialLFunctionZero chi.primitiveCharacter rho :=
      (isPrimitiveNontrivialLFunctionZero_iff
        chi.primitiveCharacter rho).2
          ⟨one_lt_conductor_of_ne_one chi hchi,
            chi.primitiveCharacter_isPrimitive,
            hprimitiveZero, hre0, hre1⟩
    exact ⟨hchi, hprimitive.2.2⟩

/-- Imprimitive Euler factors add no multiplicity in the open right
half-plane. -/
theorem analyticOrderNatAt_LFunction_eq_inducingPrimitive_of_re_pos
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {rho : ℂ} (hrho : 0 < rho.re) :
    analyticOrderNatAt (DirichletCharacter.LFunction chi) rho =
      analyticOrderNatAt
        (DirichletCharacter.LFunction chi.primitiveCharacter) rho := by
  let P : ℂ → ℂ := inducingEulerProduct chi
  have heq : DirichletCharacter.LFunction chi =ᶠ[𝓝 rho]
      fun z => DirichletCharacter.LFunction chi.primitiveCharacter z * P z :=
    Eventually.of_forall fun z => by
      simpa [P] using
        LFunction_eq_inducingPrimitive_mul_inducingEulerProduct chi
          (.inl hchi)
  have hpsi : AnalyticAt ℂ
      (DirichletCharacter.LFunction chi.primitiveCharacter) rho :=
    (DirichletCharacter.differentiable_LFunction
      (primitiveCharacter_ne_one_of_ne_one chi hchi)).analyticAt rho
  have hP : AnalyticAt ℂ P rho := by
    simpa [P] using (differentiable_inducingEulerProduct chi).analyticAt rho
  have hPne : P rho ≠ 0 := by
    simpa [P] using inducingEulerProduct_ne_zero_of_re_pos chi hrho
  have horder :
      analyticOrderAt (DirichletCharacter.LFunction chi) rho =
        analyticOrderAt
          (DirichletCharacter.LFunction chi.primitiveCharacter) rho := by
    calc
      analyticOrderAt (DirichletCharacter.LFunction chi) rho =
          analyticOrderAt
            (fun z =>
              DirichletCharacter.LFunction chi.primitiveCharacter z * P z) rho :=
        analyticOrderAt_congr heq
      _ = analyticOrderAt
            (DirichletCharacter.LFunction chi.primitiveCharacter) rho +
          analyticOrderAt P rho := analyticOrderAt_mul hpsi hP
      _ = analyticOrderAt
            (DirichletCharacter.LFunction chi.primitiveCharacter) rho := by
        rw [hP.analyticOrderAt_eq_zero.mpr hPne, add_zero]
  exact congrArg ENat.toNat horder

/-- Equation (12.1) with an explicit arbitrary-modulus constant. -/
theorem norm_logDeriv_LFunction_sub_inducingPrimitive_le_log
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {s : ℂ} (hs : 1 ≤ s.re) :
    ‖logDeriv (DirichletCharacter.LFunction chi) s -
        logDeriv
          (DirichletCharacter.LFunction chi.primitiveCharacter) s‖ ≤
      Real.log (q : ℝ) := by
  let P : ℂ → ℂ := inducingEulerProduct chi
  have heq : DirichletCharacter.LFunction chi =ᶠ[𝓝 s]
      fun z => DirichletCharacter.LFunction chi.primitiveCharacter z * P z :=
    Eventually.of_forall fun z => by
      simpa [P] using
        LFunction_eq_inducingPrimitive_mul_inducingEulerProduct chi
          (.inl hchi)
  have hPne : P s ≠ 0 := by
    simpa [P] using inducingEulerProduct_ne_zero_of_re_pos chi
      (zero_lt_one.trans_le hs)
  have hpsiNe :
      DirichletCharacter.LFunction chi.primitiveCharacter s ≠ 0 :=
    chi.primitiveCharacter.LFunction_ne_zero_of_one_le_re
      (.inl (primitiveCharacter_ne_one_of_ne_one chi hchi)) hs
  have hlog :
      logDeriv (DirichletCharacter.LFunction chi) s =
        logDeriv (DirichletCharacter.LFunction chi.primitiveCharacter) s +
          logDeriv P s := by
    calc
      logDeriv (DirichletCharacter.LFunction chi) s =
          logDeriv (fun z =>
            DirichletCharacter.LFunction chi.primitiveCharacter z * P z) s := by
        rw [logDeriv_apply, logDeriv_apply, heq.deriv_eq,
          heq.self_of_nhds]
      _ = logDeriv
            (DirichletCharacter.LFunction chi.primitiveCharacter) s +
          logDeriv P s :=
        logDeriv_mul s hpsiNe hPne
          (DirichletCharacter.differentiable_LFunction
            (primitiveCharacter_ne_one_of_ne_one chi hchi) s)
          (by simpa [P] using differentiable_inducingEulerProduct chi s)
  rw [hlog, add_sub_cancel_left]
  simpa [P] using norm_logDeriv_inducingEulerProduct_le_log chi s hs

/-- The nonprincipal imprimitive selected-zero form of Lemma 12.2. -/
theorem exists_nat_selectedNonprincipalNontrivialZeros_sum_sub_le_re_logDeriv_LFunction :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (q : ℕ) [NeZero q]
        (chi : DirichletCharacter ℂ q), chi ≠ 1 →
          ∀ (t sigma : ℝ) (Z : ℂ →₀ ℕ),
            1 ≤ sigma → sigma ≤ 2 →
              (∀ rho ∈ Z.support,
                IsNonprincipalNontrivialLFunctionZero chi rho ∧
                  |rho.im - t| ≤ 1) →
                (∀ rho : ℂ,
                  Z rho ≤ analyticOrderNatAt
                    (DirichletCharacter.LFunction chi) rho) →
                  Z.sum (fun rho m =>
                      (m : ℝ) *
                        ((((sigma : ℂ) + t * Complex.I) - rho)⁻¹).re) -
                    (16 * (A : ℝ) + 3) *
                        Real.log ((q : ℝ) * (|t| + 2)) / 3 ≤
                    (logDeriv (DirichletCharacter.LFunction chi)
                      ((sigma : ℂ) + t * Complex.I)).re := by
  obtain ⟨A, hA, hprimitive⟩ :=
    exists_nat_selectedPrimitiveNontrivialZeros_sum_sub_le_re_logDeriv_LFunction
  refine ⟨A, hA, ?_⟩
  intro q _ chi hchi t sigma Z hsigma1 hsigma2 hZ hmult
  let s : ℂ := (sigma : ℂ) + t * I
  let T : ℝ := |t| + 2
  let d : ℕ := chi.conductor
  let D : ℂ := logDeriv (DirichletCharacter.LFunction chi) s -
    logDeriv (DirichletCharacter.LFunction chi.primitiveCharacter) s
  have hd1 : 1 < d := by
    simpa [d] using one_lt_conductor_of_ne_one chi hchi
  have hZprimitive :
      ∀ rho ∈ Z.support,
        IsPrimitiveNontrivialLFunctionZero chi.primitiveCharacter rho ∧
          |rho.im - t| ≤ 1 := by
    intro rho hrho
    exact ⟨⟨hd1, chi.primitiveCharacter_isPrimitive,
      (hZ rho hrho).1.2⟩, (hZ rho hrho).2⟩
  have hmultPrimitive :
      ∀ rho : ℂ,
        Z rho ≤ analyticOrderNatAt
          (DirichletCharacter.LFunction chi.primitiveCharacter) rho := by
    intro rho
    by_cases hz : Z rho = 0
    · simp [hz]
    · have hrho : rho ∈ Z.support := Finsupp.mem_support_iff.mpr hz
      have hre0 : 0 < rho.re :=
        ((isNonprincipalNontrivialLFunctionZero_iff chi rho).1
          (hZ rho hrho).1).2.2.1
      rw [← analyticOrderNatAt_LFunction_eq_inducingPrimitive_of_re_pos
        chi hchi hre0]
      exact hmult rho
  have hsre : 1 ≤ s.re := by simpa [s] using hsigma1
  have hpsiNe :
      DirichletCharacter.LFunction chi.primitiveCharacter s ≠ 0 :=
    chi.primitiveCharacter.LFunction_ne_zero_of_one_le_re
      (.inl (primitiveCharacter_ne_one_of_ne_one chi hchi)) hsre
  have hprimitiveBound := hprimitive d hd1 chi.primitiveCharacter
    chi.primitiveCharacter_isPrimitive t sigma Z hsigma1 hsigma2 hpsiNe
    hZprimitive hmultPrimitive
  have hcomparison : ‖D‖ ≤ Real.log (q : ℝ) := by
    simpa [D] using
      norm_logDeriv_LFunction_sub_inducingPrimitive_le_log chi hchi hsre
  have hDre : -Real.log (q : ℝ) ≤ D.re := by
    have habs : |D.re| ≤ ‖D‖ := Complex.abs_re_le_norm D
    have hnegabs : -|D.re| ≤ D.re := neg_abs_le D.re
    linarith
  have hidentity :
      (logDeriv (DirichletCharacter.LFunction chi) s).re =
        (logDeriv
          (DirichletCharacter.LFunction chi.primitiveCharacter) s).re +
            D.re := by
    simp only [D, Complex.sub_re]
    ring
  have hT2 : (2 : ℝ) ≤ T := by
    dsimp [T]
    linarith [abs_nonneg t]
  have hTpos : 0 < T := zero_lt_two.trans_le hT2
  have hqpos : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hdpos : (0 : ℝ) < d := by
    exact_mod_cast (zero_lt_one.trans hd1)
  have hdqNat : d ≤ q := by
    dsimp [d]
    exact Nat.le_of_dvd (NeZero.pos q) chi.conductor_dvd_level
  have hdq : (d : ℝ) ≤ q := by exact_mod_cast hdqNat
  have hprod : (d : ℝ) * T ≤ (q : ℝ) * T :=
    mul_le_mul_of_nonneg_right hdq hTpos.le
  have hlogProd :
      Real.log ((d : ℝ) * T) ≤ Real.log ((q : ℝ) * T) :=
    Real.log_le_log (mul_pos hdpos hTpos) hprod
  have hTone : (1 : ℝ) ≤ T := one_le_two.trans hT2
  have hqT : (q : ℝ) ≤ (q : ℝ) * T := by
    simpa using mul_le_mul_of_nonneg_left hTone hqpos.le
  have hlogq :
      Real.log (q : ℝ) ≤ Real.log ((q : ℝ) * T) :=
    Real.log_le_log hqpos hqT
  have hscaled :
      16 * ((A : ℝ) * Real.log ((d : ℝ) * T)) / 3 +
          Real.log (q : ℝ) ≤
        (16 * (A : ℝ) + 3) * Real.log ((q : ℝ) * T) / 3 := by
    have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg A
    have hmul := mul_le_mul_of_nonneg_left hlogProd
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) hA0)
    nlinarith
  have hprim :
      Z.sum (fun rho m =>
        (m : ℝ) * (((s - rho)⁻¹).re)) -
          16 * ((A : ℝ) * Real.log ((d : ℝ) * T)) / 3 ≤
        (logDeriv
          (DirichletCharacter.LFunction chi.primitiveCharacter) s).re := by
    simpa [s, d, T] using hprimitiveBound
  change Z.sum (fun rho m =>
      (m : ℝ) * (((s - rho)⁻¹).re)) -
      (16 * (A : ℝ) + 3) * Real.log ((q : ℝ) * T) / 3 ≤
    (logDeriv (DirichletCharacter.LFunction chi) s).re
  rw [hidentity]
  linarith

end BoundedGaps.Maynard
