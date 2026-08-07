import BoundedGaps.BombieriVinogradov.Analytic.RiemannZetaHeightPole

/-!
# The arbitrary-height principal-character pole estimate

Mathlib factors the principal Dirichlet L-function at level `q` as zeta times
the finite Euler product over primes dividing `q`. On the closed half-plane
`Re(s) >= 1`, each Euler-factor logarithmic derivative has norm at most
`log p`; their sum is at most `log q`. Combining this exact correction with
the regularized-zeta fixed-disk estimate retains the coefficient-one complex
pole at every height.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 119,
equation (12.1) and Lemma 12.2, and printed p. 120, equation (12.5).
Semantic review: `SEM-482`.
-/

noncomputable section

namespace BoundedGaps.Maynard

open Complex Filter
open scoped Topology

private noncomputable def principalEulerProduct (q : ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))

private lemma norm_natCast_cpow_neg_le_half
    (p : ℕ) (hp : p.Prime) (s : ℂ) (hs : 1 ≤ s.re) :
    ‖(p : ℂ) ^ (-s)‖ ≤ (1 / 2 : ℝ) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : (1 : ℝ) ≤ p := one_le_two.trans hp2
  have hpow : (2 : ℝ) ≤ (p : ℝ) ^ s.re := by
    calc
      (2 : ℝ) ≤ p := hp2
      _ = (p : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ (p : ℝ) ^ s.re :=
        Real.rpow_le_rpow_of_exponent_le hp1 hs
  rw [Complex.norm_natCast_cpow_of_pos hp.pos, neg_re,
    Real.rpow_neg (Nat.cast_nonneg p)]
  simpa [one_div] using
    (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hpow)

private lemma principalEulerFactor_ne_zero
    (p : ℕ) (hp : p.Prime) (s : ℂ) (hs : 1 ≤ s.re) :
    (1 : ℂ) - (p : ℂ) ^ (-s) ≠ 0 := by
  intro hzero
  have hpow : (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp hzero).symm
  have hnorm := norm_natCast_cpow_neg_le_half p hp s hs
  rw [hpow, norm_one] at hnorm
  linarith

private lemma differentiableAt_principalEulerFactor
    (p : ℕ) (hp : p.Prime) (s : ℂ) :
    DifferentiableAt ℂ (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s :=
  ((hasDerivAt_const s (1 : ℂ)).sub
    ((hasDerivAt_neg' s).const_cpow
      (Or.inl (Nat.cast_ne_zero.mpr hp.ne_zero)))).differentiableAt

private lemma norm_logDeriv_principalEulerFactor_le_log
    (p : ℕ) (hp : p.Prime) (s : ℂ) (hs : 1 ≤ s.re) :
    ‖logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖ ≤
      Real.log p := by
  let w : ℂ := (p : ℂ) ^ (-s)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hwNorm : ‖w‖ ≤ (1 / 2 : ℝ) :=
    norm_natCast_cpow_neg_le_half p hp s hs
  have hden : (1 / 2 : ℝ) ≤ ‖(1 : ℂ) - w‖ := by
    have hreverse := norm_sub_norm_le (1 : ℂ) w
    norm_num at hreverse
    linarith
  have hdenPos : 0 < ‖(1 : ℂ) - w‖ := by linarith
  have hpcast : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpowDeriv :=
    (hasDerivAt_neg' s).const_cpow (c := (p : ℂ)) (Or.inl hpcast)
  have hfactorDeriv := (hasDerivAt_const s (1 : ℂ)).sub hpowDeriv
  have hderiv :
      deriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s =
        (p : ℂ) ^ (-s) * Complex.log p := by
    have hd := hfactorDeriv.deriv
    change deriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s = _ at hd
    calc
      _ = 0 - (p : ℂ) ^ (-s) * Complex.log p * -1 := hd
      _ = _ := by ring
  have hlogNorm : ‖Complex.log (p : ℂ)‖ = Real.log p := by
    rw [show (p : ℂ) = ((p : ℝ) : ℂ) by norm_cast,
      ← Complex.ofReal_log (Nat.cast_nonneg p), Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg]
    exact Real.log_nonneg hp1
  rw [logDeriv_apply, hderiv, norm_div, norm_mul, hlogNorm]
  apply (div_le_iff₀ hdenPos).2
  have hwDen : ‖w‖ ≤ ‖(1 : ℂ) - w‖ := hwNorm.trans hden
  simpa [w, mul_comm] using
    mul_le_mul_of_nonneg_left hwDen (Real.log_nonneg hp1)

private lemma principalEulerProduct_ne_zero
    (q : ℕ) (s : ℂ) (hs : 1 ≤ s.re) :
    principalEulerProduct q s ≠ 0 := by
  rw [principalEulerProduct, Finset.prod_ne_zero_iff]
  intro p hp
  exact principalEulerFactor_ne_zero p
    (Nat.prime_of_mem_primeFactors hp) s hs

private lemma differentiableAt_principalEulerProduct
    (q : ℕ) (s : ℂ) :
    DifferentiableAt ℂ (principalEulerProduct q) s := by
  unfold principalEulerProduct
  exact .fun_finsetProd fun p hp =>
    differentiableAt_principalEulerFactor p
      (Nat.prime_of_mem_primeFactors hp) s

private lemma norm_logDeriv_principalEulerProduct_le_log
    (q : ℕ) [NeZero q] (s : ℂ) (hs : 1 ≤ s.re) :
    ‖logDeriv (principalEulerProduct q) s‖ ≤ Real.log q := by
  change ‖logDeriv (fun z : ℂ =>
    ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) s‖ ≤ _
  rw [logDeriv_prod]
  · calc
      ‖∑ p ∈ q.primeFactors,
          logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖ ≤
          ∑ p ∈ q.primeFactors,
            ‖logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖ :=
        norm_sum_le _ _
      _ ≤ ∑ p ∈ q.primeFactors, Real.log p := by
        exact Finset.sum_le_sum fun p hp =>
          norm_logDeriv_principalEulerFactor_le_log p
            (Nat.prime_of_mem_primeFactors hp) s hs
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
        have hcast : (P : ℝ) = ∏ p ∈ q.primeFactors, (p : ℝ) := by
          simp [P]
        rw [← hcast]
        exact Real.log_le_log (by exact_mod_cast hPpos)
          (by exact_mod_cast hPle)
  · intro p hp
    exact principalEulerFactor_ne_zero p
      (Nat.prime_of_mem_primeFactors hp) s hs
  · intro p hp
    exact differentiableAt_principalEulerFactor p
      (Nat.prime_of_mem_primeFactors hp) s

/-- The same-level principal Euler factors cost at most `log q`. -/
theorem norm_logDeriv_principal_LFunction_sub_riemannZeta_le_log
    {q : ℕ} [NeZero q] {s : ℂ}
    (hs : 1 ≤ s.re) (hs1 : s ≠ 1) :
    ‖logDeriv (DirichletCharacter.LFunction
          (1 : DirichletCharacter ℂ q)) s -
        logDeriv riemannZeta s‖ ≤ Real.log (q : ℝ) := by
  let P : ℂ → ℂ := principalEulerProduct q
  have heq : DirichletCharacter.LFunction
      (1 : DirichletCharacter ℂ q) =ᶠ[𝓝 s]
        fun z => P z * riemannZeta z := by
    filter_upwards [eventually_ne_nhds hs1] with z hz
    change DirichletCharacter.LFunctionTrivChar q z = _
    simpa [P, principalEulerProduct] using
      DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta
        (N := q) hz
  have hP : P s ≠ 0 := principalEulerProduct_ne_zero q s hs
  have hzeta : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re hs
  have hlog :
      logDeriv (DirichletCharacter.LFunction
          (1 : DirichletCharacter ℂ q)) s =
        logDeriv P s + logDeriv riemannZeta s := by
    calc
      logDeriv (DirichletCharacter.LFunction
          (1 : DirichletCharacter ℂ q)) s =
          logDeriv (fun z => P z * riemannZeta z) s := by
        rw [logDeriv_apply, logDeriv_apply, heq.deriv_eq,
          heq.self_of_nhds]
      _ = logDeriv P s + logDeriv riemannZeta s :=
        logDeriv_mul s hP hzeta
          (differentiableAt_principalEulerProduct q s)
          (differentiableAt_riemannZeta hs1)
  rw [hlog, add_sub_cancel_right]
  exact norm_logDeriv_principalEulerProduct_le_log q s hs

/-- The arbitrary-height principal-character pole estimate used in
Koukoulopoulos Lemma 12.2 with an empty selected list. -/
theorem exists_nat_neg_logDeriv_principal_LFunction_re_le_pole_add_log :
    ∃ A : ℕ, 1 ≤ A ∧
      ∀ (q : ℕ) [NeZero q] (s : ℂ),
        1 ≤ s.re → s.re ≤ 2 → s ≠ 1 →
          (-logDeriv (DirichletCharacter.LFunction
            (1 : DirichletCharacter ℂ q)) s).re ≤
            ((s - 1)⁻¹).re +
              (16 * (A : ℝ) + 1) *
                Real.log ((q : ℝ) * (|s.im| + 2)) := by
  obtain ⟨A, hA, hzetaBound⟩ :=
    exists_nat_neg_logDeriv_riemannZeta_re_le_pole_add_log
  refine ⟨A, hA, ?_⟩
  intro q _ s hs1 hs2 hsne
  let T : ℝ := |s.im| + 2
  let Q : ℝ := (q : ℝ) * T
  let D : ℂ :=
    logDeriv (DirichletCharacter.LFunction
      (1 : DirichletCharacter ℂ q)) s - logDeriv riemannZeta s
  have hq1 : (1 : ℝ) ≤ q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hqpos : (0 : ℝ) < q := zero_lt_one.trans_le hq1
  have hT2 : (2 : ℝ) ≤ T := by dsimp [T]; linarith [abs_nonneg s.im]
  have hTpos : 0 < T := zero_lt_two.trans_le hT2
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (one_le_two.trans hT2)
  have hcorrection : ‖D‖ ≤ Real.log (q : ℝ) := by
    simpa [D] using
      norm_logDeriv_principal_LFunction_sub_riemannZeta_le_log hs1 hsne
  have hcorrectionRe : -D.re ≤ Real.log (q : ℝ) := by
    calc
      -D.re ≤ |D.re| := neg_le_abs _
      _ ≤ ‖D‖ := Complex.abs_re_le_norm _
      _ ≤ Real.log (q : ℝ) := hcorrection
  have hidentity :
      (-logDeriv (DirichletCharacter.LFunction
        (1 : DirichletCharacter ℂ q)) s).re =
        (-logDeriv riemannZeta s).re - D.re := by
    simp only [Complex.neg_re, D, Complex.sub_re]
    ring_nf
  have hzeta :
      (-logDeriv riemannZeta s).re ≤
        ((s - 1)⁻¹).re + 16 * (A : ℝ) * Real.log T := by
    simpa [T] using hzetaBound s hs1 hs2 hsne
  have hraw :
      (-logDeriv (DirichletCharacter.LFunction
        (1 : DirichletCharacter ℂ q)) s).re ≤
        ((s - 1)⁻¹).re +
          16 * (A : ℝ) * Real.log T + Real.log (q : ℝ) := by
    rw [hidentity]
    linarith
  have hlogQ : Real.log Q = Real.log (q : ℝ) + Real.log T := by
    dsimp [Q]
    exact Real.log_mul hqpos.ne' hTpos.ne'
  have hscale :
      16 * (A : ℝ) * Real.log T + Real.log (q : ℝ) ≤
        (16 * (A : ℝ) + 1) * Real.log Q := by
    rw [hlogQ]
    have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg A
    have hAq : 0 ≤ 16 * (A : ℝ) * Real.log (q : ℝ) :=
      mul_nonneg (mul_nonneg (by norm_num) hA0) hlogq
    nlinarith
  calc
    (-logDeriv (DirichletCharacter.LFunction
        (1 : DirichletCharacter ℂ q)) s).re ≤
        ((s - 1)⁻¹).re +
          (16 * (A : ℝ) * Real.log T + Real.log (q : ℝ)) := by
      linarith
    _ ≤ ((s - 1)⁻¹).re + (16 * (A : ℝ) + 1) * Real.log Q :=
      by linarith
    _ = ((s - 1)⁻¹).re +
        (16 * (A : ℝ) + 1) *
          Real.log ((q : ℝ) * (|s.im| + 2)) := by rfl

end BoundedGaps.Maynard
