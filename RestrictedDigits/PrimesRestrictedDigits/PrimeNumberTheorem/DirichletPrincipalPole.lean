import PrimesRestrictedDigits.PrimeNumberTheorem.PrimitiveEulerFactorBounds
import PrimesRestrictedDigits.PrimeNumberTheorem.ZetaPrincipalPole

/-!
# Principal Dirichlet logarithmic derivatives

This file compares a same-level principal Dirichlet L-function directly with
zeta through its finite Euler product. For decimal-smooth levels, the two
possible factors are uniformly bounded and give the repaired principal pole
inequality needed in Montgomery--Vaughan Theorem 11.3.
-/

open Complex Filter

namespace PrimesRestrictedDigits

private lemma principalEulerFactor_eq (p : Nat) (s : Complex) :
    primitiveEulerFactor (1 : DirichletCharacter Complex 1) p s =
      1 - (p : Complex) ^ (-s) := by
  rw [primitiveEulerFactor,
    MulChar.one_apply (isUnit_of_subsingleton _), one_mul]

private noncomputable def principalEulerCorrection (q : Nat)
    (s : Complex) : Complex :=
  ∏ p ∈ q.primeFactors,
    primitiveEulerFactor (1 : DirichletCharacter Complex 1) p s

private noncomputable def principalEulerLogDerivCorrection (q : Nat)
    (s : Complex) : Complex :=
  ∑ p ∈ q.primeFactors,
    (1 : DirichletCharacter Complex 1) p * Complex.log p *
        (p : Complex) ^ (-s) /
      primitiveEulerFactor (1 : DirichletCharacter Complex 1) p s

private lemma principalLFunction_eq_correction_mul_riemannZeta
    {q : Nat} [NeZero q] {s : Complex} (hs : s ≠ 1) :
    (1 : DirichletCharacter Complex q).LFunction s =
      principalEulerCorrection q s * riemannZeta s := by
  have hCorrection :
      (∏ p ∈ q.primeFactors, (1 - (p : Complex) ^ (-s))) =
        principalEulerCorrection q s := by
    rw [principalEulerCorrection]
    apply Finset.prod_congr rfl
    intro p _hp
    exact (principalEulerFactor_eq p s).symm
  change DirichletCharacter.LFunctionTrivChar q s = _
  rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hs,
    hCorrection]

private lemma principalEulerCorrection_ne_zero_of_re_pos
    (q : Nat) {s : Complex} (hs : 0 < s.re) :
    principalEulerCorrection q s ≠ 0 := by
  rw [principalEulerCorrection, Finset.prod_ne_zero_iff]
  intro p hp
  exact primitiveEulerFactor_ne_zero_of_re_pos
    (1 : DirichletCharacter Complex 1)
    (Nat.prime_of_mem_primeFactors hp) hs

/-- Away from one in the positive half-plane, zeta nonvanishing implies
nonvanishing of the same-level principal Dirichlet L-function. -/
theorem principalLFunction_ne_zero_of_re_pos_of_riemannZeta_ne_zero
    {q : Nat} [NeZero q] {s : Complex} (hsPos : 0 < s.re)
    (hsOne : s ≠ 1) (hZeta : riemannZeta s ≠ 0) :
    (1 : DirichletCharacter Complex q).LFunction s ≠ 0 := by
  rw [principalLFunction_eq_correction_mul_riemannZeta hsOne]
  exact mul_ne_zero (principalEulerCorrection_ne_zero_of_re_pos q hsPos)
    hZeta

/-- Away from its pole, the negative logarithmic derivative of a principal
L-function is the negative logarithmic derivative of Mathlib's entire
regularization plus the unit simple pole. -/
theorem neg_logDeriv_principal_eq_neg_logDeriv_LFunctionTrivChar₁_add_inv
    {q : Nat} [NeZero q] {s : Complex} (hsPos : 0 < s.re)
    (hsOne : s ≠ 1) (hZeta : riemannZeta s ≠ 0) :
    -logDeriv (1 : DirichletCharacter Complex q).LFunction s =
      -logDeriv (DirichletCharacter.LFunctionTrivChar₁ q) s +
        1 / (s - 1) := by
  have hL : (1 : DirichletCharacter Complex q).LFunction s ≠ 0 :=
    principalLFunction_ne_zero_of_re_pos_of_riemannZeta_ne_zero
      hsPos hsOne hZeta
  have hSub : s - 1 ≠ 0 := sub_ne_zero.mpr hsOne
  have hRegularized :
      DirichletCharacter.LFunctionTrivChar₁ q s =
        (s - 1) * (1 : DirichletCharacter Complex q).LFunction s := by
    change Function.update
      (fun z => (z - 1) * (1 : DirichletCharacter Complex q).LFunction z)
      1 _ s = _
    rw [Function.update_of_ne hsOne]
  have hRegularizedNonzero :
      DirichletCharacter.LFunctionTrivChar₁ q s ≠ 0 := by
    rw [hRegularized]
    exact mul_ne_zero hSub hL
  rw [logDeriv_apply, logDeriv_apply,
    DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one q hsOne,
    hRegularized]
  field_simp [hL, hSub, hRegularizedNonzero]
  ring

private lemma differentiableAt_principalEulerCorrection
    (q : Nat) (s : Complex) :
    DifferentiableAt Complex (principalEulerCorrection q) s := by
  change DifferentiableAt Complex
    (fun z : Complex => ∏ p ∈ q.primeFactors,
      primitiveEulerFactor (1 : DirichletCharacter Complex 1) p z) s
  exact .fun_finsetProd fun p hp =>
    (primitiveEulerFactor_hasDerivAt
      (1 : DirichletCharacter Complex 1)
      (Nat.prime_of_mem_primeFactors hp) s).differentiableAt

private lemma logDeriv_principalEulerCorrection
    (q : Nat) {s : Complex} (hs : 0 < s.re) :
    logDeriv (principalEulerCorrection q) s =
      principalEulerLogDerivCorrection q s := by
  change logDeriv (fun z : Complex => ∏ p ∈ q.primeFactors,
    primitiveEulerFactor (1 : DirichletCharacter Complex 1) p z) s = _
  rw [principalEulerLogDerivCorrection, logDeriv_prod]
  · apply Finset.sum_congr rfl
    intro p hp
    exact logDeriv_primitiveEulerFactor
      (1 : DirichletCharacter Complex 1)
      (Nat.prime_of_mem_primeFactors hp) s
  · intro p hp
    exact primitiveEulerFactor_ne_zero_of_re_pos
      (1 : DirichletCharacter Complex 1)
      (Nat.prime_of_mem_primeFactors hp) hs
  · intro p hp
    exact (primitiveEulerFactor_hasDerivAt
      (1 : DirichletCharacter Complex 1)
      (Nat.prime_of_mem_primeFactors hp) s).differentiableAt

private lemma norm_principalEulerLogDerivCorrection_le
    {q : Nat} (hq : IsDecimalSmooth q) {s : Complex}
    (hs : (1 : Real) / 2 ≤ s.re) :
    ‖principalEulerLogDerivCorrection q s‖ ≤ 8 * Real.log 5 := by
  have hcard := hq.card_primeFactors_le_two
  rw [principalEulerLogDerivCorrection]
  calc
    ‖∑ p ∈ q.primeFactors,
        (1 : DirichletCharacter Complex 1) p * Complex.log p *
            (p : Complex) ^ (-s) /
          primitiveEulerFactor
            (1 : DirichletCharacter Complex 1) p s‖ ≤
        ∑ p ∈ q.primeFactors,
          ‖(1 : DirichletCharacter Complex 1) p * Complex.log p *
              (p : Complex) ^ (-s) /
            primitiveEulerFactor
              (1 : DirichletCharacter Complex 1) p s‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _p ∈ q.primeFactors, 4 * Real.log 5 := by
      apply Finset.sum_le_sum
      intro p hp
      have hp5 : p ≤ 5 := by
        have hmem := hq.primeFactors_subset hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        omega
      exact norm_primitiveEulerLogDerivTerm_le_four_log_five
        (1 : DirichletCharacter Complex 1)
        (Nat.prime_of_mem_primeFactors hp) hp5 hs
    _ = q.primeFactors.card * (4 * Real.log 5) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * (4 * Real.log 5) := by
      gcongr
      exact_mod_cast hcard
    _ = 8 * Real.log 5 := by ring

private lemma logDeriv_principal_eq_riemannZeta_add_correction
    {q : Nat} [NeZero q] {s : Complex} (hsPos : 0 < s.re)
    (hsOne : s ≠ 1) (hZeta : riemannZeta s ≠ 0) :
    logDeriv (1 : DirichletCharacter Complex q).LFunction s =
      logDeriv riemannZeta s + principalEulerLogDerivCorrection q s := by
  have hCorrection := principalEulerCorrection_ne_zero_of_re_pos q hsPos
  have hEqNhd :
      (1 : DirichletCharacter Complex q).LFunction =ᶠ[nhds s]
        fun z => principalEulerCorrection q z * riemannZeta z := by
    filter_upwards [eventually_ne_nhds hsOne] with z hz
    exact principalLFunction_eq_correction_mul_riemannZeta hz
  calc
    logDeriv (1 : DirichletCharacter Complex q).LFunction s =
        logDeriv
          (fun z => principalEulerCorrection q z * riemannZeta z) s := by
      rw [logDeriv_apply, logDeriv_apply, hEqNhd.deriv_eq,
        hEqNhd.self_of_nhds]
    _ = logDeriv (principalEulerCorrection q) s +
        logDeriv riemannZeta s :=
      logDeriv_mul s hCorrection hZeta
        (differentiableAt_principalEulerCorrection q s)
        (differentiableAt_riemannZeta hsOne)
    _ = principalEulerLogDerivCorrection q s +
        logDeriv riemannZeta s := by
      rw [logDeriv_principalEulerCorrection q hsPos]
    _ = _ := add_comm _ _

/-- On the closed half-plane `Re(s) ≥ 1 / 2`, away from the pole and zeta
zeros, a decimal-smooth principal L-function logarithmic derivative differs
from zeta by at most the two fixed Euler factors at two and five. -/
theorem norm_logDeriv_principal_sub_riemannZeta_le_of_one_half_le_re
    {q : Nat} [NeZero q] (hq : IsDecimalSmooth q) {s : Complex}
    (hs : (1 : Real) / 2 ≤ s.re) (hsOne : s ≠ 1)
    (hZeta : riemannZeta s ≠ 0) :
    ‖logDeriv (1 : DirichletCharacter Complex q).LFunction s -
      logDeriv riemannZeta s‖ ≤ 8 * Real.log 5 := by
  rw [logDeriv_principal_eq_riemannZeta_add_correction
    (by linarith) hsOne hZeta, add_sub_cancel_left]
  exact norm_principalEulerLogDerivCorrection_le hq hs

/-- At every point strictly to the right of one, a decimal-smooth principal
L-function logarithmic derivative differs from zeta by at most the two fixed
Euler factors at two and five. -/
theorem norm_logDeriv_principal_sub_riemannZeta_le
    {q : Nat} [NeZero q] (hq : IsDecimalSmooth q)
    {s : Complex} (hs : 1 < s.re) :
    ‖logDeriv (1 : DirichletCharacter Complex q).LFunction s -
      logDeriv riemannZeta s‖ ≤ 8 * Real.log 5 := by
  apply norm_logDeriv_principal_sub_riemannZeta_le_of_one_half_le_re hq
  · linarith
  · intro hsEq
    have hRe := congrArg Complex.re hsEq
    norm_num at hRe
    linarith
  · exact riemannZeta_ne_zero_of_one_lt_re hs

/-- One absolute coefficient bounds the negative real logarithmic derivative
of every decimal-smooth principal L-function by its exact pole and a
`log (q * (|t| + 4))` error. -/
theorem exists_decimalSmooth_principal_neg_re_logDeriv_le :
    ∃ A : Real, 0 < A ∧
      ∀ {q : Nat} [NeZero q], IsDecimalSmooth q →
        ∀ delta t : Real, 0 < delta → delta ≤ 1 →
          (-logDeriv (1 : DirichletCharacter Complex q).LFunction
            (((1 + delta : Real) : Complex) +
              Complex.I * (t : Complex))).re ≤
            delta / (delta ^ 2 + t ^ 2) +
              A * Real.log ((q : Real) * (|t| + 4)) := by
  obtain ⟨C, hCPos, hZeta⟩ :=
    exists_neg_re_logDeriv_riemannZeta_le_pole_add_log
  let B : Real := 8 * Real.log 5
  let A : Real := C + B
  have hBPos : 0 < B := by
    dsimp [B]
    exact mul_pos (by norm_num) (Real.log_pos (by norm_num))
  have hAPos : 0 < A := by
    dsimp [A]
    positivity
  refine ⟨A, hAPos, ?_⟩
  intro q _ hq delta t hDeltaPos hDeltaLe
  let s : Complex := ((1 + delta : Real) : Complex) + Complex.I * t
  let tau : Real := |t| + 4
  let Q : Real := (q : Real) * tau
  have hs : 1 < s.re := by
    dsimp [s]
    norm_num
    linarith
  have hCorrection := norm_logDeriv_principal_sub_riemannZeta_le hq hs
  change ‖logDeriv (1 : DirichletCharacter Complex q).LFunction s -
    logDeriv riemannZeta s‖ ≤ B at hCorrection
  have hZetaAt := hZeta delta t hDeltaPos hDeltaLe
  change (-logDeriv riemannZeta s).re ≤
    delta / (delta ^ 2 + t ^ 2) + C * Real.log tau at hZetaAt
  have hLogTauOne : 1 < Real.log tau := by
    dsimp [tau]
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    exact Real.exp_one_lt_three.trans (by linarith [abs_nonneg t])
  have hTauPos : 0 < tau := by
    dsimp [tau]
    linarith [abs_nonneg t]
  have hqOne : (1 : Real) ≤ q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hTauLeQ : tau ≤ Q := by
    dsimp [Q]
    nlinarith
  have hLogTauLeQ : Real.log tau ≤ Real.log Q :=
    Real.log_le_log hTauPos hTauLeQ
  have hLogQOne : 1 < Real.log Q := hLogTauOne.trans_le hLogTauLeQ
  have hCorrectionRe :
      (-logDeriv (1 : DirichletCharacter Complex q).LFunction s).re ≤
        (-logDeriv riemannZeta s).re + B := by
    have hDiffRe :
        -(logDeriv (1 : DirichletCharacter Complex q).LFunction s -
          logDeriv riemannZeta s).re ≤ B := by
      calc
        -(logDeriv (1 : DirichletCharacter Complex q).LFunction s -
            logDeriv riemannZeta s).re ≤
            |(logDeriv (1 : DirichletCharacter Complex q).LFunction s -
              logDeriv riemannZeta s).re| := neg_le_abs _
        _ ≤ ‖logDeriv (1 : DirichletCharacter Complex q).LFunction s -
              logDeriv riemannZeta s‖ := Complex.abs_re_le_norm _
        _ ≤ B := hCorrection
    have hIdentity :
        (-logDeriv (1 : DirichletCharacter Complex q).LFunction s).re =
          (-logDeriv riemannZeta s).re -
            (logDeriv (1 : DirichletCharacter Complex q).LFunction s -
              logDeriv riemannZeta s).re := by
      simp only [Complex.neg_re, Complex.sub_re]
      ring
    rw [hIdentity]
    linarith
  have hCScale : C * Real.log tau ≤ C * Real.log Q :=
    mul_le_mul_of_nonneg_left hLogTauLeQ hCPos.le
  have hBAbsorb : B ≤ B * Real.log Q := by
    nlinarith
  change (-logDeriv (1 : DirichletCharacter Complex q).LFunction s).re ≤
    delta / (delta ^ 2 + t ^ 2) + A * Real.log Q
  dsimp [A]
  calc
    (-logDeriv (1 : DirichletCharacter Complex q).LFunction s).re ≤
        (-logDeriv riemannZeta s).re + B := hCorrectionRe
    _ ≤ delta / (delta ^ 2 + t ^ 2) + C * Real.log tau + B := by
      linarith
    _ ≤ delta / (delta ^ 2 + t ^ 2) + C * Real.log Q + B := by
      linarith
    _ ≤ delta / (delta ^ 2 + t ^ 2) +
        C * Real.log Q + B * Real.log Q := by
      linarith
    _ = delta / (delta ^ 2 + t ^ 2) +
        (C + B) * Real.log Q := by ring

end PrimesRestrictedDigits
