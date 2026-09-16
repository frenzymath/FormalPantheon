import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletGrowth
import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletLocalAnchors
import PrimesRestrictedDigits.PrimeNumberTheorem.LocalDivisorTranslation
import PrimesRestrictedDigits.PrimeNumberTheorem.LocalLogDerivative

/-!
# Local zeros of nonprincipal Dirichlet L-functions

This file formalizes the nonprincipal specialization of
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 11, Lemma 11.1, p. 359. The local zero
sum uses the closed disk and analytic multiplicities.
-/

open Complex Metric Set

namespace PrimesRestrictedDigits

/-- The multiplicity-weighted zeros of a Dirichlet L-function in the closed
disk of radius `5 / 6` centered at `3 / 2 + I * t`. -/
noncomputable def dirichletLFunctionLocalZeroSum
    {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
    (t : Real) (s : Complex) : Complex :=
  ∑ᶠ rho : Complex,
    ((MeromorphicOn.divisor chi.LFunction
      (closedBall
        (((3 / 2 : Real) : Complex) + Complex.I * (t : Complex))
        (5 / 6 : Real)) rho : Int) : Complex) / (s - rho)

/-- The logarithmic derivative of a nonprincipal Dirichlet L-function is
approximated uniformly by the multiplicity-weighted zeros in its local closed
disk. This is the nonprincipal branch of
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 11, Lemma 11.1, p. 359. -/
theorem dirichletLFunction_logDeriv_localZeroSum_bound :
    ∃ C : Real, 0 < C ∧
      ∀ {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q),
        chi ≠ 1 →
        ∀ t sigma : Real,
          5 / 6 ≤ sigma →
          sigma ≤ 2 →
          chi.LFunction
            ((sigma : Complex) + Complex.I * (t : Complex)) ≠ 0 →
          norm
            (logDeriv chi.LFunction
                ((sigma : Complex) + Complex.I * (t : Complex)) -
              dirichletLFunctionLocalZeroSum chi t
                ((sigma : Complex) + Complex.I * (t : Complex))) ≤
            C * Real.log ((q : Real) * (|t| + 4)) := by
  refine ⟨696, by norm_num, ?_⟩
  intro q _ chi hchi t sigma hSigmaLower hSigmaUpper hs
  let c : Complex := ((3 / 2 : Real) : Complex) + Complex.I * t
  let s : Complex := (sigma : Complex) + Complex.I * t
  let f : Complex → Complex := fun w => chi.LFunction (w + c)
  let z : Complex := ((sigma - 3 / 2 : Real) : Complex)
  let tau : Real := |t| + 4
  let x : Real := (q : Real) * tau
  let M : Real := 2 * x
  let m : Real := 1 / 4
  have hqNat : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq : (1 : Real) ≤ q := by exact_mod_cast hqNat
  have hTauFour : 4 ≤ tau := by
    dsimp [tau]
    exact le_add_of_nonneg_left (abs_nonneg t)
  have hXFour : 4 ≤ x := by
    have hProduct : (1 : Real) * 4 ≤ (q : Real) * tau :=
      mul_le_mul hq hTauFour (by norm_num) (Nat.cast_nonneg q)
    simpa [x] using hProduct
  have hXPos : 0 < x := lt_of_lt_of_le (by norm_num) hXFour
  have hLAnalytic : AnalyticOnNhd Complex chi.LFunction Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (chi.differentiable_LFunction hchi)
  have hf : AnalyticOnNhd Complex f (closedBall 0 1) := by
    intro w _
    exact AnalyticAt.fun_comp (g := chi.LFunction)
      (f := fun u : Complex => u + c) (x := w)
      (hLAnalytic (w + c) (Set.mem_univ _)) (by fun_prop)
  have hM : 1 ≤ M := by
    dsimp [M]
    nlinarith
  have hm : 0 < m := by norm_num [m]
  have hmf : m ≤ ‖f 0‖ := by
    simpa [m, f, c] using
      one_fourth_le_norm_LFunction_three_halves_add_mul_I chi t
  have hf0 : f 0 ≠ 0 := by
    have : 0 < ‖f 0‖ := hm.trans_le hmf
    exact norm_pos_iff.mp this
  have hbound : ∀ u ∈ closedBall (0 : Complex) 1, ‖f u‖ ≤ M := by
    intro u hu
    have huNorm : norm u ≤ 1 := by
      simpa only [mem_closedBall, dist_zero_right] using hu
    simpa [f, c, M, x, tau, mul_assoc] using
      norm_LFunction_le_on_shifted_unitDisk chi hchi t huNorm
  have hratio : 1 < M / m := by
    dsimp [M, m]
    norm_num
    nlinarith
  have hz : ‖z‖ ≤ (2 / 3 : Real) := by
    simp only [z, norm_real, Real.norm_eq_abs]
    rw [abs_le]
    constructor <;> linarith
  have hzs : z + c = s := by
    dsimp [z, c, s]
    push_cast
    ring
  have hfz : f z ≠ 0 := by
    simpa [f, hzs] using hs
  have hLocal := norm_logDeriv_sub_localZeroSum_le
    hf hM hm hf0 hmf hbound hratio hz hfz
  have hLogDeriv : logDeriv f z = logDeriv chi.LFunction s := by
    change logDeriv (chi.LFunction ∘ fun w : Complex => w + c) z = _
    rw [logDeriv_comp (f := chi.LFunction)
      (g := fun w : Complex => w + c) (x := z)
      (chi.differentiable_LFunction hchi).differentiableAt (by fun_prop)]
    rw [hzs]
    simp
  have hfTarget : AnalyticOnNhd Complex f
      (closedBall 0 (5 / 6 : Real)) :=
    hf.mono (closedBall_subset_closedBall (by norm_num))
  have hLTarget : AnalyticOnNhd Complex chi.LFunction
      (closedBall c (5 / 6 : Real)) :=
    hLAnalytic.mono (Set.subset_univ _)
  have hSum :
      (∑ᶠ w : Complex,
        ((MeromorphicOn.divisor f
          (closedBall 0 (5 / 6 : Real)) w : Int) : Complex) / (z - w)) =
        dirichletLFunctionLocalZeroSum chi t s := by
    have hTranslate := finsum_divisor_add_shift_eq
      chi.LFunction c s (5 / 6 : Real)
      hfTarget.meromorphicOn hLTarget.meromorphicOn
    simpa [dirichletLFunctionLocalZeroSum, f, c, z, s] using hTranslate
  rw [hLogDeriv, hSum] at hLocal
  have hRatio : M / m = 8 * x := by
    dsimp [M, m]
    ring
  rw [hRatio] at hLocal
  have hEight : (8 : Real) ≤ x ^ 2 := by
    nlinarith [sq_nonneg (x - 4)]
  have hArg : (8 : Real) * x ≤ x ^ 3 := by
    calc
      (8 : Real) * x ≤ x ^ 2 * x :=
        mul_le_mul_of_nonneg_right hEight hXPos.le
      _ = x ^ 3 := by ring
  have hLog : Real.log (8 * x) ≤ 3 * Real.log x := by
    have h := Real.log_le_log (by positivity) hArg
    rw [Real.log_pow] at h
    norm_num at h ⊢
    exact h
  change ‖logDeriv chi.LFunction s -
      dirichletLFunctionLocalZeroSum chi t s‖ ≤
    696 * Real.log x
  calc
    ‖logDeriv chi.LFunction s -
        dirichletLFunctionLocalZeroSum chi t s‖ ≤
        232 * Real.log (8 * x) := hLocal
    _ ≤ 232 * (3 * Real.log x) :=
      mul_le_mul_of_nonneg_left hLog (by norm_num)
    _ = 696 * Real.log x := by ring

end PrimesRestrictedDigits
