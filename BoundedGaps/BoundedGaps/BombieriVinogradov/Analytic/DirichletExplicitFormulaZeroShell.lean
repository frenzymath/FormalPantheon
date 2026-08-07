import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaHorizontalKernel
import BoundedGaps.BombieriVinogradov.Analytic.DirichletNontrivialZeroTransport

/-!
# Selected-height Dirichlet zero shells

The proof of Koukoulopoulos Theorem 11.3 first moves the contour at a good
height selected in `[T,T+1]`, then returns the nontrivial-zero sum to the
requested cutoff `T`. The exact intervening shell is open at `T` and closed at
the selected height.

This file owns the finite shell algebra and elementary modified-kernel bound.
The multiplicity estimates for the primitive and modulus-one branches remain
in separate files. Semantic review: `SEM-531`.
-/

namespace BoundedGaps.Maynard

open Complex Metric Set
open scoped BigOperators

noncomputable section

/-- The distinct nontrivial-zero locations present at cutoff `U` but absent
at cutoff `T`. Analytic multiplicity remains a separate summand weight. -/
noncomputable def dirichletNontrivialLFunctionZeroShellFinset
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (T U : ℝ) : Finset ℂ :=
  dirichletNontrivialLFunctionZerosFinset chi U \
    dirichletNontrivialLFunctionZerosFinset chi T

/-- On nonnegative nested cutoffs, shell membership is exactly
`T < |Im rho| <= U`. -/
@[simp] theorem mem_dirichletNontrivialLFunctionZeroShellFinset_iff
    {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    {T U : ℝ} (hT : 0 ≤ T) (hTU : T ≤ U) {rho : ℂ} :
    rho ∈ dirichletNontrivialLFunctionZeroShellFinset chi T U ↔
      IsDirichletNontrivialLFunctionZero chi rho ∧
        T < |rho.im| ∧ |rho.im| ≤ U := by
  rw [dirichletNontrivialLFunctionZeroShellFinset, Finset.mem_sdiff,
    mem_dirichletNontrivialLFunctionZerosFinset_iff,
    mem_dirichletNontrivialLFunctionZerosFinset_iff,
    abs_of_nonneg hT, abs_of_nonneg (hT.trans hTU)]
  constructor
  · rintro ⟨⟨hzero, hupper⟩, hnotLower⟩
    refine ⟨hzero, ?_, hupper⟩
    by_contra hlower
    exact hnotLower ⟨hzero, le_of_not_gt hlower⟩
  · rintro ⟨hzero, hlower, hupper⟩
    refine ⟨⟨hzero, hupper⟩, ?_⟩
    rintro ⟨_, hlower'⟩
    exact (not_lt_of_ge hlower') hlower

/-- The selected-minus-requested grouped kernel sum is exactly the shell sum.
The strict lower endpoint comes only from finite-set subtraction. -/
theorem dirichletNontrivialZeroKernelSum_sub_eq_sum_zeroShell
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (x : ℝ) {T U : ℝ} (hT : 0 ≤ T) (hTU : T ≤ U) :
    dirichletNontrivialZeroKernelSum chi x U -
        dirichletNontrivialZeroKernelSum chi x T =
      ∑ rho ∈ dirichletNontrivialLFunctionZeroShellFinset chi T U,
        (analyticOrderNatAt
          (DirichletCharacter.LFunction chi) rho : ℂ) *
            dirichletExplicitFormulaKernel x rho := by
  have hsubset :
      dirichletNontrivialLFunctionZerosFinset chi T ⊆
        dirichletNontrivialLFunctionZerosFinset chi U := by
    intro rho hrho
    rw [mem_dirichletNontrivialLFunctionZerosFinset_iff] at hrho ⊢
    refine ⟨hrho.1, ?_⟩
    rw [abs_of_nonneg (hT.trans hTU)]
    have hrhoT : |rho.im| ≤ T := by
      simpa [abs_of_nonneg hT] using hrho.2
    exact hrhoT.trans hTU
  rw [dirichletNontrivialZeroKernelSum,
    dirichletNontrivialZeroKernelSum,
    dirichletNontrivialLFunctionZeroShellFinset]
  exact (Finset.sum_sdiff_eq_sub hsubset).symm

/-- Open-critical-strip geometry places a zero with ordinate within one unit
of `t` in the closed radius-six disk centered at `2+i*t`. -/
theorem IsDirichletNontrivialLFunctionZero.dist_two_add_mul_I_le_six
    {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    {rho : ℂ} (hrho : IsDirichletNontrivialLFunctionZero chi rho)
    {t : ℝ} (hheight : |rho.im - t| ≤ 1) :
    dist rho ((2 : ℂ) + t * Complex.I) ≤ 6 := by
  have hxabs : |rho.re - 2| ≤ (2 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith [hrho.2.1, hrho.2.2]
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

/-- Every modified kernel in the shell has the sharp elementary envelope
`2*x/T` on the source range. -/
theorem norm_dirichletExplicitFormulaKernel_le_two_mul_x_div_of_mem_zeroShell
    {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    {x T U : ℝ} (hx : 2 ≤ x) (hT : 2 ≤ T) {rho : ℂ}
    (hrho : rho ∈
      dirichletNontrivialLFunctionZeroShellFinset chi T U) :
    ‖dirichletExplicitFormulaKernel x rho‖ ≤ 2 * x / T := by
  have hrhoU := (Finset.mem_sdiff.mp hrho).1
  have hzero :=
    (mem_dirichletNontrivialLFunctionZerosFinset_iff.mp hrhoU).1
  have hheight : T ≤ |rho.im| := by
    have hrhoT := (Finset.mem_sdiff.mp hrho).2
    by_contra hnot
    apply hrhoT
    rw [mem_dirichletNontrivialLFunctionZerosFinset_iff,
      abs_of_nonneg (show 0 ≤ T by linarith)]
    exact ⟨hzero, le_of_not_ge hnot⟩
  have hkernel :
      ‖dirichletExplicitFormulaKernel x rho‖ ≤
        (x ^ rho.re + 1) / T := by
    simpa only [Complex.re_add_im] using
      (norm_dirichletExplicitFormulaKernel_horizontal_le
        (x := x) (sigma := rho.re) (t := rho.im) (T := T)
        (by linarith) (by linarith) hheight)
  have hpow : x ^ rho.re ≤ x := by
    calc
      x ^ rho.re ≤ x ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hzero.2.2.le
      _ = x := Real.rpow_one x
  have hnum : x ^ rho.re + 1 ≤ 2 * x := by
    linarith [show (1 : ℝ) ≤ x by linarith]
  exact hkernel.trans
    (div_le_div_of_nonneg_right hnum (show 0 ≤ T by linarith))

/-- The norm of the grouped shell is bounded by the kernel envelope times
the complete analytic multiplicity in that shell. -/
theorem
    norm_dirichletNontrivialZeroKernelSum_sub_le_zeroShellMultiplicity
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {x T U : ℝ} (hx : 2 ≤ x) (hT : 2 ≤ T)
    (hU : U ∈ Set.Icc T (T + 1)) :
    ‖dirichletNontrivialZeroKernelSum chi x U -
        dirichletNontrivialZeroKernelSum chi x T‖ ≤
      (2 * x / T) *
        ∑ rho ∈ dirichletNontrivialLFunctionZeroShellFinset chi T U,
          (analyticOrderNatAt
            (DirichletCharacter.LFunction chi) rho : ℝ) := by
  rw [dirichletNontrivialZeroKernelSum_sub_eq_sum_zeroShell
    chi x (show 0 ≤ T by linarith) hU.1]
  calc
    ‖∑ rho ∈ dirichletNontrivialLFunctionZeroShellFinset chi T U,
        (analyticOrderNatAt
          (DirichletCharacter.LFunction chi) rho : ℂ) *
            dirichletExplicitFormulaKernel x rho‖ ≤
        ∑ rho ∈ dirichletNontrivialLFunctionZeroShellFinset chi T U,
          ‖(analyticOrderNatAt
            (DirichletCharacter.LFunction chi) rho : ℂ) *
              dirichletExplicitFormulaKernel x rho‖ := norm_sum_le _ _
    _ ≤ ∑ rho ∈ dirichletNontrivialLFunctionZeroShellFinset chi T U,
        (analyticOrderNatAt
          (DirichletCharacter.LFunction chi) rho : ℝ) *
            (2 * x / T) := by
      apply Finset.sum_le_sum
      intro rho hrho
      rw [norm_mul, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left
        (norm_dirichletExplicitFormulaKernel_le_two_mul_x_div_of_mem_zeroShell
          hx hT hrho) (Nat.cast_nonneg _)
    _ = (2 * x / T) *
        ∑ rho ∈ dirichletNontrivialLFunctionZeroShellFinset chi T U,
          (analyticOrderNatAt
            (DirichletCharacter.LFunction chi) rho : ℝ) := by
      rw [← Finset.sum_mul]
      ring

end

end BoundedGaps.Maynard
