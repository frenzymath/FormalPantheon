import BoundedGaps.BombieriVinogradov.Analytic.DirichletExplicitFormulaShallowCorrection
import BoundedGaps.BombieriVinogradov.Analytic.PrimitiveLFunctionZeroShell
import BoundedGaps.BombieriVinogradov.Analytic.RiemannZetaZeroShell

/-!
# Selected-height zero-sum transfer

This file closes the final good-height step in the proof of Koukoulopoulos
Theorem 11.3. After equation (11.7) has reduced to a primitive character, the
nontrivial-zero sum at a selected `U in [T,T+1]` is returned to the requested
height `T` at the explicit-formula error scale.

The selected-height clearance used on horizontal contour edges is not needed
for this finite shell estimate. Semantic review: `SEM-531`.
-/

namespace BoundedGaps.Maynard

open Complex Set
open scoped BigOperators

noncomputable section

/-- One absolute witness bounds the selected-height shell multiplicity for
every primitive character, including the modulus-one branch. -/
theorem
    exists_nat_sum_dirichletNontrivialZeroShellMultiplicity_of_isPrimitive_le :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (q : ℕ) [NeZero q]
        (chi : DirichletCharacter ℂ q), chi.IsPrimitive →
          ∀ (T U : ℝ), 2 ≤ T → U ∈ Set.Icc T (T + 1) →
            (∑ rho ∈
                dirichletNontrivialLFunctionZeroShellFinset chi T U,
              (analyticOrderNatAt
                (DirichletCharacter.LFunction chi) rho : ℝ)) ≤
              4 * (A : ℝ) * Real.log ((q : ℝ) * (T + 2)) := by
  obtain ⟨Ap, hAp, hprimitive⟩ :=
    exists_nat_sum_dirichletNontrivialZeroShellMultiplicity_primitive_le
  obtain ⟨Az, hAz, hzeta⟩ :=
    exists_nat_sum_dirichletNontrivialZeroShellMultiplicity_modOne_le
  let A := max Ap Az
  refine ⟨A, hAp.trans (Nat.le_max_left Ap Az), ?_⟩
  intro q _ chi hchi T U hT hU
  have hlogNonneg : 0 ≤ Real.log ((q : ℝ) * (T + 2)) := by
    apply Real.log_nonneg
    have hq : (1 : ℝ) ≤ q := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    nlinarith [mul_le_mul hq
      (show (1 : ℝ) ≤ T + 2 by linarith)
      (by norm_num : (0 : ℝ) ≤ 1) (by positivity : (0 : ℝ) ≤ q)]
  by_cases hqOne : q = 1
  · subst q
    have hchiOne : chi = (1 : DirichletCharacter ℂ 1) :=
      Subsingleton.elim _ _
    subst chi
    have hz := hzeta T U hT hU
    have hAzA : (Az : ℝ) ≤ A := by
      exact_mod_cast Nat.le_max_right Ap Az
    simpa only [Nat.cast_one, one_mul] using
      hz.trans (by nlinarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ T + 2)])
  · have hq : 1 < q := by
      have hqpos := Nat.pos_of_ne_zero (NeZero.ne q)
      omega
    have hp := hprimitive q hq chi hchi T U hT hU
    have hApA : (Ap : ℝ) ≤ A := by
      exact_mod_cast Nat.le_max_left Ap Az
    exact hp.trans (by nlinarith)

/-- The grouped nontrivial-zero sum at a selected good height differs from
the requested-height sum by at most `32*A` copies of the literal Theorem 11.3
error scale. -/
theorem
    exists_nat_norm_dirichletNontrivialZeroKernelSum_selected_sub_requested_le :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (q : ℕ) [NeZero q]
        (chi : DirichletCharacter ℂ q), chi.IsPrimitive →
          ∀ (x T U : ℝ), 2 ≤ T → T ≤ x →
            U ∈ Set.Icc T (T + 1) →
              ‖dirichletNontrivialZeroKernelSum chi x U -
                  dirichletNontrivialZeroKernelSum chi x T‖ ≤
                32 * (A : ℝ) *
                  dirichletExplicitFormulaErrorScale x q T := by
  obtain ⟨A, hA, hmass⟩ :=
    exists_nat_sum_dirichletNontrivialZeroShellMultiplicity_of_isPrimitive_le
  refine ⟨A, hA, ?_⟩
  intro q _ chi hchi x T U hT hTx hU
  let L : ℝ := Real.log ((q : ℝ) * x)
  let M : ℝ := Real.log ((q : ℝ) * (T + 2))
  have hx : 2 ≤ x := hT.trans hTx
  have hxpos : 0 < x := by linarith
  have hTpos : 0 < T := by linarith
  have hq : (1 : ℝ) ≤ q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq0 : (0 : ℝ) ≤ q := zero_le_one.trans hq
  have hqxPos : 0 < (q : ℝ) * x := mul_pos (by linarith) hxpos
  have hT2xSq : T + 2 ≤ x ^ 2 := by
    have hproduct : 0 ≤ (x - 2) * (x + 1) :=
      mul_nonneg (sub_nonneg.mpr hx) (by linarith)
    nlinarith
  have hqSq : (q : ℝ) ≤ (q : ℝ) ^ 2 := by
    nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hq)]
  have hscale : (q : ℝ) * (T + 2) ≤ ((q : ℝ) * x) ^ 2 := by
    calc
      (q : ℝ) * (T + 2) ≤ (q : ℝ) * x ^ 2 :=
        mul_le_mul_of_nonneg_left hT2xSq hq0
      _ ≤ (q : ℝ) ^ 2 * x ^ 2 :=
        mul_le_mul_of_nonneg_right hqSq (sq_nonneg x)
      _ = ((q : ℝ) * x) ^ 2 := by ring_nf
  have hMle : M ≤ 2 * L := by
    dsimp [M, L]
    calc
      Real.log ((q : ℝ) * (T + 2)) ≤
          Real.log (((q : ℝ) * x) ^ 2) :=
        Real.log_le_log (mul_pos (by linarith) (by linarith)) hscale
      _ = 2 * Real.log ((q : ℝ) * x) := by
        rw [Real.log_pow]
        norm_num
  have hLhalf : (1 / 2 : ℝ) ≤ L := by
    have htwo : (2 : ℝ) ≤ (q : ℝ) * x := by
      nlinarith [mul_le_mul hq hx (by norm_num : (0 : ℝ) ≤ 2) hq0]
    have hhalfTwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have h := Real.one_sub_inv_le_log_of_pos
        (show (0 : ℝ) < 2 by norm_num)
      norm_num at h ⊢
      exact h
    exact hhalfTwo.trans (by
      simpa [L] using Real.log_le_log (by norm_num) htwo)
  have hL0 : 0 ≤ L := by linarith
  have hMfour : M ≤ 4 * L ^ 2 := by
    have hLlinear : L ≤ 2 * L ^ 2 := by
      nlinarith [sq_nonneg (L - 1 / 2)]
    linarith
  have hkernel :=
    norm_dirichletNontrivialZeroKernelSum_sub_le_zeroShellMultiplicity
      chi hx hT hU
  have hshell := hmass q chi hchi T U hT hU
  have hfactor : 0 ≤ 2 * x / T := by positivity
  calc
    ‖dirichletNontrivialZeroKernelSum chi x U -
        dirichletNontrivialZeroKernelSum chi x T‖ ≤
        (2 * x / T) *
          (∑ rho ∈ dirichletNontrivialLFunctionZeroShellFinset chi T U,
            (analyticOrderNatAt
              (DirichletCharacter.LFunction chi) rho : ℝ)) := hkernel
    _ ≤ (2 * x / T) *
        (4 * (A : ℝ) * M) :=
      mul_le_mul_of_nonneg_left (by simpa [M] using hshell) hfactor
    _ = 8 * ((A : ℝ) * x / T) * M := by ring_nf
    _ ≤ 8 * ((A : ℝ) * x / T) * (4 * L ^ 2) := by
      exact mul_le_mul_of_nonneg_left hMfour (by positivity)
    _ = 32 * (A : ℝ) *
        dirichletExplicitFormulaErrorScale x q T := by
      rw [dirichletExplicitFormulaErrorScale]
      dsimp [L]
      ring_nf

end

end BoundedGaps.Maynard
