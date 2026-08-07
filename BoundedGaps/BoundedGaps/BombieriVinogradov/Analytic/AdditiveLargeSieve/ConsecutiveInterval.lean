import BoundedGaps.BombieriVinogradov.Analytic.CosecantHilbert
import BoundedGaps.BombieriVinogradov.Analytic.AdditiveLargeSieve.FiniteDuality
import BoundedGaps.BombieriVinogradov.Analytic.AdditiveLargeSieve.ConsecutiveIntervalKernel

/-!
# The additive large sieve on a consecutive interval

This file proves the generic Montgomery--Vaughan additive large-sieve
inequality from the exact SEM-448 interval kernel, the coefficient-one
cosecant Hilbert inequality of SEM-447, and finite transpose duality.
-/

open scoped BigOperators ComplexConjugate
open Metric

namespace BoundedGaps.Maynard

noncomputable section

open AdditiveLargeSieve

private noncomputable def phase (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

private def lift (x : UnitAddCircle) : ℝ :=
  AddCircle.equivIco 1 (0 : ℝ) x

private lemma coe_lift (x : UnitAddCircle) : (lift x : UnitAddCircle) = x := by
  exact AddCircle.coe_equivIco

private lemma phase_norm (x : ℝ) : ‖phase x‖ = 1 := by
  rw [phase]
  exact Complex.norm_exp_ofReal_mul_I _

private lemma char_coe_phase (x : ℝ) (n : ℕ) :
    unitAddCircleAddChar (n • (x : UnitAddCircle)) = phase ((n : ℝ) * x) := by
  unfold unitAddCircleAddChar phase
  change Circle.coeHom (AddCircle.toCircle (n • (x : UnitAddCircle))) = _
  rw [AddCircle.toCircle_nsmul, map_pow, AddCircle.toCircle_apply_mk]
  rw [show Circle.coeHom (Circle.exp (2 * Real.pi / 1 * x)) =
      Complex.exp ((2 * Real.pi / 1 * x : ℝ) * Complex.I) by rfl]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring_nf

private lemma char_lift_phase (x : UnitAddCircle) (n : ℕ) :
    unitAddCircleAddChar (n • x) = phase ((n : ℝ) * lift x) := by
  calc
    unitAddCircleAddChar (n • x) =
        unitAddCircleAddChar (n • (lift x : UnitAddCircle)) := by
      rw [coe_lift]
    _ = phase ((n : ℝ) * lift x) := char_coe_phase (lift x) n

private lemma phase_sub_factor (a x y : ℝ) :
    phase (a * (x - y)) = phase (a * x) * star (phase (a * y)) := by
  unfold phase
  simp only [Complex.star_def]
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  push_cast
  simp [Complex.conj_ofReal, Complex.conj_I]
  rw [show (starRingEnd ℂ) (2 : ℂ) = 2 by
    rw [map_ofNat]]
  ring_nf

private lemma sum_phase_norm_sq_expand
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ℕ) (y : ι → ℝ) (v : ι → ℂ) :
    (((∑ n ∈ S, ‖∑ r, phase ((n : ℝ) * y r) * v r‖ ^ 2 : ℝ) : ℂ)) =
      ∑ r, ∑ s,
        v r * star (v s) *
          ∑ n ∈ S, phase ((n : ℝ) * (y r - y s)) := by
  calc
    (((∑ n ∈ S, ‖∑ r, phase ((n : ℝ) * y r) * v r‖ ^ 2 : ℝ) : ℂ)) =
        ∑ n ∈ S,
          (∑ r, phase ((n : ℝ) * y r) * v r) *
            star (∑ s, phase ((n : ℝ) * y s) * v s) := by
      rw [Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro n _
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
      rw [Complex.star_def]
      -- commutativity changes `star z * z` to `z * star z`
      ring
    _ = ∑ n ∈ S, ∑ r, ∑ s,
          (phase ((n : ℝ) * y r) * v r) *
            star (phase ((n : ℝ) * y s) * v s) := by
      simp only [Complex.star_def, map_sum, star_mul]
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      simp only [map_mul]
      ring
    _ = ∑ r, ∑ s,
          v r * star (v s) *
            ∑ n ∈ S, phase ((n : ℝ) * (y r - y s)) := by
      simp only [Complex.star_def]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      simp only [map_mul]
      have hphase := phase_sub_factor (n : ℝ) (y r) (y s)
      simp only [Complex.star_def] at hphase
      calc
        phase ((n : ℝ) * y r) * v r *
            ((starRingEnd ℂ) (phase ((n : ℝ) * y s)) *
              (starRingEnd ℂ) (v s)) =
            (phase ((n : ℝ) * y r) *
              (starRingEnd ℂ) (phase ((n : ℝ) * y s))) *
              (v r * (starRingEnd ℂ) (v s)) := by ring
        _ = phase ((n : ℝ) * (y r - y s)) *
              (v r * (starRingEnd ℂ) (v s)) := by rw [← hphase]
        _ = v r * (starRingEnd ℂ) (v s) *
              phase ((n : ℝ) * (y r - y s)) := by ring

private lemma sum_phase_diag (S : Finset ℕ) (y : ℝ) :
    ∑ n ∈ S, phase ((n : ℝ) * (y - y)) = (S.card : ℂ) := by
  simp [phase]

private lemma sum_phase_norm_sq_eq_diag_add_offDiagonal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset ℕ) (y : ι → ℝ) (v : ι → ℂ) :
    (((∑ n ∈ S, ‖∑ r, phase ((n : ℝ) * y r) * v r‖ ^ 2 : ℝ) : ℂ)) =
      ((S.card : ℝ) * ∑ r, ‖v r‖ ^ 2 : ℝ) +
        ∑ r, ∑ s ∈ Finset.univ.erase r,
          v r * star (v s) *
            ∑ n ∈ S, phase ((n : ℝ) * (y r - y s)) := by
  rw [sum_phase_norm_sq_expand S y v]
  calc
    (∑ r, ∑ s,
        v r * star (v s) *
          ∑ n ∈ S, phase ((n : ℝ) * (y r - y s))) =
        ∑ r, (v r * star (v r) *
            ∑ n ∈ S, phase ((n : ℝ) * (y r - y r)) +
          ∑ s ∈ Finset.univ.erase r,
            v r * star (v s) *
              ∑ n ∈ S, phase ((n : ℝ) * (y r - y s))) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [add_comm]
      exact (Finset.sum_erase_add Finset.univ
        (fun s => v r * star (v s) *
          ∑ n ∈ S, phase ((n : ℝ) * (y r - y s)))
        (Finset.mem_univ r)).symm
    _ = ∑ r, (((S.card : ℝ) * ‖v r‖ ^ 2 : ℝ) : ℂ) +
          ∑ r, ∑ s ∈ Finset.univ.erase r,
            v r * star (v s) *
              ∑ n ∈ S, phase ((n : ℝ) * (y r - y s)) := by
      rw [Finset.sum_add_distrib]
      apply congrArg (fun z : ℂ => z + _)
      apply Finset.sum_congr rfl
      intro r _
      rw [sum_phase_diag]
      simp only [Complex.star_def, RCLike.mul_conj]
      push_cast
      exact mul_comm _ _
    _ = (((S.card : ℝ) * ∑ r, ‖v r‖ ^ 2 : ℝ) : ℂ) +
          ∑ r, ∑ s ∈ Finset.univ.erase r,
            v r * star (v s) *
              ∑ n ∈ S, phase ((n : ℝ) * (y r - y s)) := by
      congr 1
      push_cast
      rw [Finset.mul_sum]

private lemma sum_phase_Ioc_eq_cosecant
    (t : ℝ) (ht : (t : UnitAddCircle) ≠ 0) (m0 N : ℕ) :
    (∑ n ∈ Finset.Ioc m0 (m0 + N), phase ((n : ℝ) * t)) =
      Complex.I / 2 *
        (phase (((m0 : ℝ) + 1 / 2) * t) -
          phase ((((m0 + N : ℕ) : ℝ) + 1 / 2) * t)) *
        (((Real.sin (Real.pi * t))⁻¹ : ℝ) : ℂ) := by
  calc
    (∑ n ∈ Finset.Ioc m0 (m0 + N), phase ((n : ℝ) * t)) =
        ∑ n ∈ Finset.Ioc m0 (m0 + N),
          unitAddCircleAddChar (n • (t : UnitAddCircle)) := by
      apply Finset.sum_congr rfl
      intro n _
      exact (char_coe_phase t n).symm
    _ = Complex.I / 2 *
        (Complex.exp (2 * Real.pi * Complex.I *
          (((m0 : ℝ) + 1 / 2) * t)) -
         Complex.exp (2 * Real.pi * Complex.I *
          ((((m0 + N : ℕ) : ℝ) + 1 / 2) * t))) *
        (((Real.sin (Real.pi * t))⁻¹ : ℝ) : ℂ) :=
      sum_unitAddCircleAddChar_Ioc_eq_cosecant t ht m0 N
    _ = _ := by
      simp only [phase]
      congr 3 <;> push_cast <;> ring_nf

private lemma offDiagonal_eq_endpoint_forms
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y : ι → ℝ) (v : ι → ℂ)
    (hneq : ∀ r s, r ≠ s →
      ((y r - y s : ℝ) : UnitAddCircle) ≠ 0)
    (m0 N : ℕ) :
    (∑ r, ∑ s ∈ Finset.univ.erase r,
      v r * star (v s) *
        ∑ n ∈ Finset.Ioc m0 (m0 + N),
          phase ((n : ℝ) * (y r - y s))) =
      Complex.I / 2 *
        (cosecantBilinearForm y
            (fun r => v r * phase (((m0 : ℝ) + 1 / 2) * y r)) -
          cosecantBilinearForm y
            (fun r => v r *
              phase ((((m0 + N : ℕ) : ℝ) + 1 / 2) * y r))) := by
  rw [cosecantBilinearForm, cosecantBilinearForm]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hrs : r ≠ s := Ne.symm (Finset.ne_of_mem_erase hs)
  rw [sum_phase_Ioc_eq_cosecant (y r - y s) (hneq r s hrs)]
  rw [phase_sub_factor, phase_sub_factor]
  simp only [star_mul']
  ring

private lemma phase_twist_energy
    {ι : Type*} [Fintype ι]
    (a : ℝ) (y : ι → ℝ) (v : ι → ℂ) :
    (∑ r, ‖v r * phase (a * y r)‖ ^ 2) = ∑ r, ‖v r‖ ^ 2 := by
  apply Finset.sum_congr rfl
  intro r _
  rw [Complex.norm_mul, phase_norm, mul_one]

private lemma norm_offDiagonal_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r s, r ≠ s →
      δ ≤ dist (y r : UnitAddCircle) (y s : UnitAddCircle))
    (v : ι → ℂ) (m0 N : ℕ) :
    ‖∑ r, ∑ s ∈ Finset.univ.erase r,
      v r * star (v s) *
        ∑ n ∈ Finset.Ioc m0 (m0 + N),
          phase ((n : ℝ) * (y r - y s))‖ ≤
      δ⁻¹ * ∑ r, ‖v r‖ ^ 2 := by
  have hneq : ∀ r s, r ≠ s →
      ((y r - y s : ℝ) : UnitAddCircle) ≠ 0 := by
    intro r s hrs
    change (y r : UnitAddCircle) - (y s : UnitAddCircle) ≠ 0
    exact sub_ne_zero.mpr (dist_pos.mp (hδ.trans_le (hsep r s hrs)))
  rw [offDiagonal_eq_endpoint_forms y v hneq m0 N]
  let u₀ : ι → ℂ :=
    fun r => v r * phase (((m0 : ℝ) + 1 / 2) * y r)
  let u₁ : ι → ℂ :=
    fun r => v r * phase ((((m0 + N : ℕ) : ℝ) + 1 / 2) * y r)
  have h₀ := norm_cosecantBilinearForm_le y hδ hsep u₀
  have h₁ := norm_cosecantBilinearForm_le y hδ hsep u₁
  have he₀ : (∑ r, ‖u₀ r‖ ^ 2) = ∑ r, ‖v r‖ ^ 2 := by
    exact phase_twist_energy _ y v
  have he₁ : (∑ r, ‖u₁ r‖ ^ 2) = ∑ r, ‖v r‖ ^ 2 := by
    exact phase_twist_energy _ y v
  calc
    ‖Complex.I / 2 *
        (cosecantBilinearForm y u₀ - cosecantBilinearForm y u₁)‖ =
        (1 / 2 : ℝ) *
          ‖cosecantBilinearForm y u₀ - cosecantBilinearForm y u₁‖ := by
      rw [Complex.norm_mul, norm_div, Complex.norm_I]
      norm_num
    _ ≤ (1 / 2 : ℝ) *
        (‖cosecantBilinearForm y u₀‖ +
          ‖cosecantBilinearForm y u₁‖) := by
      exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
    _ ≤ (1 / 2 : ℝ) *
        (δ⁻¹ * ∑ r, ‖v r‖ ^ 2 + δ⁻¹ * ∑ r, ‖v r‖ ^ 2) := by
      gcongr
      · simpa only [he₀] using h₀
      · simpa only [he₁] using h₁
    _ = δ⁻¹ * ∑ r, ‖v r‖ ^ 2 := by ring

private lemma sum_phase_norm_sq_Ioc_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r s, r ≠ s →
      δ ≤ dist (y r : UnitAddCircle) (y s : UnitAddCircle))
    (m0 N : ℕ) (v : ι → ℂ) :
    (∑ n ∈ Finset.Ioc m0 (m0 + N),
      ‖∑ r, phase ((n : ℝ) * y r) * v r‖ ^ 2) ≤
      ((N : ℝ) + δ⁻¹) * ∑ r, ‖v r‖ ^ 2 := by
  let S : Finset ℕ := Finset.Ioc m0 (m0 + N)
  let E : ℝ := ∑ r, ‖v r‖ ^ 2
  let O : ℂ := ∑ r, ∑ s ∈ Finset.univ.erase r,
    v r * star (v s) *
      ∑ n ∈ S, phase ((n : ℝ) * (y r - y s))
  have hexpand :
      (((∑ n ∈ S, ‖∑ r, phase ((n : ℝ) * y r) * v r‖ ^ 2 : ℝ) : ℂ)) =
        ((S.card : ℝ) * E : ℝ) + O := by
    exact sum_phase_norm_sq_eq_diag_add_offDiagonal S y v
  have hre := congrArg Complex.re hexpand
  have hre' :
      (∑ n ∈ S, ‖∑ r, phase ((n : ℝ) * y r) * v r‖ ^ 2) =
        (S.card : ℝ) * E + O.re := by
    simpa only [Complex.add_re, Complex.ofReal_re] using hre
  have hcard : (S.card : ℝ) = N := by
    dsimp only [S]
    rw [Nat.card_Ioc]
    norm_num
  have hO : ‖O‖ ≤ δ⁻¹ * E := by
    exact norm_offDiagonal_le y hδ hsep v m0 N
  calc
    (∑ n ∈ Finset.Ioc m0 (m0 + N),
        ‖∑ r, phase ((n : ℝ) * y r) * v r‖ ^ 2) =
        (N : ℝ) * E + O.re := by rw [hre', hcard]
    _ ≤ (N : ℝ) * E + ‖O‖ :=
      add_le_add_right (Complex.re_le_norm O) _
    _ ≤ (N : ℝ) * E + δ⁻¹ * E :=
      add_le_add_right hO _
    _ = ((N : ℝ) + δ⁻¹) * ∑ r, ‖v r‖ ^ 2 := by
      dsimp only [E]
      ring

/-- The additive large sieve for a finite family of points of the unit
circle separated by at least `delta`, on the interval `m0 < n <= m0 + N`.
The coefficient is exactly `N + delta^(-1)`. -/
theorem sum_norm_sq_unitAddCircleAddChar_Ioc_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → UnitAddCircle) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r s, r ≠ s → δ ≤ dist (x r) (x s))
    (m0 N : ℕ) (c : ℕ → ℂ) :
    (∑ r, ‖∑ n ∈ Finset.Ioc m0 (m0 + N),
      c n * unitAddCircleAddChar (n • x r)‖ ^ 2) ≤
      ((N : ℝ) + δ⁻¹) *
        ∑ n ∈ Finset.Ioc m0 (m0 + N), ‖c n‖ ^ 2 := by
  classical
  let S : Finset ℕ := Finset.Ioc m0 (m0 + N)
  let y : ι → ℝ := fun r => lift (x r)
  let C : ι → {n : ℕ // n ∈ S} → ℂ :=
    fun r n => unitAddCircleAddChar (n.1 • x r)
  let w : {n : ℕ // n ∈ S} → ℂ := fun n => c n.1
  have hsep' : ∀ r s, r ≠ s →
      δ ≤ dist (y r : UnitAddCircle) (y s : UnitAddCircle) := by
    intro r s hrs
    simpa only [y, coe_lift] using hsep r s hrs
  have hA : 0 ≤ (N : ℝ) + δ⁻¹ :=
    add_nonneg (Nat.cast_nonneg N) (inv_nonneg.mpr hδ.le)
  have hdual : ∀ v : ι → ℂ,
      (∑ n : {n : ℕ // n ∈ S}, ‖∑ r, C r n * v r‖ ^ 2) ≤
        ((N : ℝ) + δ⁻¹) * ∑ r, ‖v r‖ ^ 2 := by
    intro v
    dsimp only [C]
    rw [Finset.sum_coe_sort S
      (fun n : ℕ => ‖∑ r, unitAddCircleAddChar (n • x r) * v r‖ ^ 2)]
    simpa only [S, y, char_lift_phase] using
      sum_phase_norm_sq_Ioc_le y hδ hsep' m0 N v
  have htranspose := finite_transpose_l2_bound C hA hdual w
  dsimp only [C, w] at htranspose
  have hinner (r : ι) :
      (∑ n : {n : ℕ // n ∈ S},
        unitAddCircleAddChar (n.1 • x r) * c n.1) =
        ∑ n ∈ S, unitAddCircleAddChar (n • x r) * c n :=
    Finset.sum_coe_sort S
      (fun n : ℕ => unitAddCircleAddChar (n • x r) * c n)
  simp_rw [hinner] at htranspose
  rw [Finset.sum_coe_sort S (fun n : ℕ => ‖c n‖ ^ 2)] at htranspose
  simpa only [S, mul_comm] using htranspose

end

end BoundedGaps.Maynard
