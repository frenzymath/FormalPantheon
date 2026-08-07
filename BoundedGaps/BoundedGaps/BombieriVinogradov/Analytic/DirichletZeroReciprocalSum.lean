import BoundedGaps.BombieriVinogradov.Analytic.DirichletZeroWindowMultiplicity
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Reciprocal-height Dirichlet zero multiplicity

The proof of `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 121--
122, sums equation (12.9) with weight `1/(1+|gamma|)` and invokes Lemma
11.4(a). This file supplies the corresponding grouped analytic-multiplicity
bound. The analogous zeta summation appears explicitly on printed p. 89.

Semantic review: `SEM-537`.
-/

namespace BoundedGaps.Maynard

open Complex Set
open scoped BigOperators

noncomputable section

private local instance conductorNeZero
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) :
    NeZero chi.conductor :=
  ⟨chi.conductor_ne_zero⟩

/-- The analytic multiplicity of every nontrivial zero up to height `T`,
weighted by the reciprocal source envelope `1/(1+|Im(rho)|)`. -/
noncomputable def dirichletNontrivialZeroReciprocalMultiplicitySum
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (T : ℝ) : ℝ :=
  ∑ rho ∈ dirichletNontrivialLFunctionZerosFinset chi T,
    (analyticOrderNatAt
      (DirichletCharacter.LFunction chi) rho : ℝ) /
        (1 + |rho.im|)

/-- Passage to the primitive inducer preserves the complete weighted sum. -/
theorem
    dirichletNontrivialZeroReciprocalMultiplicitySum_eq_inducingPrimitive
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (T : ℝ) :
    dirichletNontrivialZeroReciprocalMultiplicitySum chi T =
      dirichletNontrivialZeroReciprocalMultiplicitySum
        chi.primitiveCharacter T := by
  classical
  rw [dirichletNontrivialZeroReciprocalMultiplicitySum,
    dirichletNontrivialZeroReciprocalMultiplicitySum,
    dirichletNontrivialLFunctionZerosFinset_eq_inducingPrimitive chi T]
  apply Finset.sum_congr rfl
  intro rho hrho
  have hzero :=
    (mem_dirichletNontrivialLFunctionZerosFinset_iff.mp hrho).1
  have hrhoOne : rho ≠ 1 := by
    intro hrho
    have hre := congrArg Complex.re hrho
    norm_num at hre
    linarith [hzero.2.2]
  rw [analyticOrderNatAt_LFunction_eq_inducingPrimitive_of_re_pos_of_guard
    chi (.inr hrhoOne) hzero.2.1]

private theorem sum_range_inv_nat_add_one_eq_harmonic (N : ℕ) :
    (∑ n ∈ Finset.range N, (((n + 1 : ℕ) : ℝ))⁻¹) =
      (harmonic N : ℝ) := by
  induction N with
  | zero => simp [harmonic]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, harmonic_succ]
      simp only [Rat.cast_add, Rat.cast_inv, Rat.cast_natCast]

private theorem
    exists_nat_dirichletNontrivialZeroReciprocalMultiplicitySum_le_of_isPrimitive :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (q : ℕ) [NeZero q]
        (chi : DirichletCharacter ℂ q), chi.IsPrimitive →
          ∀ T : ℝ, 2 ≤ T →
            dirichletNontrivialZeroReciprocalMultiplicitySum chi T ≤
              8 * (A : ℝ) *
                Real.log ((q : ℝ) * (T + 2)) ^ 2 := by
  obtain ⟨A, hA, hwindow⟩ :=
    exists_nat_sum_dirichletNontrivialZeroWindowMultiplicity_of_isPrimitive_le
  refine ⟨A, hA, ?_⟩
  intro q _ chi hchi T hT
  let S := dirichletNontrivialLFunctionZerosFinset chi T
  let N := ⌊T⌋₊ + 1
  let L := Real.log ((q : ℝ) * (T + 2))
  let g : ℂ → ℕ := fun rho => ⌊|rho.im|⌋₊
  let m : ℂ → ℝ := fun rho =>
    analyticOrderNatAt (DirichletCharacter.LFunction chi) rho
  have hT0 : 0 ≤ T := by linarith
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hq0 : (0 : ℝ) ≤ q := zero_le_one.trans hq
  have hscaleFour : (4 : ℝ) ≤ (q : ℝ) * (T + 2) := by
    nlinarith [mul_le_mul hq
      (show (4 : ℝ) ≤ T + 2 by linarith)
      (by norm_num : (0 : ℝ) ≤ 4) hq0]
  have hLOne : (1 : ℝ) ≤ L := by
    have hlogFour : (1 : ℝ) < Real.log 4 := by
      rw [Real.log_four_eq]
      nlinarith [Real.log_two_gt_d9]
    exact hlogFour.le.trans
      (Real.log_le_log (by norm_num) (by simpa [L] using hscaleFour))
  have hmaps : ∀ rho ∈ S, g rho ∈ Finset.range N := by
    intro rho hrho
    have hheight :=
      (mem_dirichletNontrivialLFunctionZerosFinset_iff.mp hrho).2
    rw [abs_of_nonneg hT0] at hheight
    rw [Finset.mem_range]
    have hfloor : ⌊|rho.im|⌋₊ ≤ ⌊T⌋₊ :=
      Nat.floor_mono hheight
    simpa [g, N] using Nat.lt_succ_of_le hfloor
  have hnT : ∀ n ∈ Finset.range N, (n : ℝ) ≤ T := by
    intro n hn
    have hnNat : n ≤ ⌊T⌋₊ := by
      simpa [N] using Nat.le_of_lt_succ (Finset.mem_range.mp hn)
    exact (Nat.cast_le.mpr hnNat).trans (Nat.floor_le hT0)
  have hwindowScale : ∀ n ∈ Finset.range N,
      Real.log ((q : ℝ) * ((n : ℝ) + 2)) ≤ L := by
    intro n hn
    have hn := hnT n hn
    dsimp [L]
    apply Real.log_le_log (mul_pos (by linarith) (by positivity))
    exact mul_le_mul_of_nonneg_left (by linarith) hq0
  have hfiberMass : ∀ n ∈ Finset.range N,
      (∑ rho ∈ S with g rho = n, m rho) ≤
        4 * (A : ℝ) * L := by
    intro n hn
    let F := S.filter fun rho => g rho = n
    let Fplus := F.filter fun rho => 0 ≤ rho.im
    let Fminus := F.filter fun rho => ¬ 0 ≤ rho.im
    have hplusSubset : Fplus ⊆
        dirichletNontrivialLFunctionZeroWindowFinset chi (n : ℝ) := by
      intro rho hrho
      have hrho' := Finset.mem_filter.mp hrho
      have hF := Finset.mem_filter.mp hrho'.1
      have hzero :=
        (mem_dirichletNontrivialLFunctionZerosFinset_iff.mp hF.1).1
      have hfloor := hF.2
      have him := hrho'.2
      have hlower : (n : ℝ) ≤ |rho.im| := by
        rw [← hfloor]
        exact Nat.floor_le (abs_nonneg rho.im)
      have hupper : |rho.im| < (n : ℝ) + 1 := by
        have h := Nat.lt_floor_add_one |rho.im|
        have hfloor' : ⌊|rho.im|⌋₊ = n := by
          simpa [g] using hfloor
        rw [hfloor'] at h
        simpa using h
      rw [mem_dirichletNontrivialLFunctionZeroWindowFinset_iff]
      refine ⟨hzero, ?_⟩
      rw [abs_of_nonneg him] at hlower hupper
      rw [abs_le]
      constructor <;> linarith
    have hminusSubset : Fminus ⊆
        dirichletNontrivialLFunctionZeroWindowFinset chi (-(n : ℝ)) := by
      intro rho hrho
      have hrho' := Finset.mem_filter.mp hrho
      have hF := Finset.mem_filter.mp hrho'.1
      have hzero :=
        (mem_dirichletNontrivialLFunctionZerosFinset_iff.mp hF.1).1
      have hfloor := hF.2
      have him : rho.im ≤ 0 := le_of_not_ge hrho'.2
      have hlower : (n : ℝ) ≤ |rho.im| := by
        rw [← hfloor]
        exact Nat.floor_le (abs_nonneg rho.im)
      have hupper : |rho.im| < (n : ℝ) + 1 := by
        have h := Nat.lt_floor_add_one |rho.im|
        have hfloor' : ⌊|rho.im|⌋₊ = n := by
          simpa [g] using hfloor
        rw [hfloor'] at h
        simpa using h
      rw [mem_dirichletNontrivialLFunctionZeroWindowFinset_iff]
      refine ⟨hzero, ?_⟩
      rw [abs_of_nonpos him] at hlower hupper
      rw [abs_le]
      constructor <;> linarith
    have hplus : (∑ rho ∈ Fplus, m rho) ≤
        ∑ rho ∈ dirichletNontrivialLFunctionZeroWindowFinset chi (n : ℝ),
          m rho :=
      Finset.sum_le_sum_of_subset_of_nonneg hplusSubset
        (fun rho _ _ => by simp [m])
    have hminus : (∑ rho ∈ Fminus, m rho) ≤
        ∑ rho ∈
          dirichletNontrivialLFunctionZeroWindowFinset chi (-(n : ℝ)),
            m rho :=
      Finset.sum_le_sum_of_subset_of_nonneg hminusSubset
        (fun rho _ _ => by simp [m])
    have hwindowPlus := hwindow q chi hchi (n : ℝ)
    have hwindowMinus := hwindow q chi hchi (-(n : ℝ))
    have hlog := hwindowScale n hn
    have hwindowPlus' :
        (∑ rho ∈
            dirichletNontrivialLFunctionZeroWindowFinset chi (n : ℝ),
          m rho) ≤
          2 * (A : ℝ) *
            Real.log ((q : ℝ) * ((n : ℝ) + 2)) := by
      simpa [m, abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) by positivity)] using
        hwindowPlus
    have hplusBound : (∑ rho ∈ Fplus, m rho) ≤
        2 * (A : ℝ) * L := by
      exact hplus.trans (hwindowPlus'.trans
        (mul_le_mul_of_nonneg_left hlog (by positivity)))
    have hminusBound : (∑ rho ∈ Fminus, m rho) ≤
        2 * (A : ℝ) * L := by
      have hwindowMinus' :
          (∑ rho ∈
              dirichletNontrivialLFunctionZeroWindowFinset chi (-(n : ℝ)),
            m rho) ≤
            2 * (A : ℝ) *
              Real.log ((q : ℝ) * ((n : ℝ) + 2)) := by
        simpa [m, abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) by positivity)] using
          hwindowMinus
      exact hminus.trans (hwindowMinus'.trans
        (mul_le_mul_of_nonneg_left hlog (by positivity)))
    have hsplit := Finset.sum_filter_add_sum_filter_not
      F (fun rho => 0 ≤ rho.im) m
    change (∑ rho ∈ F, m rho) ≤ 4 * (A : ℝ) * L
    rw [← hsplit]
    linarith
  have hfiberWeight : ∀ n ∈ Finset.range N,
      (∑ rho ∈ S with g rho = n,
        m rho / (1 + |rho.im|)) ≤
          (4 * (A : ℝ) * L) * (((n + 1 : ℕ) : ℝ))⁻¹ := by
    intro n hn
    calc
      (∑ rho ∈ S with g rho = n,
          m rho / (1 + |rho.im|)) ≤
          ∑ rho ∈ S with g rho = n,
            m rho * (((n + 1 : ℕ) : ℝ))⁻¹ := by
        apply Finset.sum_le_sum
        intro rho hrho
        have hfloor := (Finset.mem_filter.mp hrho).2
        have hnle : (n : ℝ) ≤ |rho.im| := by
          rw [← hfloor]
          exact Nat.floor_le (abs_nonneg rho.im)
        have hden : ((n + 1 : ℕ) : ℝ) ≤ 1 + |rho.im| := by
          norm_num only [Nat.cast_add, Nat.cast_one]
          linarith
        have hinv : (1 + |rho.im|)⁻¹ ≤
            (((n + 1 : ℕ) : ℝ))⁻¹ := by
          simpa [one_div] using one_div_le_one_div_of_le
            (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ)) hden
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = (∑ rho ∈ S with g rho = n, m rho) *
          (((n + 1 : ℕ) : ℝ))⁻¹ := by
        rw [Finset.sum_mul]
      _ ≤ (4 * (A : ℝ) * L) * (((n + 1 : ℕ) : ℝ))⁻¹ :=
        mul_le_mul_of_nonneg_right (hfiberMass n hn) (by positivity)
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := S) (t := Finset.range N) (g := g) hmaps
    (fun rho => m rho / (1 + |rho.im|))
  have hNreal : (N : ℝ) ≤ T + 1 := by
    dsimp [N]
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith [Nat.floor_le hT0]
  have hNpos : (0 : ℝ) < N := by positivity
  have hNscale : (N : ℝ) ≤ (q : ℝ) * (T + 2) := by
    calc
      (N : ℝ) ≤ T + 1 := hNreal
      _ ≤ T + 2 := by linarith
      _ = 1 * (T + 2) := by ring
      _ ≤ (q : ℝ) * (T + 2) :=
        mul_le_mul hq le_rfl (by linarith) (by norm_num)
  have hlogN : Real.log N ≤ L := by
    simpa [L] using Real.log_le_log hNpos hNscale
  have hharmonic : (harmonic N : ℝ) ≤ 2 * L := by
    have hbase := harmonic_le_one_add_log N
    linarith
  rw [dirichletNontrivialZeroReciprocalMultiplicitySum]
  change (∑ rho ∈ S, m rho / (1 + |rho.im|)) ≤ _
  rw [← hfiber]
  calc
    (∑ n ∈ Finset.range N,
        ∑ rho ∈ S with g rho = n,
          m rho / (1 + |rho.im|)) ≤
        ∑ n ∈ Finset.range N,
          (4 * (A : ℝ) * L) * (((n + 1 : ℕ) : ℝ))⁻¹ := by
      exact Finset.sum_le_sum hfiberWeight
    _ = (4 * (A : ℝ) * L) * (harmonic N : ℝ) := by
      rw [← Finset.mul_sum, sum_range_inv_nat_add_one_eq_harmonic]
    _ ≤ (4 * (A : ℝ) * L) * (2 * L) :=
      mul_le_mul_of_nonneg_left hharmonic (by positivity)
    _ = 8 * (A : ℝ) * L ^ 2 := by ring
    _ = 8 * (A : ℝ) *
        Real.log ((q : ℝ) * (T + 2)) ^ 2 := rfl

/-- The complete reciprocal-height multiplicity has one absolute squared-log
bound for every character, primitive or imprimitive. -/
theorem exists_nat_dirichletNontrivialZeroReciprocalMultiplicitySum_le :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (q : ℕ) [NeZero q]
        (chi : DirichletCharacter ℂ q) (T : ℝ), 2 ≤ T →
          dirichletNontrivialZeroReciprocalMultiplicitySum chi T ≤
            8 * (A : ℝ) *
              Real.log ((q : ℝ) * (T + 2)) ^ 2 := by
  obtain ⟨A, hA, hprimitive⟩ :=
    exists_nat_dirichletNontrivialZeroReciprocalMultiplicitySum_le_of_isPrimitive
  refine ⟨A, hA, ?_⟩
  intro q _ chi T hT
  have hbase := hprimitive chi.conductor chi.primitiveCharacter
    chi.primitiveCharacter_isPrimitive T hT
  have hdqNat : chi.conductor ≤ q :=
    Nat.le_of_dvd (NeZero.pos q) chi.conductor_dvd_level
  have hdq : (chi.conductor : ℝ) ≤ q := by exact_mod_cast hdqNat
  have hTpos : 0 < T + 2 := by linarith
  have hdpos : (0 : ℝ) < chi.conductor := by
    exact_mod_cast NeZero.pos chi.conductor
  have hscale : (chi.conductor : ℝ) * (T + 2) ≤
      (q : ℝ) * (T + 2) :=
    mul_le_mul_of_nonneg_right hdq hTpos.le
  have hlog :
      Real.log ((chi.conductor : ℝ) * (T + 2)) ≤
        Real.log ((q : ℝ) * (T + 2)) :=
    Real.log_le_log (mul_pos hdpos hTpos) hscale
  have hleftNonneg :
      0 ≤ Real.log ((chi.conductor : ℝ) * (T + 2)) := by
    apply Real.log_nonneg
    nlinarith [mul_le_mul (show (1 : ℝ) ≤ chi.conductor by
      exact_mod_cast NeZero.pos chi.conductor)
      (show (1 : ℝ) ≤ T + 2 by linarith)
      (by norm_num : (0 : ℝ) ≤ 1)
      (by positivity : (0 : ℝ) ≤ chi.conductor)]
  have hrightNonneg : 0 ≤ Real.log ((q : ℝ) * (T + 2)) :=
    hleftNonneg.trans hlog
  have hsquare :
      Real.log ((chi.conductor : ℝ) * (T + 2)) ^ 2 ≤
        Real.log ((q : ℝ) * (T + 2)) ^ 2 :=
    sq_le_sq₀ hleftNonneg hrightNonneg |>.2 hlog
  rw [dirichletNontrivialZeroReciprocalMultiplicitySum_eq_inducingPrimitive
    chi T]
  exact hbase.trans
    (mul_le_mul_of_nonneg_left hsquare (by positivity))

end

end BoundedGaps.Maynard
