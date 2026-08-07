import BoundedGaps.BombieriVinogradov.Analytic.ReducedFractionFrequencies
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The exact additive-character kernel on a consecutive interval

This file proves the half-phase reciprocal-sine identity used in the proof of
Montgomery--Vaughan's additive large sieve. See SEM-448 and
MontgomeryVaughanLargeSieve1973, equation (2.3).
-/

open scoped BigOperators

noncomputable section

namespace BoundedGaps.Maynard.AdditiveLargeSieve

private noncomputable def phase (x : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * x)

private lemma phase_nat_mul (x : ℝ) (n : ℕ) :
    phase ((n : ℝ) * x) = phase x ^ n := by
  rw [phase, phase, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private lemma phase_add (x y : ℝ) :
    phase (x + y) = phase x * phase y := by
  rw [phase, phase, phase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma sin_pi_mul_ne_zero_of_unitAddCircle_ne_zero (t : ℝ)
    (ht : (t : UnitAddCircle) ≠ 0) :
    Real.sin (Real.pi * t) ≠ 0 := by
  rw [Real.sin_ne_zero_iff]
  intro n hn
  apply ht
  rw [AddCircle.coe_eq_zero_iff]
  refine ⟨n, ?_⟩
  have hnt : (n : ℝ) = t := by
    nlinarith [Real.pi_pos]
  simpa [zsmul_eq_mul] using hnt

private lemma phase_half_denominator (t : ℝ) :
    (1 - phase t) * Complex.I =
      2 * phase (t / 2) * (Real.sin (Real.pi * t) : ℂ) := by
  rw [show phase t = phase (t / 2 + t / 2) by congr 1; ring,
    phase_add]
  simp only [phase]
  have hhalf : Complex.exp (2 * Real.pi * Complex.I * ((t / 2 : ℝ) : ℂ)) =
      Complex.exp (Real.pi * Complex.I * t) := by
    congr 1
    push_cast
    ring
  rw [hhalf]
  rw [Complex.ofReal_sin]
  rw [show ((Real.pi * t : ℝ) : ℂ) =
      (Real.pi : ℂ) * (t : ℂ) by push_cast; rfl]
  change (1 - Complex.exp (Real.pi * Complex.I * t) *
      Complex.exp (Real.pi * Complex.I * t)) * Complex.I =
    2 * Complex.exp (Real.pi * Complex.I * t) *
      (Complex.sin (Real.pi * t) : ℂ)
  rw [Complex.sin]
  have hcancel :
      Complex.exp (Real.pi * Complex.I * t) *
          Complex.exp (-(Real.pi * Complex.I * t)) = 1 := by
    rw [← Complex.exp_add]
    simp
  ring_nf
  rw [show Complex.I * Complex.exp (Real.pi * Complex.I * t) *
      Complex.exp (-(Real.pi * Complex.I * t)) = Complex.I by
        rw [mul_assoc, hcancel, mul_one]]

private lemma unitAddCircleAddChar_nsmul_coe (n : ℕ) (t : ℝ) :
    BoundedGaps.Maynard.unitAddCircleAddChar
        (n • (t : UnitAddCircle)) = phase ((n : ℝ) * t) := by
  rw [AddChar.map_nsmul_eq_pow, phase_nat_mul]
  congr 1
  rw [BoundedGaps.Maynard.unitAddCircleAddChar]
  change ((AddCircle.toCircle (t : UnitAddCircle) : Circle) : ℂ) = phase t
  rw [AddCircle.toCircle_apply_mk, Circle.coe_exp]
  simp only [phase]
  congr 1
  push_cast
  ring

private lemma phase_ne_one_of_unitAddCircle_ne_zero (t : ℝ)
    (ht : (t : UnitAddCircle) ≠ 0) : phase t ≠ 1 := by
  intro hphase
  have hzero : (1 - phase t) * Complex.I = 0 := by rw [hphase]; ring
  have hzero' :
      2 * phase (t / 2) * (Real.sin (Real.pi * t) : ℂ) = 0 := by
    rw [← phase_half_denominator]
    exact hzero
  have hsinC : (Real.sin (Real.pi * t) : ℂ) = 0 :=
    (mul_eq_zero.mp hzero').resolve_left
      (mul_ne_zero (by norm_num) (Complex.exp_ne_zero _))
  exact sin_pi_mul_ne_zero_of_unitAddCircle_ne_zero t ht
    (Complex.ofReal_eq_zero.mp hsinC)

private lemma sum_Ioc_nat_eq_sum_range_succ
    {A : Type*} [AddCommMonoid A] (f : ℕ → A) (m0 N : ℕ) :
    (∑ n ∈ Finset.Ioc m0 (m0 + N), f n) =
      ∑ k ∈ Finset.range N, f (m0 + k + 1) := by
  let e : ℕ ↪ ℕ :=
    ⟨fun k ↦ m0 + k + 1, by intro a b hab; dsimp at hab; omega⟩
  have hset : Finset.Ioc m0 (m0 + N) = (Finset.range N).map e := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_map, Finset.mem_range, e]
    constructor
    · intro hn
      dsimp [e]
      refine ⟨n - m0 - 1, ?_, ?_⟩
      · omega
      · omega
    · rintro ⟨k, hk, rfl⟩
      dsimp [e]
      omega
  rw [hset, Finset.sum_map]
  simp [e]

private lemma sum_phase_Ioc (t : ℝ) (ht : (t : UnitAddCircle) ≠ 0)
    (m0 N : ℕ) :
    (∑ n ∈ Finset.Ioc m0 (m0 + N),
      phase ((n : ℝ) * t)) =
      phase (((m0 : ℝ) + 1) * t) *
        ((1 - phase ((N : ℝ) * t)) / (1 - phase t)) := by
  rw [sum_Ioc_nat_eq_sum_range_succ]
  have hterm (k : ℕ) :
      phase (((m0 + k + 1 : ℕ) : ℝ) * t) =
        phase (((m0 : ℝ) + 1) * t) * phase t ^ k := by
    have harg : (((m0 + k + 1 : ℕ) : ℝ) * t) =
        (((m0 : ℝ) + 1) * t) + ((k : ℝ) * t) := by
      push_cast
      ring
    rw [harg, phase_add, phase_nat_mul]
  simp_rw [hterm]
  rw [← Finset.mul_sum, geom_sum_eq
    (phase_ne_one_of_unitAddCircle_ne_zero t ht)]
  rw [phase_nat_mul]
  congr 1
  rw [show phase t - 1 = -(1 - phase t) by ring, div_neg]
  ring

private lemma phase_one_half_split (a t : ℝ) :
    phase ((a + 1) * t) =
      phase ((a + 1 / 2) * t) * phase (t / 2) := by
  rw [show (a + 1) * t = (a + 1 / 2) * t + t / 2 by ring,
    phase_add]

private lemma phase_add_nat_interval (a t : ℝ) (N : ℕ) :
    phase ((a + 1) * t) * phase ((N : ℝ) * t) =
      phase (((a + (N : ℝ)) + 1) * t) := by
  rw [← phase_add]
  congr 1
  ring

private lemma half_phase_ratio {H Z s : ℂ}
    (hden : (1 - Z) * Complex.I = 2 * H * s)
    (hZ : Z ≠ 1) (hs : s ≠ 0) :
    H * (1 - Z)⁻¹ = (Complex.I / 2) * s⁻¹ := by
  field_simp [sub_ne_zero.mpr hZ, hs]
  calc
    H * 2 * s = 2 * H * s := by ring
    _ = (1 - Z) * Complex.I := hden.symm

/-- Exact geometric-series evaluation on `m0 < n ≤ m0 + N`.

The nonzero circle hypothesis excludes every integer sine pole.  The endpoint
phases are retained as real lifts, matching Montgomery--Vaughan (1973),
equation (2.3), with the positive additive-character convention of SEM-444.
-/
theorem sum_unitAddCircleAddChar_Ioc_eq_cosecant
    (t : ℝ) (ht : (t : UnitAddCircle) ≠ 0) (m0 N : ℕ) :
    (∑ n ∈ Finset.Ioc m0 (m0 + N),
      BoundedGaps.Maynard.unitAddCircleAddChar (n • (t : UnitAddCircle))) =
      Complex.I / 2 *
        (Complex.exp (2 * Real.pi * Complex.I *
          (((m0 : ℝ) + 1 / 2) * t)) -
         Complex.exp (2 * Real.pi * Complex.I *
          ((((m0 + N : ℕ) : ℝ) + 1 / 2) * t))) *
        (((Real.sin (Real.pi * t))⁻¹ : ℝ) : ℂ) := by
  calc
    (∑ n ∈ Finset.Ioc m0 (m0 + N),
        BoundedGaps.Maynard.unitAddCircleAddChar
          (n • (t : UnitAddCircle))) =
        ∑ n ∈ Finset.Ioc m0 (m0 + N), phase ((n : ℝ) * t) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact unitAddCircleAddChar_nsmul_coe n t
    _ = phase (((m0 : ℝ) + 1) * t) *
        ((1 - phase ((N : ℝ) * t)) / (1 - phase t)) :=
      sum_phase_Ioc t ht m0 N
    _ = Complex.I / 2 *
        (Complex.exp (2 * Real.pi * Complex.I *
          (((m0 : ℝ) + 1 / 2) * t)) -
         Complex.exp (2 * Real.pi * Complex.I *
          ((((m0 + N : ℕ) : ℝ) + 1 / 2) * t))) *
        (((Real.sin (Real.pi * t))⁻¹ : ℝ) : ℂ) := by
      let A : ℂ := phase (((m0 : ℝ) + 1 / 2) * t)
      let B : ℂ := phase ((((m0 + N : ℕ) : ℝ) + 1 / 2) * t)
      let H : ℂ := phase (t / 2)
      let Z : ℂ := phase t
      let s : ℂ := (Real.sin (Real.pi * t) : ℂ)
      have hstart : phase (((m0 : ℝ) + 1) * t) = A * H := by
        dsimp [A, H]
        exact phase_one_half_split (m0 : ℝ) t
      have hend : phase (((m0 : ℝ) + 1) * t) *
          phase ((N : ℝ) * t) = B * H := by
        have h₁ := phase_add_nat_interval (m0 : ℝ) t N
        have h₂ := phase_one_half_split (((m0 + N : ℕ) : ℝ)) t
        dsimp [B, H]
        calc
          _ = phase (((m0 : ℝ) + (N : ℝ) + 1) * t) := h₁
          _ = phase ((((m0 + N : ℕ) : ℝ) + 1) * t) := by
            congr 1
            push_cast
            ring
          _ = _ := h₂
      have hnum : phase (((m0 : ℝ) + 1) * t) *
          (1 - phase ((N : ℝ) * t)) = (A - B) * H := by
        calc
          _ = phase (((m0 : ℝ) + 1) * t) -
              phase (((m0 : ℝ) + 1) * t) * phase ((N : ℝ) * t) := by ring
          _ = A * H - phase (((m0 : ℝ) + 1) * t) *
              phase ((N : ℝ) * t) := by rw [hstart]
          _ = A * H - B * H := by rw [hend]
          _ = (A - B) * H := by ring
      have hden : (1 - Z) * Complex.I = 2 * H * s := by
        dsimp [Z, H, s]
        exact phase_half_denominator t
      have hratio : H * (1 - Z)⁻¹ = (Complex.I / 2) * s⁻¹ :=
        half_phase_ratio hden
          (phase_ne_one_of_unitAddCircle_ne_zero t ht)
          (Complex.ofReal_ne_zero.mpr
            (sin_pi_mul_ne_zero_of_unitAddCircle_ne_zero t ht))
      dsimp [A, B, H, Z, s] at hnum hratio ⊢
      calc
        phase (((m0 : ℝ) + 1) * t) *
            ((1 - phase ((N : ℝ) * t)) / (1 - phase t)) =
            (phase (((m0 : ℝ) + 1) * t) *
              (1 - phase ((N : ℝ) * t))) * (1 - phase t)⁻¹ := by
                rw [div_eq_mul_inv]
                ring
        _ = ((phase (((m0 : ℝ) + 1 / 2) * t) -
              phase ((((m0 + N : ℕ) : ℝ) + 1 / 2) * t)) *
              phase (t / 2)) * (1 - phase t)⁻¹ := by rw [hnum]
        _ = (Complex.I / 2) *
              (phase (((m0 : ℝ) + 1 / 2) * t) -
                phase ((((m0 + N : ℕ) : ℝ) + 1 / 2) * t)) *
              (Real.sin (Real.pi * t) : ℂ)⁻¹ := by
                rw [show ((phase (((m0 : ℝ) + 1 / 2) * t) -
                    phase ((((m0 + N : ℕ) : ℝ) + 1 / 2) * t)) *
                    phase (t / 2)) * (1 - phase t)⁻¹ =
                  (phase (((m0 : ℝ) + 1 / 2) * t) -
                    phase ((((m0 + N : ℕ) : ℝ) + 1 / 2) * t)) *
                    (phase (t / 2) * (1 - phase t)⁻¹) by ring]
                rw [hratio]
                ring
        _ = _ := by
          simp only [phase]
          push_cast
          ring


end BoundedGaps.Maynard.AdditiveLargeSieve
