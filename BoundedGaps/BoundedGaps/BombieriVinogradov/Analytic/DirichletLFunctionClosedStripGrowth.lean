import BoundedGaps.BombieriVinogradov.Analytic.InducingEulerProduct
import BoundedGaps.BombieriVinogradov.Analytic.PrimitiveLFunctionFixedStrip

/-!
# Dirichlet L-functions on the Goldfeld strip

This file extends the primitive fixed-strip bound through the exact inducing
Euler product.  The resulting estimate covers the generally imprimitive
cross character in Koukoulopoulos, printed p. 126, Theorem 12.9.

Source: printed p. 110, equation (11.2), and printed p. 115, Exercise 11.1.
Semantic review: `SEM-556`.
-/

namespace BoundedGaps.Maynard

open Complex

/-- On `Re(s) >= -1`, the finite Euler product omitted by passage to the
primitive inducer costs at most the square of the original level. -/
theorem norm_inducingEulerProduct_le_sq_of_neg_one_le_re
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {s : ℂ} (hs : -(1 : ℝ) ≤ s.re) :
    ‖inducingEulerProduct chi s‖ ≤ (q : ℝ) ^ 2 := by
  rw [inducingEulerProduct]
  calc
    ‖∏ p ∈ q.primeFactors,
        (1 - chi.primitiveCharacter p * (p : ℂ) ^ (-s))‖ ≤
        ∏ p ∈ q.primeFactors,
          ‖1 - chi.primitiveCharacter p * (p : ℂ) ^ (-s)‖ :=
      Finset.norm_prod_le _ _
    _ ≤ ∏ p ∈ q.primeFactors, (p : ℝ) ^ 2 := by
      apply Finset.prod_le_prod
      · intro p hp
        positivity
      · intro p hp
        have hpPrime := Nat.prime_of_mem_primeFactors hp
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpPrime.one_le
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpPrime.two_le
        have hpow : (p : ℝ) ^ (-s.re) ≤ (p : ℝ) := by
          calc
            (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
            _ = (p : ℝ) := Real.rpow_one _
        calc
          ‖1 - chi.primitiveCharacter p * (p : ℂ) ^ (-s)‖ ≤
              1 + ‖chi.primitiveCharacter p * (p : ℂ) ^ (-s)‖ := by
            simpa using norm_sub_le (1 : ℂ)
              (chi.primitiveCharacter p * (p : ℂ) ^ (-s))
          _ = 1 + ‖chi.primitiveCharacter p‖ * (p : ℝ) ^ (-s.re) := by
            rw [norm_mul, Complex.norm_natCast_cpow_of_pos hpPrime.pos, neg_re]
          _ ≤ 1 + 1 * (p : ℝ) := by
            gcongr
            exact chi.primitiveCharacter.norm_le_one p
          _ ≤ (p : ℝ) ^ 2 := by nlinarith
    _ = (∏ p ∈ q.primeFactors, (p : ℝ)) ^ 2 :=
      Finset.prod_pow q.primeFactors 2 (fun p : ℕ => (p : ℝ))
    _ = ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ^ 2 := by
      push_cast
      rfl
    _ ≤ (q : ℝ) ^ 2 := by
      gcongr
      exact_mod_cast Nat.le_of_dvd (NeZero.pos q)
        (Nat.prod_primeFactors_dvd q)

private theorem exists_norm_primitiveLFunction_closedStrip_le_pow :
    ∃ A : ℕ, 12 ≤ A ∧
      ∀ (q : ℕ) [NeZero q], 1 < q →
        ∀ (chi : DirichletCharacter ℂ q), chi.IsPrimitive →
          ∀ s : ℂ, -(1 : ℝ) ≤ s.re → s.re ≤ 3 →
            ‖DirichletCharacter.LFunction chi s‖ ≤
              ((q : ℝ) * (|s.im| + 2)) ^ A := by
  obtain ⟨A, hA, hleft⟩ := exists_norm_LFunction_fixedStrip_le_pow
  refine ⟨A, hA, ?_⟩
  intro q _ hq chi hchi s hslo hshi
  let T : ℝ := |s.im| + 2
  let B : ℝ := (q : ℝ) * T
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := one_le_two.trans hq2
  have hT2 : (2 : ℝ) ≤ T := by
    dsimp [T]
    linarith [abs_nonneg s.im]
  have hB4 : (4 : ℝ) ≤ B := by
    dsimp [B]
    nlinarith
  have hB1 : (1 : ℝ) ≤ B := by linarith
  by_cases hleftCase : s.re ≤ (1 / 2 : ℝ)
  · exact hleft q hq chi hchi s (by linarith) hleftCase
  · have hhalf : (1 / 2 : ℝ) ≤ s.re := le_of_not_ge hleftCase
    by_cases hcentral : s.re ≤ 2
    · have hc := norm_LFunction_centralStrip_le hq chi hchi
          (sigma := s.re) (t := s.im) hhalf hcentral
      have hsarg : (((s.re : ℝ) : ℂ) + ((s.im : ℝ) : ℂ) * I) = s := by
        apply Complex.ext <;> simp
      rw [hsarg] at hc
      have hsqrt : Real.sqrt (q : ℝ) ≤ q :=
        Real.sqrt_le_self_iff.mpr (Or.inr hq1)
      have hlog : Real.log (q : ℝ) ≤ q :=
        (Real.log_le_sub_one_of_pos (by positivity)).trans
          (sub_le_self _ zero_le_one)
      have hcentralBound :
          2 * T * Real.sqrt (q : ℝ) * Real.log (q : ℝ) ≤ B ^ 2 := by
        calc
          2 * T * Real.sqrt (q : ℝ) * Real.log (q : ℝ) ≤
              2 * T * (q : ℝ) * (q : ℝ) := by gcongr
          _ ≤ ((q : ℝ) * T) ^ 2 := by nlinarith
          _ = B ^ 2 := rfl
      calc
        ‖DirichletCharacter.LFunction chi s‖ ≤
            2 * T * Real.sqrt (q : ℝ) * Real.log (q : ℝ) := by
          simpa [T] using hc
        _ ≤ B ^ 2 := hcentralBound
        _ ≤ B ^ A := pow_le_pow_right₀ hB1 (by omega)
    · have hfar : (2 : ℝ) ≤ s.re := le_of_not_ge hcentral
      have hf := norm_LFunction_farRight_le_three chi s hfar
      calc
        ‖DirichletCharacter.LFunction chi s‖ ≤ 3 := hf
        _ ≤ B ^ 1 := by simp; linarith
        _ ≤ B ^ A := pow_le_pow_right₀ hB1 (by omega)

/-- One absolute exponent controls every nonprincipal, possibly imprimitive,
Dirichlet L-function on the closed strip used by Goldfeld's contour. -/
theorem exists_norm_LFunction_closedStrip_le_pow :
    ∃ A : ℕ, 14 ≤ A ∧
      ∀ (q : ℕ) [NeZero q], 1 < q →
        ∀ (chi : DirichletCharacter ℂ q), chi ≠ 1 →
          ∀ s : ℂ, -(1 : ℝ) ≤ s.re → s.re ≤ 3 →
            ‖DirichletCharacter.LFunction chi s‖ ≤
              ((q : ℝ) * (|s.im| + 2)) ^ A := by
  obtain ⟨A, hA, hprimitive⟩ :=
    exists_norm_primitiveLFunction_closedStrip_le_pow
  refine ⟨A + 2, by omega, ?_⟩
  intro q _ hq chi hchi s hslo hshi
  let d := chi.conductor
  letI : NeZero d := ⟨chi.conductor_ne_zero⟩
  have hd1 : 1 < d := by
    have hdne : d ≠ 1 := by
      intro hd
      apply hchi
      exact DirichletCharacter.eq_one_iff_conductor_eq_one.mpr hd
    have hd0 : d ≠ 0 := NeZero.ne d
    omega
  have hdq : d ≤ q :=
    Nat.le_of_dvd (NeZero.pos q) chi.conductor_dvd_level
  let T : ℝ := |s.im| + 2
  let B : ℝ := (q : ℝ) * T
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := one_le_two.trans hq2
  have hT2 : (2 : ℝ) ≤ T := by
    dsimp [T]
    linarith [abs_nonneg s.im]
  have hT0 : (0 : ℝ) ≤ T := zero_le_two.trans hT2
  have hB1 : (1 : ℝ) ≤ B := by
    dsimp [B]
    nlinarith
  have hprimitiveBound := hprimitive d hd1 chi.primitiveCharacter
    chi.primitiveCharacter_isPrimitive s hslo hshi
  have hbase : (d : ℝ) * T ≤ B := by
    dsimp [B]
    gcongr
  have hprimitiveBound' :
      ‖DirichletCharacter.LFunction chi.primitiveCharacter s‖ ≤ B ^ A :=
    hprimitiveBound.trans (by
      simpa [T] using
        pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg d) hT0) hbase A)
  have hEuler := norm_inducingEulerProduct_le_sq_of_neg_one_le_re chi hslo
  have hqB : (q : ℝ) ≤ B := by
    dsimp [B]
    nlinarith
  have hqSq : (q : ℝ) ^ 2 ≤ B ^ 2 := by gcongr
  rw [LFunction_eq_inducingPrimitive_mul_inducingEulerProduct chi (.inl hchi),
    norm_mul]
  calc
    ‖DirichletCharacter.LFunction chi.primitiveCharacter s‖ *
        ‖inducingEulerProduct chi s‖ ≤ B ^ A * B ^ 2 :=
      mul_le_mul hprimitiveBound' (hEuler.trans hqSq)
        (norm_nonneg _) (pow_nonneg (zero_le_one.trans hB1) A)
    _ = B ^ (A + 2) := by rw [pow_add]

end BoundedGaps.Maynard
