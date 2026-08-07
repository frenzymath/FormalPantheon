import BoundedGaps.BombieriVinogradov.Analytic.PrimePowerCorrectionBound
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# Centered character reduction

This file formalizes the finite `psi'` normalization and the pointwise
primitive-character reduction on Akbary--Hambrook2013v2, Section 7, p. 24.
The squared-log correction comes from SEM-416. The later conductor reindex,
reciprocal-totient estimate, and character mean-value theorem are deliberately
not included here.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators ArithmeticFunction.vonMangoldt

/-
The source subtracts the global Chebyshev function only for the principal
character. A local classical equality decision keeps this definition total at
level zero; every normalized theorem below explicitly assumes a positive level.
-/
noncomputable def centeredTwistedChebyshevSum
    (x q : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  letI : DecidableEq (DirichletCharacter ℂ q) := Classical.decEq _
  twistedChebyshevSum x q χ -
    if χ = 1 then (Chebyshev.psi (x : ℝ) : ℂ) else 0

theorem centeredTwistedChebyshevSum_one (x : ℕ) :
    centeredTwistedChebyshevSum x 1
      (1 : DirichletCharacter ℂ 1) = 0 := by
  rw [centeredTwistedChebyshevSum, if_pos rfl, sub_eq_zero]
  rw [twistedChebyshevSum, Chebyshev.psi, Nat.floor_natCast]
  have hinterval : Finset.Icc 1 x = Finset.Ioc 0 x := by
    simpa using Finset.Icc_succ_left_eq_Ioc 0 x
  rw [hinterval]
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hu : IsUnit (n : ZMod 1) := by
    exact ⟨1, Subsingleton.elim _ _⟩
  rw [MulChar.one_apply hu]
  simp

theorem primitiveCharacter_eq_one_iff
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    χ.primitiveCharacter = 1 ↔ χ = 1 := by
  constructor
  · intro h
    have hchange := χ.changeLevel_primitiveCharacter
    rw [h, DirichletCharacter.changeLevel_one] at hchange
    exact hchange.symm
  · rintro rfl
    exact DirichletCharacter.primitiveCharacter_one

theorem centeredPrimitive_sub_centered_eq
    {x q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    centeredTwistedChebyshevSum x χ.conductor χ.primitiveCharacter -
        centeredTwistedChebyshevSum x q χ =
      twistedChebyshevSum x χ.conductor χ.primitiveCharacter -
        twistedChebyshevSum x q χ := by
  classical
  rw [centeredTwistedChebyshevSum, centeredTwistedChebyshevSum]
  rw [if_congr (primitiveCharacter_eq_one_iff χ) rfl]
  ring_nf
  rfl

theorem chebyshevProgressionSum_sub_global_eq_centered_character_average
    {x q a : ℕ} [NeZero q] (ha : Nat.Coprime a q) :
    ((chebyshevProgressionSum x q a -
        Chebyshev.psi (x : ℝ) / (q.totient : ℝ) : ℝ) : ℂ) =
      (q.totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q,
          χ (a : ZMod q)⁻¹ * centeredTwistedChebyshevSum x q χ := by
  classical
  have hraw := chebyshevProgressionSum_complex_eq_character_average
    (x := x) (q := q) (a := a) ha
  have hone_inv : (1 : DirichletCharacter ℂ q) (a : ZMod q)⁻¹ = 1 := by
    have hunit : IsUnit (a : ZMod q) := by
      rw [ZMod.isUnit_iff_coprime]
      exact ha
    rcases hunit with ⟨u, hu⟩
    rw [← hu]
    rw [ZMod.inv_coe_unit]
    exact MulChar.one_apply_coe (R' := ℂ) (u⁻¹)
  simp_rw [centeredTwistedChebyshevSum]
  simp only [Complex.ofReal_sub, Complex.ofReal_div, hraw]
  rw [Finset.mul_sum]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hsum :
      (∑ χ : DirichletCharacter ℂ q,
        χ (a : ZMod q)⁻¹ *
          (if χ = 1 then (Chebyshev.psi (x : ℝ) : ℂ) else 0)) =
        (Chebyshev.psi (x : ℝ) : ℂ) := by
    simp [hone_inv]
  rw [hsum]
  rw [← Finset.mul_sum]
  push_cast
  ring

theorem abs_chebyshevProgressionSum_sub_global_le_centered_average
    {x q a : ℕ} [NeZero q] (ha : Nat.Coprime a q) :
    |chebyshevProgressionSum x q a -
        Chebyshev.psi (x : ℝ) / (q.totient : ℝ)| ≤
      (q.totient : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q,
          ‖centeredTwistedChebyshevSum x q χ‖ := by
  have hphi : 0 < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hunit : IsUnit (a : ZMod q) := by
    rw [ZMod.isUnit_iff_coprime]
    exact ha
  rcases hunit with ⟨u, hu⟩
  have hχnorm (χ : DirichletCharacter ℂ q) :
      ‖χ (a : ZMod q)⁻¹‖ = 1 := by
    rw [← hu, ZMod.inv_coe_unit]
    exact χ.unit_norm_eq_one (u⁻¹)
  rw [← Real.norm_eq_abs, ← Complex.norm_real]
  change ‖((chebyshevProgressionSum x q a -
      Chebyshev.psi (x : ℝ) / (q.totient : ℝ) : ℝ) : ℂ)‖ ≤ _
  rw [chebyshevProgressionSum_sub_global_eq_centered_character_average ha]
  rw [norm_mul]
  have hinvnorm : ‖(q.totient : ℂ)⁻¹‖ = (q.totient : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_natCast]
  rw [hinvnorm]
  apply mul_le_mul_of_nonneg_left
  · calc
      ‖∑ χ : DirichletCharacter ℂ q,
          χ (a : ZMod q)⁻¹ * centeredTwistedChebyshevSum x q χ‖ ≤
          ∑ χ : DirichletCharacter ℂ q,
            ‖χ (a : ZMod q)⁻¹ * centeredTwistedChebyshevSum x q χ‖ := by
        apply norm_sum_le
      _ = ∑ χ : DirichletCharacter ℂ q,
          ‖centeredTwistedChebyshevSum x q χ‖ := by
        apply Finset.sum_congr rfl
        intro χ hχ
        rw [norm_mul, hχnorm, one_mul]
  · positivity

theorem norm_centeredTwistedChebyshevSum_le_log_sq_add_primitive
    {x q : ℕ} (χ : DirichletCharacter ℂ q)
    (hx : 2 ≤ x) (hq : 1 ≤ q) :
    ‖centeredTwistedChebyshevSum x q χ‖ ≤
      (Real.log ((q * x : ℕ) : ℝ)) ^ 2 +
        ‖centeredTwistedChebyshevSum
          x χ.conductor χ.primitiveCharacter‖ := by
  have hq0 : q ≠ 0 := by omega
  letI : NeZero q := ⟨hq0⟩
  have hdiff := centeredPrimitive_sub_centered_eq (x := x) χ
  have hraw := norm_primitiveTwistedChebyshevSum_sub_le_log_mul_sq χ hx hq
  have hcenter :
      ‖centeredTwistedChebyshevSum
              x χ.conductor χ.primitiveCharacter -
            centeredTwistedChebyshevSum x q χ‖ ≤
        (Real.log ((q * x : ℕ) : ℝ)) ^ 2 := by
    rw [hdiff]
    exact hraw
  calc
    ‖centeredTwistedChebyshevSum x q χ‖ =
        ‖centeredTwistedChebyshevSum
            x χ.conductor χ.primitiveCharacter -
          (centeredTwistedChebyshevSum
              x χ.conductor χ.primitiveCharacter -
            centeredTwistedChebyshevSum x q χ)‖ := by
      congr 1
      ring
    _ ≤ ‖centeredTwistedChebyshevSum
            x χ.conductor χ.primitiveCharacter‖ +
        ‖centeredTwistedChebyshevSum
              x χ.conductor χ.primitiveCharacter -
            centeredTwistedChebyshevSum x q χ‖ := norm_sub_le _ _
    _ ≤ ‖centeredTwistedChebyshevSum
            x χ.conductor χ.primitiveCharacter‖ +
        (Real.log ((q * x : ℕ) : ℝ)) ^ 2 := by
      simpa [add_comm] using
        (add_le_add_left hcenter
          ‖centeredTwistedChebyshevSum
            x χ.conductor χ.primitiveCharacter‖)
    _ = (Real.log ((q * x : ℕ) : ℝ)) ^ 2 +
        ‖centeredTwistedChebyshevSum
          x χ.conductor χ.primitiveCharacter‖ := by ring

theorem inv_totient_mul_sum_norm_centered_le_log_sq_add_primitive
    {x q : ℕ} (hx : 2 ≤ x) (hq : 1 ≤ q) :
    (q.totient : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q,
          ‖centeredTwistedChebyshevSum x q χ‖ ≤
      (Real.log ((q * x : ℕ) : ℝ)) ^ 2 +
        (q.totient : ℝ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q,
            ‖centeredTwistedChebyshevSum
              x χ.conductor χ.primitiveCharacter‖ := by
  have hq0 : q ≠ 0 := by omega
  letI : NeZero q := ⟨hq0⟩
  have hpoint : ∀ χ : DirichletCharacter ℂ q,
      ‖centeredTwistedChebyshevSum x q χ‖ ≤
        (Real.log ((q * x : ℕ) : ℝ)) ^ 2 +
          ‖centeredTwistedChebyshevSum
            x χ.conductor χ.primitiveCharacter‖ := by
    intro χ
    exact norm_centeredTwistedChebyshevSum_le_log_sq_add_primitive χ hx hq
  have hsum :
      ∑ χ : DirichletCharacter ℂ q,
          ‖centeredTwistedChebyshevSum x q χ‖ ≤
        (q.totient : ℝ) * (Real.log ((q * x : ℕ) : ℝ)) ^ 2 +
          ∑ χ : DirichletCharacter ℂ q,
            ‖centeredTwistedChebyshevSum
              x χ.conductor χ.primitiveCharacter‖ := by
    calc
      ∑ χ : DirichletCharacter ℂ q,
          ‖centeredTwistedChebyshevSum x q χ‖ ≤
          ∑ χ : DirichletCharacter ℂ q,
            ((Real.log ((q * x : ℕ) : ℝ)) ^ 2 +
              ‖centeredTwistedChebyshevSum
                x χ.conductor χ.primitiveCharacter‖) := by
        apply Finset.sum_le_sum
        intro χ hχ
        exact hpoint χ
      _ = (q.totient : ℝ) * (Real.log ((q * x : ℕ) : ℝ)) ^ 2 +
          ∑ χ : DirichletCharacter ℂ q,
            ‖centeredTwistedChebyshevSum
              x χ.conductor χ.primitiveCharacter‖ := by
        rw [Finset.sum_add_distrib]
        have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
          rw [← Nat.card_eq_fintype_card]
          exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
        simp [hcard, Finset.sum_const, nsmul_eq_mul]
  have hphi : 0 < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq0)
  have hmul := mul_le_mul_of_nonneg_left hsum
    (inv_nonneg.mpr hphi.le)
  calc
    (q.totient : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q,
          ‖centeredTwistedChebyshevSum x q χ‖ ≤
      (q.totient : ℝ)⁻¹ *
        ((q.totient : ℝ) * (Real.log ((q * x : ℕ) : ℝ)) ^ 2 +
          ∑ χ : DirichletCharacter ℂ q,
            ‖centeredTwistedChebyshevSum
              x χ.conductor χ.primitiveCharacter‖) := hmul
    _ = (Real.log ((q * x : ℕ) : ℝ)) ^ 2 +
        (q.totient : ℝ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q,
            ‖centeredTwistedChebyshevSum
              x χ.conductor χ.primitiveCharacter‖ := by
      field_simp [hphi.ne']

theorem abs_chebyshevProgressionSum_sub_global_le_log_sq_add_primitive_average
    {x q a : ℕ} (hx : 2 ≤ x) (hq : 1 ≤ q)
    (ha : Nat.Coprime a q) :
    |chebyshevProgressionSum x q a -
        Chebyshev.psi (x : ℝ) / (q.totient : ℝ)| ≤
      (Real.log ((q * x : ℕ) : ℝ)) ^ 2 +
        (q.totient : ℝ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q,
            ‖centeredTwistedChebyshevSum
              x χ.conductor χ.primitiveCharacter‖ := by
  have hq0 : q ≠ 0 := by omega
  letI : NeZero q := ⟨hq0⟩
  exact (abs_chebyshevProgressionSum_sub_global_le_centered_average ha).trans
    (inv_totient_mul_sum_norm_centered_le_log_sq_add_primitive hx hq)

end BoundedGaps.Maynard
