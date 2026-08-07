import Mathlib.Analysis.Fourier.ZMod
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# Primitive Gauss sums on `ZMod`

This file proves the finite Fourier and Gauss-sum prerequisites for
DavenportMNTCh23PV1980, printed pp. 135--136. In particular, the Gauss norm
proof works for composite moduli and does not use Mathlib's field-only Gauss
sum product theorem.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

open AddChar Finset

private theorem sum_star_mul_dft {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    (∑ k : ZMod q, star (ZMod.dft f k) * ZMod.dft f k) =
      (q : ℂ) * ∑ j : ZMod q, star (f j) * f j := by
  classical
  have hstar (x : ZMod q) :
      star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
    simpa only [Complex.star_def] using
      (AddChar.map_neg_eq_conj ZMod.stdAddChar x).symm
  simp only [ZMod.dft_apply, smul_eq_mul, star_sum, star_mul]
  simp_rw [hstar]
  simp only [neg_neg]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  have hsummand (i k : ZMod q) :
      star (f j) * ZMod.stdAddChar (j * k) *
          (ZMod.stdAddChar (-(i * k)) * f i) =
        (star (f j) * f i) * ZMod.stdAddChar (k * (j - i)) := by
    calc
      _ = (star (f j) * f i) *
          (ZMod.stdAddChar (j * k) * ZMod.stdAddChar (-(i * k))) := by ring
      _ = (star (f j) * f i) *
          ZMod.stdAddChar (j * k + -(i * k)) := by rw [map_add_eq_mul]
      _ = _ := by
        rw [show j * k + -(i * k) = k * (j - i) by ring]
  simp_rw [hsummand, ← Finset.mul_sum]
  simp_rw [AddChar.sum_mulShift (ψ := ZMod.stdAddChar) _
    (ZMod.isPrimitive_stdAddChar q)]
  simp only [sub_eq_zero, ZMod.card, Nat.cast_ite, Nat.cast_zero,
    mul_ite, mul_zero]
  simp [eq_comm]
  ring

/-- Parseval's identity for Mathlib's unnormalized complex DFT on `ZMod q`. -/
theorem sum_norm_sq_dft {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    (∑ k : ZMod q, ‖ZMod.dft f k‖ ^ 2) =
      (q : ℝ) * ∑ j : ZMod q, ‖f j‖ ^ 2 := by
  have h := sum_star_mul_dft f
  rw [Complex.star_def] at h
  simp_rw [← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq] at h
  exact_mod_cast h

/-- The squared mass of a Dirichlet character is the number of unit residue
classes. -/
theorem sum_norm_sq_dirichletCharacter {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    (∑ j : ZMod q, ‖χ j‖ ^ 2) = (Nat.totient q : ℝ) := by
  classical
  calc
    (∑ j : ZMod q, ‖χ j‖ ^ 2) =
        ∑ j : ZMod q, if IsUnit j then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : IsUnit j
      · have hnorm : ‖χ j‖ = 1 := by
          rw [← hj.unit_spec]
          exact χ.unit_norm_eq_one hj.unit
        simp [hj, hnorm]
      · simp [hj, χ.map_nonunit hj]
    _ = (((Finset.univ : Finset (ZMod q)).filter IsUnit).card : ℝ) := by
      simp
    _ = ((Fintype.card (ZMod q)ˣ : ℕ) : ℝ) := by
      congr 1
      calc
        ((Finset.univ : Finset (ZMod q)).filter IsUnit).card =
            (Finset.univ.map ⟨((↑) : (ZMod q)ˣ → ZMod q),
              Units.val_injective⟩).card := by
          congr 1
          ext j
          simp [IsUnit]
        _ = Fintype.card (ZMod q)ˣ := by simp
    _ = (Nat.totient q : ℝ) := by rw [ZMod.card_units_eq_totient]

/-- A primitive Dirichlet character modulo any positive, possibly composite,
modulus has standard Gauss-sum norm `sqrt q`. -/
theorem norm_gaussSum_stdAddChar_of_isPrimitive {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt q := by
  have hmassNeg :
      (∑ k : ZMod q, ‖χ⁻¹ (-k)‖ ^ 2) = (Nat.totient q : ℝ) := by
    calc
      _ = ∑ k : ZMod q, ‖χ⁻¹ k‖ ^ 2 :=
        Equiv.sum_comp (Equiv.neg (ZMod q)) (fun k ↦ ‖χ⁻¹ k‖ ^ 2)
      _ = (Nat.totient q : ℝ) := sum_norm_sq_dirichletCharacter χ⁻¹
  have hparseval := sum_norm_sq_dft (f := fun j ↦ χ j)
  simp_rw [hχ.fourierTransform_eq_inv_mul_gaussSum, norm_mul, mul_pow] at hparseval
  rw [← Finset.sum_mul, hmassNeg,
    sum_norm_sq_dirichletCharacter χ] at hparseval
  have htotient : (Nat.totient q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.totient_pos.mpr
      (Nat.pos_of_ne_zero (NeZero.ne q))))
  have hsquare : ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 = (q : ℝ) := by
    apply mul_left_cancel₀ htotient
    calc
      (Nat.totient q : ℝ) * ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 =
          (q : ℝ) * Nat.totient q := hparseval
      _ = (Nat.totient q : ℝ) * q := by ring
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg q),
    norm_nonneg (gaussSum χ ZMod.stdAddChar), Real.sqrt_nonneg (q : ℝ)]

/-- Davenport's primitive Fourier expansion in Mathlib's negative-kernel DFT
normalization. -/
theorem primitive_fourier_expansion {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (n : ZMod q) :
    (∑ a : ZMod q, χ⁻¹ a * ZMod.stdAddChar (a * n)) =
      χ n * gaussSum χ⁻¹ ZMod.stdAddChar := by
  have hχinv : χ⁻¹.IsPrimitive := by
    rw [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_inv]
    exact hχ
  have hfourier := hχinv.fourierTransform_eq_inv_mul_gaussSum (-n)
  simpa only [ZMod.dft_apply, smul_eq_mul, mul_neg, neg_neg, inv_inv,
    mul_comm] using hfourier

/-- Davenport's primitive Fourier expansion after division by the proved
nonzero Gauss sum. -/
theorem primitive_fourier_expansion_div {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (n : ZMod q) :
    χ n = (∑ a : ZMod q, χ⁻¹ a * ZMod.stdAddChar (a * n)) /
      gaussSum χ⁻¹ ZMod.stdAddChar := by
  have hχinv : χ⁻¹.IsPrimitive := by
    rw [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_inv]
    exact hχ
  have hnorm := norm_gaussSum_stdAddChar_of_isPrimitive χ⁻¹ hχinv
  have hgauss : gaussSum χ⁻¹ ZMod.stdAddChar ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hnorm
    have hqpos : (0 : ℝ) < q := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
    nlinarith [Real.sqrt_pos.2 hqpos]
  rw [primitive_fourier_expansion χ hχ n,
    mul_div_cancel_right₀ _ hgauss]

end BoundedGaps.Maynard
