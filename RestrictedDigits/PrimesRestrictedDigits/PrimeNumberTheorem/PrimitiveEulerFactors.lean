import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Primitive and imprimitive Dirichlet Euler factors

This file implements the exact primitive/imprimitive factorization, together with its
branch-free logarithmic derivative.

Source: `MONTGOMERY-VAUGHAN-MNT-I`, Eqs. (9.2) and (10.20), pp. 282 and 334.
-/

open scoped LSeries.notation

namespace PrimesRestrictedDigits

open DirichletCharacter

/-- One Euler factor removed when a primitive character is raised to a larger
level. -/
noncomputable def primitiveEulerFactor {d : Nat}
    (chi : DirichletCharacter Complex d) (p : Nat) (s : Complex) : Complex :=
  1 - chi p * (p : Complex) ^ (-s)

/-- The finite Euler correction between a character and its primitive
inducer. The product is over distinct prime divisors of the original level. -/
noncomputable def primitiveEulerCorrection {q : Nat}
    (chi : DirichletCharacter Complex q) (s : Complex) : Complex :=
  ∏ p ∈ q.primeFactors, primitiveEulerFactor chi.primitiveCharacter p s

/-- The logarithmic derivative of the finite primitive Euler correction,
written as its explicit finite sum. -/
noncomputable def primitiveEulerLogDerivCorrection {q : Nat}
    (chi : DirichletCharacter Complex q) (s : Complex) : Complex :=
  ∑ p ∈ q.primeFactors,
    chi.primitiveCharacter p * Complex.log p * (p : Complex) ^ (-s) /
      primitiveEulerFactor chi.primitiveCharacter p s

/-- The absolutely convergent Dirichlet series differs from that of the
primitive inducer by the finite Euler correction. -/
theorem LSeries_eq_primitive_mul_eulerCorrection {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) {s : Complex} (hs : 1 < s.re) :
    L ↗chi s = L ↗chi.primitiveCharacter s * primitiveEulerCorrection chi s := by
  simpa only [primitiveEulerCorrection, primitiveEulerFactor,
    DirichletCharacter.changeLevel_primitiveCharacter] using
      DirichletCharacter.LSeries_changeLevel chi.conductor_dvd_level
        chi.primitiveCharacter hs

/-- The analytically continued L-function differs from that of the primitive
inducer by the same finite Euler correction. -/
theorem LFunction_eq_primitive_mul_eulerCorrection {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) [NeZero chi.conductor]
    {s : Complex} (hregular : chi.primitiveCharacter ≠ 1 ∨ s ≠ 1) :
    chi.LFunction s = chi.primitiveCharacter.LFunction s *
      primitiveEulerCorrection chi s := by
  simpa only [primitiveEulerCorrection, primitiveEulerFactor,
    DirichletCharacter.changeLevel_primitiveCharacter] using
      DirichletCharacter.LFunction_changeLevel chi.conductor_dvd_level
        chi.primitiveCharacter hregular

/-- Differentiating a removed Euler factor produces a positive sign: the
minus in the factor cancels the derivative of the negative exponent. -/
theorem primitiveEulerFactor_hasDerivAt {d p : Nat}
    (chi : DirichletCharacter Complex d) (hp : p.Prime) (s : Complex) :
    HasDerivAt (primitiveEulerFactor chi p)
      (chi p * Complex.log p * (p : Complex) ^ (-s)) s := by
  have hp0 : (p : Complex) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  have hpow' := (hasDerivAt_neg s).const_cpow (c := (p : Complex))
    (.inl hp0)
  have hfactor := (hpow'.const_mul (chi p)).const_sub 1
  change HasDerivAt (fun z : Complex ↦
    1 - chi p * (p : Complex) ^ (-z)) _ s
  simpa only [mul_neg, neg_mul, mul_neg_one, neg_neg, mul_one, one_mul,
    mul_assoc, mul_comm, mul_left_comm] using hfactor

/-- Exact logarithmic derivative of one primitive Euler factor. -/
theorem logDeriv_primitiveEulerFactor {d p : Nat}
    (chi : DirichletCharacter Complex d) (hp : p.Prime) (s : Complex) :
    logDeriv (primitiveEulerFactor chi p) s =
      chi p * Complex.log p * (p : Complex) ^ (-s) /
        primitiveEulerFactor chi p s := by
  rw [logDeriv_apply, (primitiveEulerFactor_hasDerivAt chi hp s).deriv]

/-- A primitive Euler factor cannot vanish in the open right half-plane. -/
theorem primitiveEulerFactor_ne_zero_of_re_pos {d p : Nat}
    (chi : DirichletCharacter Complex d) (hp : p.Prime) {s : Complex}
    (hs : 0 < s.re) : primitiveEulerFactor chi p s ≠ 0 := by
  have hpow : ‖(p : Complex) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos]
    apply Real.rpow_lt_one_of_one_lt_of_neg
    · exact_mod_cast hp.one_lt
    · simpa only [Complex.neg_re] using neg_lt_zero.mpr hs
  have hmul : ‖chi p * (p : Complex) ^ (-s)‖ < 1 := by
    rw [norm_mul]
    calc
      ‖chi p‖ * ‖(p : Complex) ^ (-s)‖ ≤
          1 * ‖(p : Complex) ^ (-s)‖ := by
        gcongr
        exact chi.norm_le_one p
      _ < 1 := by simpa only [one_mul] using hpow
  rw [primitiveEulerFactor, sub_ne_zero]
  intro heq
  rw [← heq, norm_one] at hmul
  exact lt_irrefl 1 hmul

/-- The complete finite Euler correction is nonzero in the open right
half-plane. -/
theorem primitiveEulerCorrection_ne_zero_of_re_pos {q : Nat}
    (chi : DirichletCharacter Complex q) {s : Complex} (hs : 0 < s.re) :
    primitiveEulerCorrection chi s ≠ 0 := by
  rw [primitiveEulerCorrection, Finset.prod_ne_zero_iff]
  intro p hp
  exact primitiveEulerFactor_ne_zero_of_re_pos chi.primitiveCharacter
    (Nat.prime_of_mem_primeFactors hp) hs

/-- The logarithmic derivative of the finite correction is the sum of the
local logarithmic derivatives. -/
theorem logDeriv_primitiveEulerCorrection {q : Nat}
    (chi : DirichletCharacter Complex q) {s : Complex} (hs : 0 < s.re) :
    logDeriv (primitiveEulerCorrection chi) s =
      primitiveEulerLogDerivCorrection chi s := by
  change logDeriv (fun z ↦ ∏ p ∈ q.primeFactors,
    primitiveEulerFactor chi.primitiveCharacter p z) s = _
  rw [primitiveEulerLogDerivCorrection, logDeriv_prod]
  · apply Finset.sum_congr rfl
    intro p hp
    exact logDeriv_primitiveEulerFactor chi.primitiveCharacter
      (Nat.prime_of_mem_primeFactors hp) s
  · intro p hp
    exact primitiveEulerFactor_ne_zero_of_re_pos chi.primitiveCharacter
      (Nat.prime_of_mem_primeFactors hp) hs
  · intro p hp
    exact (primitiveEulerFactor_hasDerivAt chi.primitiveCharacter
      (Nat.prime_of_mem_primeFactors hp) s).differentiableAt

/-- Imprimitive and primitive L-functions have exactly the same zeros in the
open right half-plane, away from the principal pole. -/
theorem LFunction_eq_zero_iff_primitive {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) [NeZero chi.conductor]
    {s : Complex} (hs : 0 < s.re)
    (hregular : chi.primitiveCharacter ≠ 1 ∨ s ≠ 1) :
    chi.LFunction s = 0 ↔ chi.primitiveCharacter.LFunction s = 0 := by
  rw [LFunction_eq_primitive_mul_eulerCorrection chi hregular,
    mul_eq_zero]
  simp only [primitiveEulerCorrection_ne_zero_of_re_pos chi hs, or_false]

/-- Branch-free logarithmic derivatives differ by the explicit finite Euler
correction. The primitive L-value must be nonzero because division is
totalized in Lean. -/
theorem logDeriv_LFunction_eq_primitive_add {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) [NeZero chi.conductor]
    {s : Complex} (hs : 0 < s.re)
    (hregular : chi.primitiveCharacter ≠ 1 ∨ s ≠ 1)
    (hL : chi.primitiveCharacter.LFunction s ≠ 0) :
    logDeriv chi.LFunction s = logDeriv chi.primitiveCharacter.LFunction s +
      primitiveEulerLogDerivCorrection chi s := by
  have hE := primitiveEulerCorrection_ne_zero_of_re_pos chi hs
  have hdL : DifferentiableAt Complex chi.primitiveCharacter.LFunction s :=
    differentiableAt_LFunction chi.primitiveCharacter s
      (hregular.elim Or.inr Or.inl)
  have hdE : DifferentiableAt Complex (primitiveEulerCorrection chi) s := by
    change DifferentiableAt Complex (fun z ↦ ∏ p ∈ q.primeFactors,
      primitiveEulerFactor chi.primitiveCharacter p z) s
    exact .fun_finsetProd fun p hp ↦
      (primitiveEulerFactor_hasDerivAt chi.primitiveCharacter
        (Nat.prime_of_mem_primeFactors hp) s).differentiableAt
  have heq : chi.LFunction =ᶠ[nhds s]
      fun z ↦ chi.primitiveCharacter.LFunction z *
        primitiveEulerCorrection chi z := by
    rcases hregular with hchi | hs1
    · exact Filter.Eventually.of_forall fun z ↦
        LFunction_eq_primitive_mul_eulerCorrection chi (.inl hchi)
    · filter_upwards [eventually_ne_nhds hs1] with z hz
      exact LFunction_eq_primitive_mul_eulerCorrection chi (.inr hz)
  calc
    logDeriv chi.LFunction s =
        logDeriv (fun z ↦ chi.primitiveCharacter.LFunction z *
          primitiveEulerCorrection chi z) s := by
      rw [logDeriv_apply, logDeriv_apply, heq.deriv_eq,
        heq.self_of_nhds]
    _ = logDeriv chi.primitiveCharacter.LFunction s +
        logDeriv (primitiveEulerCorrection chi) s :=
      logDeriv_mul s hL hE hdL hdE
    _ = _ := by rw [logDeriv_primitiveEulerCorrection chi hs]

/-- The correction has the opposite sign for the negative logarithmic
derivative used in Perron's formula. -/
theorem neg_logDeriv_LFunction_eq_primitive_sub {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) [NeZero chi.conductor]
    {s : Complex} (hs : 0 < s.re)
    (hregular : chi.primitiveCharacter ≠ 1 ∨ s ≠ 1)
    (hL : chi.primitiveCharacter.LFunction s ≠ 0) :
    -logDeriv chi.LFunction s =
      -logDeriv chi.primitiveCharacter.LFunction s -
        primitiveEulerLogDerivCorrection chi s := by
  rw [logDeriv_LFunction_eq_primitive_add chi hs hregular hL]
  ring

end PrimesRestrictedDigits
