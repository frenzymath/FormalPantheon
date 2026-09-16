import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.MulChar.Duality
import PrimesRestrictedDigits.PrimeNumberTheorem.PrimitiveEulerFactors
import PrimesRestrictedDigits.PrimeNumberTheorem.QuadraticConductor

/-!
# A uniform zero gap for the finite family of decimal conductors

This file implements the finite-family argument. Nonvanishing at one and continuity give a
common punctured neighborhood for all characters at a fixed level. Taking the minimum over the
six possible decimal quadratic conductors gives the real zero gap needed downstream.

The source zero-free region is `MONTGOMERY-VAUGHAN-MNT-I`, Theorem 11.3, pp. 360--362. The
finite six-conductor gap is a project-derived qualitative consequence using Mathlib's
kernel-checked nonvanishing theorem at one.
-/

namespace PrimesRestrictedDigits

open DirichletCharacter

/-- At a fixed positive level, all Dirichlet L-functions are nonzero in one
common closed punctured ball around one. The principal pole is handled via
the regularized function `LFunctionTrivChar₁`. -/
theorem exists_uniform_LFunction_ne_zero_punctured_one
    (q : Nat) [NeZero q] :
    ∃ radius : Real, 0 < radius ∧ radius ≤ 1 / 2 ∧
      ∀ (chi : DirichletCharacter Complex q) {s : Complex},
        s ≠ 1 → dist s 1 ≤ radius → chi.LFunction s ≠ 0 := by
  have hnonprincipal :
      ∀ᶠ s in nhds (1 : Complex),
        ∀ chi : DirichletCharacter Complex q,
          chi ≠ 1 → chi.LFunction s ≠ 0 := by
    rw [Filter.eventually_all]
    intro chi
    by_cases hchi : chi = 1
    · exact Filter.Eventually.of_forall fun _ hs ↦ (hs hchi).elim
    · exact
        ((differentiable_LFunction hchi).continuous.continuousAt.eventually_ne
          (LFunction_apply_one_ne_zero hchi)).mono fun _ hs _ ↦ hs
  have hprincipal :
      ∀ᶠ s in nhds (1 : Complex), LFunctionTrivChar₁ q s ≠ 0 :=
    (differentiable_LFunctionTrivChar₁ q).continuous.continuousAt.eventually_ne
      (LFunctionTrivChar₁_apply_one_ne_zero q)
  have hnear := hnonprincipal.and hprincipal
  rw [Metric.eventually_nhds_iff] at hnear
  obtain ⟨epsilon, hepsilon, hnear⟩ := hnear
  refine ⟨min (epsilon / 2) (1 / 2), by positivity,
    min_le_right _ _, ?_⟩
  intro chi s hs hdist
  have hs_epsilon : dist s 1 < epsilon :=
    lt_of_le_of_lt (hdist.trans (min_le_left _ _)) (by linarith)
  by_cases hchi : chi = 1
  · subst chi
    have hregularized := (hnear hs_epsilon).2
    rw [LFunctionTrivChar₁, Function.update_of_ne hs] at hregularized
    exact (mul_ne_zero_iff.mp hregularized).2
  · exact (hnear hs_epsilon).1 chi hchi

/-- One radius works for all characters at each of the six possible decimal
quadratic conductor levels. -/
theorem exists_decimalConductor_LFunction_ne_zero_punctured_one :
    ∃ radius : Real, 0 < radius ∧ radius ≤ 1 / 2 ∧
      ∀ {q : Nat} [NeZero q], q ∈ decimalQuadraticConductors →
        ∀ (chi : DirichletCharacter Complex q) {s : Complex},
          s ≠ 1 → dist s 1 ≤ radius → chi.LFunction s ≠ 0 := by
  obtain ⟨r1, hr1, hr1_le, h1⟩ :=
    exists_uniform_LFunction_ne_zero_punctured_one 1
  obtain ⟨r4, hr4, _, h4⟩ :=
    exists_uniform_LFunction_ne_zero_punctured_one 4
  obtain ⟨r5, hr5, _, h5⟩ :=
    exists_uniform_LFunction_ne_zero_punctured_one 5
  obtain ⟨r8, hr8, _, h8⟩ :=
    exists_uniform_LFunction_ne_zero_punctured_one 8
  obtain ⟨r20, hr20, _, h20⟩ :=
    exists_uniform_LFunction_ne_zero_punctured_one 20
  obtain ⟨r40, hr40, _, h40⟩ :=
    exists_uniform_LFunction_ne_zero_punctured_one 40
  let radius := min r1 (min r4 (min r5 (min r8 (min r20 r40))))
  refine ⟨radius, by dsimp only [radius]; positivity,
    (min_le_left _ _).trans hr1_le, ?_⟩
  intro q _ hq chi s hs hdist
  simp only [decimalQuadraticConductors, Finset.mem_insert,
    Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1 chi hs (hdist.trans (by simp [radius]))
  · exact h4 chi hs (hdist.trans (by simp [radius]))
  · exact h5 chi hs (hdist.trans (by simp [radius]))
  · exact h8 chi hs (hdist.trans (by simp [radius]))
  · exact h20 chi hs (hdist.trans (by simp [radius]))
  · exact h40 chi hs (hdist.trans (by simp [radius]))

/-- Primitive quadratic characters induced from decimal-smooth levels have
one common real zero gap immediately to the left of one. -/
theorem exists_decimalSmooth_quadratic_primitive_LFunction_real_zero_gap :
    ∃ radius : Real, 0 < radius ∧ radius ≤ 1 / 2 ∧
      ∀ {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q),
        IsDecimalSmooth q → chi.IsQuadratic →
          letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
          ∀ x : Real, 1 - radius ≤ x → x < 1 →
            chi.primitiveCharacter.LFunction (x : Complex) ≠ 0 := by
  obtain ⟨radius, hradius, hradius_le, hgap⟩ :=
    exists_decimalConductor_LFunction_ne_zero_punctured_one
  refine ⟨radius, hradius, hradius_le, ?_⟩
  intro q _ chi hq hchi x hx hlt
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  apply hgap (quadratic_conductor_mem chi hq hchi) chi.primitiveCharacter
  · exact_mod_cast ne_of_lt hlt
  · have hdist : dist (x : Complex) 1 = 1 - x := by
      rw [dist_eq_norm, ← Complex.ofReal_one, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos]
      · ring
      · linarith
    rw [hdist]
    linarith

/-- Every quadratic character at a decimal-smooth level has the same real
zero gap as its primitive inducer. -/
theorem exists_decimalSmooth_quadratic_LFunction_real_zero_gap :
    ∃ radius : Real, 0 < radius ∧ radius ≤ 1 / 2 ∧
      ∀ {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q),
        IsDecimalSmooth q → chi.IsQuadratic →
          ∀ x : Real, 1 - radius ≤ x → x < 1 →
            chi.LFunction (x : Complex) ≠ 0 := by
  obtain ⟨radius, hradius, hradius_le, hprimitive⟩ :=
    exists_decimalSmooth_quadratic_primitive_LFunction_real_zero_gap
  refine ⟨radius, hradius, hradius_le, ?_⟩
  intro q _ chi hq hchi x hx hlt
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hprim := hprimitive chi hq hchi x hx hlt
  have hxpos : 0 < x := by linarith
  intro hzero
  have hregular : chi.primitiveCharacter ≠ 1 ∨ (x : Complex) ≠ 1 :=
    Or.inr (by exact_mod_cast ne_of_lt hlt)
  have hzprim := (LFunction_eq_zero_iff_primitive chi
    (by simpa only [Complex.ofReal_re] using hxpos) hregular).1 hzero
  exact hprim hzprim

end PrimesRestrictedDigits
