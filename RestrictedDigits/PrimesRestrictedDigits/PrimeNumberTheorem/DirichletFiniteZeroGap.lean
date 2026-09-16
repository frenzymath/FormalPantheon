import PrimesRestrictedDigits.PrimeNumberTheorem.FiniteCharacterZeroGap

/-!
# Complex zero gaps for decimal-smooth quadratic characters

This file proves the complex punctured-neighborhood bridges. They strengthen the real
corollaries and will replace the low-height quadratic cases in the decimal-smooth
specialization of `MONTGOMERY-VAUGHAN-MNT-I`, Theorem 11.3.
-/

namespace PrimesRestrictedDigits

open DirichletCharacter

/-- Primitive quadratic characters induced from positive decimal-smooth
levels have one common complex zero gap around one, with the pole removed. -/
theorem exists_decimalSmooth_quadratic_primitive_LFunction_zero_gap :
    ∃ radius : Real, 0 < radius ∧ radius ≤ 1 / 2 ∧
      ∀ {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q),
        IsDecimalSmooth q → chi.IsQuadratic →
          letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
          ∀ {s : Complex}, s ≠ 1 → dist s 1 ≤ radius →
            chi.primitiveCharacter.LFunction s ≠ 0 := by
  obtain ⟨radius, hradius, hradius_le, hgap⟩ :=
    exists_decimalConductor_LFunction_ne_zero_punctured_one
  refine ⟨radius, hradius, hradius_le, ?_⟩
  intro q _ chi hq hchi s hs hdist
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  exact hgap (quadratic_conductor_mem chi hq hchi)
    chi.primitiveCharacter hs hdist

/-- Every quadratic character at a positive decimal-smooth level has the
same complex zero gap as its primitive inducer. -/
theorem exists_decimalSmooth_quadratic_LFunction_zero_gap :
    ∃ radius : Real, 0 < radius ∧ radius ≤ 1 / 2 ∧
      ∀ {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q),
        IsDecimalSmooth q → chi.IsQuadratic →
          ∀ {s : Complex}, s ≠ 1 → dist s 1 ≤ radius →
            chi.LFunction s ≠ 0 := by
  obtain ⟨radius, hradius, hradius_le, hprimitive⟩ :=
    exists_decimalSmooth_quadratic_primitive_LFunction_zero_gap
  refine ⟨radius, hradius, hradius_le, ?_⟩
  intro q _ chi hq hchi s hs hdist
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have habs : |s.re - 1| ≤ (1 : Real) / 2 := by
    have hre : |s.re - 1| ≤ dist s 1 := by
      rw [dist_eq_norm]
      simpa using Complex.abs_re_le_norm (s - 1)
    exact hre.trans (hdist.trans hradius_le)
  have hsRe : 0 < s.re := by
    have hlower := (abs_le.mp habs).1
    linarith
  have hprim := hprimitive chi hq hchi hs hdist
  intro hzero
  exact hprim ((LFunction_eq_zero_iff_primitive chi hsRe (.inr hs)).1 hzero)

end PrimesRestrictedDigits
