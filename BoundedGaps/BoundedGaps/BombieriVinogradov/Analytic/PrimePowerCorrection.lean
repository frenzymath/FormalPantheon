import BoundedGaps.BombieriVinogradov.Analytic.PrimitiveCharacterReduction

/-!
# Prime-power support of the imprimitive correction

This file implements the finite support rewrite reviewed in SEM-415. It
rewrites the primitive character's non-coprime correction using Mathlib's
von Mangoldt formula and records the resulting least-prime-factor divisibility.
It proves no conductor-dependent estimate or divisor-count bound.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators ArithmeticFunction.vonMangoldt

/-- The finite prime-power part of a twisted non-coprime remainder. -/
noncomputable def primePowerCorrectionSum
    (x q r : ℕ) (χ : DirichletCharacter ℂ r) : ℂ :=
  ∑ n ∈ Finset.Icc 1 x with IsPrimePow n ∧ ¬Nat.Coprime n q,
    χ n * (Real.log (n.minFac : ℝ) : ℂ)

theorem nonCoprimeTwistedChebyshevSum_eq_primePowerCorrectionSum
    (x q r : ℕ) (χ : DirichletCharacter ℂ r) :
    (∑ n ∈ Finset.Icc 1 x with ¬Nat.Coprime n q,
      χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) =
      primePowerCorrectionSum x q r χ := by
  unfold primePowerCorrectionSum
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hpp : IsPrimePow n
  · simp only [ArithmeticFunction.vonMangoldt_apply, if_pos hpp]
    by_cases hcop : Nat.Coprime n q
    · simp [hcop, hpp]
    · simp [hcop, hpp]
  · simp only [ArithmeticFunction.vonMangoldt_apply, if_neg hpp]
    simp [hpp]

theorem minFac_dvd_of_isPrimePow_not_coprime
    {n q : ℕ} (hn : IsPrimePow n) (hnot : ¬Nat.Coprime n q) :
    n.minFac ∣ q := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn
  have hnotp : ¬Nat.Coprime p q := by
    intro hcp
    apply hnot
    exact (Nat.coprime_pow_left_iff hk p q).2 hcp
  have hpdvd : p ∣ q := by
    by_contra hpdvd
    exact hnotp (hp.coprime_iff_not_dvd.mpr hpdvd)
  rw [hp.pow_minFac hk.ne']
  exact hpdvd

theorem not_coprime_iff_minFac_dvd_of_isPrimePow
    {n q : ℕ} (hn : IsPrimePow n) :
    ¬Nat.Coprime n q ↔ n.minFac ∣ q := by
  constructor
  · exact minFac_dvd_of_isPrimePow_not_coprime hn
  · intro hdiv hcop
    have hmin_coprime : Nat.Coprime n.minFac q :=
      hcop.coprime_dvd_left (Nat.minFac_dvd n)
    exact (Nat.minFac_prime hn.ne_one).coprime_iff_not_dvd.mp hmin_coprime hdiv

theorem primitiveTwistedChebyshevSum_eq_add_primePowerCorrection
    (x q : ℕ) (χ : DirichletCharacter ℂ q) :
    twistedChebyshevSum x χ.conductor χ.primitiveCharacter =
      twistedChebyshevSum x q χ +
        primePowerCorrectionSum x q χ.conductor χ.primitiveCharacter := by
  rw [primitiveTwistedChebyshevSum_eq_add_correction]
  rw [nonCoprimeTwistedChebyshevSum_eq_primePowerCorrectionSum]

end BoundedGaps.Maynard
