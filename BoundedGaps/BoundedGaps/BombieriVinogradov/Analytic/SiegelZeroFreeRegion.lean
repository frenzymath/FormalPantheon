import BoundedGaps.BombieriVinogradov.Analytic.GoldfeldExceptionalCharacter
import BoundedGaps.BombieriVinogradov.Analytic.InducingEulerProduct
import BoundedGaps.BombieriVinogradov.Analytic.QuadraticRealZeroGap

/-!
# Siegel's real-character zero-free region

The optional primitive exception from Goldfeld's argument is a single fixed
character.  Its explicit weak zero gap therefore removes it after a
noncomputable shrinking of the common constant.  Equation (11.2) then
transports the result from primitive conductors to arbitrary character levels.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, Theorem 12.10, printed
p. 127, and equation (11.2), printed p. 110. Semantic review: `SEM-562`.
-/

noncomputable section

open Complex

namespace BoundedGaps.Maynard

/-- After fixing the exponent, one positive constant gives a real-axis
zero-free region for every primitive real nonprincipal character. -/
theorem exists_siegelPrimitiveRealCharacterZeroFree :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ c : ℝ, 0 < c ∧
        ∀ psi : GoldfeldPrimitiveRealCharacter,
          goldfeldPrimitiveZeroFree epsilon c psi := by
  intro epsilon hepsilon
  obtain ⟨c0, hc0, exception, hzeroFree⟩ :=
    exists_goldfeldPrimitiveExceptionalCharacter epsilon hepsilon
  cases exception with
  | none =>
      let c : ℝ := min c0 (1 / 2)
      have hcPos : 0 < c := by
        dsimp [c]
        exact lt_min hc0 (by norm_num)
      refine ⟨c, hcPos, ?_⟩
      intro psi sigma hsigma
      apply hzeroFree psi (by simp) sigma
      have hcLe : c ≤ c0 := by
        dsimp [c]
        exact min_le_left _ _
      have hweightNonneg :
          0 ≤ (psi.modulus : ℝ) ^ (-epsilon) :=
        Real.rpow_nonneg (Nat.cast_nonneg psi.modulus) _
      have hscaled :=
        mul_le_mul_of_nonneg_right hcLe hweightNonneg
      linarith
  | some exception =>
      let gap : ℝ :=
        1 / ((2 ^ 22 : ℝ) * Real.sqrt (exception.modulus : ℝ) *
          (Real.log (exception.modulus : ℝ)) ^ 4)
      let weight : ℝ :=
        (exception.modulus : ℝ) ^ (-epsilon)
      let c : ℝ := min (min c0 (1 / 2)) (gap / weight)
      have hmodulusPos : (0 : ℝ) < exception.modulus := by
        exact_mod_cast (Nat.zero_lt_of_lt exception.modulus_gt_one)
      have hlogPos : 0 < Real.log (exception.modulus : ℝ) :=
        Real.log_pos (by exact_mod_cast exception.modulus_gt_one)
      have hgapPos : 0 < gap := by
        dsimp [gap]
        positivity
      have hweightPos : 0 < weight := by
        dsimp [weight]
        exact Real.rpow_pos_of_pos hmodulusPos _
      have hcPos : 0 < c := by
        dsimp [c]
        exact lt_min (lt_min hc0 (by norm_num))
          (div_pos hgapPos hweightPos)
      have hcLe : c ≤ c0 := by
        dsimp [c]
        exact (min_le_left _ _).trans (min_le_left _ _)
      have hcGap : c * weight ≤ gap := by
        apply (le_div_iff₀ hweightPos).mp
        dsimp [c]
        exact min_le_right _ _
      refine ⟨c, hcPos, ?_⟩
      intro psi
      by_cases hpsi : psi = exception
      · subst psi
        intro sigma hsigma
        apply effectiveQuadraticLFunction_ofReal_ne_zero
          exception.modulus_gt_one exception.character exception.ne_one
            exception.sq_eq_one
        have hthreshold : 1 - gap ≤ 1 - c * weight := by
          linarith
        exact hthreshold.trans_lt (by simpa [weight] using hsigma)
      · intro sigma hsigma
        apply hzeroFree psi (by simpa using hpsi) sigma
        have hweightNonneg :
            0 ≤ (psi.modulus : ℝ) ^ (-epsilon) :=
          Real.rpow_nonneg (Nat.cast_nonneg psi.modulus) _
        have hscaled :=
          mul_le_mul_of_nonneg_right hcLe hweightNonneg
        linarith

/-- Siegel's theorem for every real nonprincipal character, including
imprimitive characters. The witness may depend noncomputably on the optional
global primitive exception selected after the exponent is fixed. -/
theorem exists_siegelRealCharacterZeroFree :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ c : ℝ, 0 < c ∧
        ∀ (q : ℕ) [NeZero q]
          (chi : DirichletCharacter ℂ q),
            chi ≠ 1 →
              chi ^ 2 = 1 →
                ∀ sigma : ℝ,
                  1 - c * (q : ℝ) ^ (-epsilon) < sigma →
                    DirichletCharacter.LFunction chi (sigma : ℂ) ≠ 0 := by
  intro epsilon hepsilon
  obtain ⟨c0, hc0, hprimitive⟩ :=
    exists_siegelPrimitiveRealCharacterZeroFree epsilon hepsilon
  let c : ℝ := min c0 (1 / 2)
  have hcPos : 0 < c := by
    dsimp [c]
    exact lt_min hc0 (by norm_num)
  have hcLe : c ≤ c0 := by
    dsimp [c]
    exact min_le_left _ _
  have hcHalf : c ≤ 1 / 2 := by
    dsimp [c]
    exact min_le_right _ _
  refine ⟨c, hcPos, ?_⟩
  intro q _ chi hchi hsquare sigma hsigma
  have hconductorOne : 1 < chi.conductor := by
    have hconductorZero : chi.conductor ≠ 0 := chi.conductor_ne_zero
    have hconductorNeOne : chi.conductor ≠ 1 := by
      intro hconductor
      exact hchi
        (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr hconductor)
    omega
  letI : NeZero chi.conductor := ⟨chi.conductor_ne_zero⟩
  have hprimitiveNeOne : chi.primitiveCharacter ≠ 1 := by
    intro hprincipal
    apply hchi
    rw [← chi.changeLevel_primitiveCharacter]
    exact (DirichletCharacter.changeLevel_eq_one_iff
      chi.conductor_dvd_level).2 hprincipal
  have hprimitiveSquare : chi.primitiveCharacter ^ 2 = 1 := by
    apply DirichletCharacter.changeLevel_injective
      chi.conductor_dvd_level
    rw [map_pow, chi.changeLevel_primitiveCharacter, hsquare, map_one]
  let psi : GoldfeldPrimitiveRealCharacter :=
    { modulus := chi.conductor
      modulus_gt_one := hconductorOne
      character := chi.primitiveCharacter
      isPrimitive := chi.primitiveCharacter_isPrimitive
      ne_one := hprimitiveNeOne
      sq_eq_one := hprimitiveSquare }
  have hconductorLe : chi.conductor ≤ q :=
    Nat.le_of_dvd (NeZero.pos q) chi.conductor_dvd_level
  have hconductorPos : (0 : ℝ) < chi.conductor := by
    exact_mod_cast (Nat.zero_lt_of_lt hconductorOne)
  have hconductorLevel : (chi.conductor : ℝ) ≤ q := by
    exact_mod_cast hconductorLe
  have hnegativePower :
      (q : ℝ) ^ (-epsilon) ≤
        (chi.conductor : ℝ) ^ (-epsilon) :=
    Real.rpow_le_rpow_of_nonpos hconductorPos hconductorLevel
      (by linarith)
  have hconductorWeightNonneg :
      0 ≤ (chi.conductor : ℝ) ^ (-epsilon) :=
    Real.rpow_nonneg (Nat.cast_nonneg chi.conductor) _
  have hscaled :
      c * (q : ℝ) ^ (-epsilon) ≤
        c0 * (chi.conductor : ℝ) ^ (-epsilon) := by
    calc
      c * (q : ℝ) ^ (-epsilon) ≤
          c * (chi.conductor : ℝ) ^ (-epsilon) :=
        mul_le_mul_of_nonneg_left hnegativePower hcPos.le
      _ ≤ c0 * (chi.conductor : ℝ) ^ (-epsilon) :=
        mul_le_mul_of_nonneg_right hcLe hconductorWeightNonneg
  have hprimitiveThreshold :
      1 - c0 * (chi.conductor : ℝ) ^ (-epsilon) < sigma := by
    linarith
  have hprimitiveNonzero :
      DirichletCharacter.LFunction chi.primitiveCharacter
          (sigma : ℂ) ≠ 0 := by
    apply hprimitive psi sigma
    simpa [psi] using hprimitiveThreshold
  have hlevelOne : (1 : ℝ) ≤ q := by
    exact_mod_cast NeZero.pos q
  have hlevelWeightLeOne :
      (q : ℝ) ^ (-epsilon) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hlevelOne (by linarith)
  have hscaledHalf : c * (q : ℝ) ^ (-epsilon) ≤ 1 / 2 :=
    (mul_le_of_le_one_right hcPos.le hlevelWeightLeOne).trans hcHalf
  have hsigmaPos : 0 < sigma := by
    linarith
  rw [LFunction_eq_inducingPrimitive_mul_inducingEulerProduct chi
    (.inl hchi)]
  exact mul_ne_zero hprimitiveNonzero
    (inducingEulerProduct_ne_zero_of_re_pos chi (by simpa using hsigmaPos))

end BoundedGaps.Maynard
