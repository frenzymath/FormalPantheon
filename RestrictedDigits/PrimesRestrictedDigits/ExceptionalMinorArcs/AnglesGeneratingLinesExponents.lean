import PrimesRestrictedDigits.ExceptionalMinorArcs.ComparableMagnitudeBand
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Exponents for the bound on angles generating lines

These exact rational identities and fixed-coefficient absorptions are the arithmetic in
`MAYNARD-PRD-PUBLISHED`, Proposition 13.4.
-/

open Filter

namespace PrimesRestrictedDigits

/-- The strict upper limit on the power saving furnished by the trivial
branch of Proposition 13.4. -/
noncomputable def anglesGeneratingLinesSavingLimit : Real := 127 / 2667280

/-- The explicit saving in the line-counting corollary. -/
noncomputable def anglesGeneratingLinesSaving : Real := 127 / 21338240

theorem anglesGeneratingLinesSavingLimit_pos :
    0 < anglesGeneratingLinesSavingLimit := by
  norm_num [anglesGeneratingLinesSavingLimit]

theorem anglesGeneratingLinesSaving_pos :
    0 < anglesGeneratingLinesSaving := by
  norm_num [anglesGeneratingLinesSaving]

theorem anglesGeneratingLinesSaving_lt_limit :
    anglesGeneratingLinesSaving < anglesGeneratingLinesSavingLimit := by
  norm_num [anglesGeneratingLinesSaving, anglesGeneratingLinesSavingLimit]

/-- The `B` exponent left in the trivial branch. -/
theorem anglesGeneratingLines_two_mul_moment_sub_three :
    2 * (235 / 154 : Real) - 3 = 4 / 77 := by
  norm_num

/-- The exact raw saving in the trivial branch. -/
theorem anglesGeneratingLines_trivial_exponent :
    2 * (59 / 433 : Real) + 57 / 80 +
        (23 / 80) * (2 * (235 / 154) - 3) =
      1 - anglesGeneratingLinesSavingLimit := by
  norm_num [anglesGeneratingLinesSavingLimit]

/-- The maximal comparable-band cardinality exponent. -/
theorem anglesGeneratingLines_band_card_exponent :
    (23 / 80 : Real) * (235 / 154) + 59 / 433 =
      23 / 40 - 127 / 5334560 := by
  norm_num

/-- The first bracket exponent after the large-`N*K` reduction. -/
theorem anglesGeneratingLines_first_bracket_exponent :
    (5 / 4 : Real) *
        ((23 / 80) * (235 / 154) + 59 / 433) =
      23 / 32 - (5 / 4) * (127 / 5334560) := by
  norm_num

/-- The second bracket exponent after the large-`N*K` reduction. -/
theorem anglesGeneratingLines_second_bracket_exponent :
    (3 / 2 : Real) *
          ((23 / 80) * (235 / 154) + 59 / 433) -
        1 / 2 + 2 * (23 / 80) =
      15 / 16 - (3 / 2) * (127 / 5334560) := by
  norm_num

/-- The first final saving after using `N>=X^(9/25)`. -/
noncomputable def anglesGeneratingLinesFirstSaving : Real :=
  1 / 800 + (5 / 4) * (127 / 5334560)

/-- The second final saving after using `N>=X^(9/25)`. -/
noncomputable def anglesGeneratingLinesSecondSaving : Real :=
  57 / 400 + (3 / 2) * (127 / 5334560)

theorem anglesGeneratingLines_secondSaving_gt_firstSaving :
    anglesGeneratingLinesFirstSaving <
      anglesGeneratingLinesSecondSaving := by
  norm_num [anglesGeneratingLinesFirstSaving,
    anglesGeneratingLinesSecondSaving]

theorem anglesGeneratingLines_four_momentGap_lt_firstSaving :
    4 * (127 / 5334560 : Real) <
      anglesGeneratingLinesFirstSaving := by
  norm_num [anglesGeneratingLinesFirstSaving]

/-- The two fixed coefficients are absorbed uniformly at decimal scales. -/
theorem exists_anglesGeneratingLinesCoefficientThreshold
    (eta : Real) (_heta : 0 < eta)
    (hetaMax : eta < anglesGeneratingLinesSavingLimit) :
    exists length0 : Nat, forall length : Nat, length0 <= length ->
      let X : Real := ((10 ^ length : Nat) : Real)
      (10 : Real) ^ (2 * (235 / 154 : Real)) <=
          X ^ (anglesGeneratingLinesSavingLimit - eta) ∧
        16 * (10 : Real) ^
              ((5 / 4 : Real) * (235 / 154 : Real)) +
            64 * (10 : Real) ^
              ((3 / 2 : Real) * (235 / 154 : Real)) <=
          X ^ (anglesGeneratingLinesFirstSaving - 2 * eta) := by
  have htrivialGap : 0 < anglesGeneratingLinesSavingLimit - eta := by
    linarith
  have hfirstGap : 0 < anglesGeneratingLinesFirstSaving - 2 * eta := by
    have hlimit : anglesGeneratingLinesSavingLimit =
        2 * (127 / 5334560 : Real) := by
      norm_num [anglesGeneratingLinesSavingLimit]
    have hfour : 4 * (127 / 5334560 : Real) <
        anglesGeneratingLinesFirstSaving :=
      anglesGeneratingLines_four_momentGap_lt_firstSaving
    rw [hlimit] at hetaMax
    linarith
  have hscale :
      Tendsto (fun length : Nat => ((10 ^ length : Nat) : Real))
        atTop atTop := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      (tendsto_pow_atTop_atTop_of_one_lt
        (by norm_num : (1 : Real) < 10))
  have htrivialGrowth :=
    (tendsto_rpow_atTop htrivialGap).comp hscale
  have hlineGrowth := (tendsto_rpow_atTop hfirstGap).comp hscale
  obtain ⟨lengthTrivial, hlengthTrivial⟩ := eventually_atTop.mp
    (htrivialGrowth.eventually_ge_atTop
      ((10 : Real) ^ (2 * (235 / 154 : Real))))
  obtain ⟨lengthLine, hlengthLine⟩ := eventually_atTop.mp
    (hlineGrowth.eventually_ge_atTop
      (16 * (10 : Real) ^
          ((5 / 4 : Real) * (235 / 154 : Real)) +
        64 * (10 : Real) ^
          ((3 / 2 : Real) * (235 / 154 : Real))))
  refine ⟨max lengthTrivial lengthLine, ?_⟩
  intro length hlength
  exact ⟨hlengthTrivial length (by omega),
    hlengthLine length (by omega)⟩

end PrimesRestrictedDigits
