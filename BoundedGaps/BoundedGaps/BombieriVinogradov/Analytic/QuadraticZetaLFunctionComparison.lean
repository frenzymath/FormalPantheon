import BoundedGaps.BombieriVinogradov.Analytic.QuadraticZetaSwappedEulerRemainder
import BoundedGaps.BombieriVinogradov.Analytic.NonprincipalLFunctionAbel

/-!
# Comparison with the ordered value at one

The direct Euler expansion and the ordered reciprocal-prefix estimate give a
quantitative comparison with `L(1, chi)`.  The theorem leaves the swapped
Euler remainder as an explicit hypothesis; this is the bridge consumed by the
later analytic lower-bound route.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed pp. 124--125.
Semantic review: `SEM-546`.
-/

noncomputable section

open scoped BigOperators

namespace BoundedGaps.Maynard

/-- The smoothed quadratic sum differs from its `L(1, chi)` main term by the
reciprocal-prefix error and the explicitly displayed Euler remainder. -/
theorem norm_quadraticZetaLinearSmoothedSum_sub_half_LFunction_le
    {q X : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) (hX : 0 < X)
    (B : ℝ)
    (hB : ‖quadraticZetaSwappedEulerRemainder chi X‖ ≤ B) :
    ‖quadraticZetaLinearSmoothedSum chi X -
        ((X : ℂ) / 2) * DirichletCharacter.LFunction chi (1 : ℂ)‖ ≤
      2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) + B := by
  let P : ℂ := ∑ a ∈ Finset.Icc 1 X,
    chi (a : ZMod q) / (a : ℂ)
  let S : ℝ := Real.sqrt (q : ℝ) * Real.log (q : ℝ)
  have htail := norm_LFunction_one_sub_dirichletCharacterReciprocalPrefix_le
    hq chi hchi X hX
  have htail' : ‖P - DirichletCharacter.LFunction chi (1 : ℂ)‖ ≤
      4 * S / (X : ℝ) := by
    rw [norm_sub_rev]
    dsimp [P, S]
    convert htail using 1 ; ring
  have hXreal : (0 : ℝ) < X := by exact_mod_cast hX
  have hmain := quadraticZetaLinearSmoothedSum_eq_directEulerRemainder chi hX
  have hswap := quadraticZetaDirectEulerRemainder_eq_swapped chi hX
  have hscale : ‖((X : ℂ) / 2)‖ = (X : ℝ) / 2 := by
    rw [norm_div, Complex.norm_natCast]
    norm_num
  have hscaled : ‖((X : ℂ) / 2) *
        (P - DirichletCharacter.LFunction chi (1 : ℂ))‖ ≤ 2 * S := by
    rw [norm_mul, hscale]
    calc
      ((X : ℝ) / 2) * ‖P - DirichletCharacter.LFunction chi (1 : ℂ)‖ ≤
          ((X : ℝ) / 2) * (4 * S / (X : ℝ)) :=
        mul_le_mul_of_nonneg_left htail' (by positivity)
      _ = 2 * S := by
        field_simp [hXreal.ne']
        ring
  calc
    ‖quadraticZetaLinearSmoothedSum chi X -
        ((X : ℂ) / 2) * DirichletCharacter.LFunction chi (1 : ℂ)‖ =
        ‖((X : ℂ) / 2) *
            (P - DirichletCharacter.LFunction chi (1 : ℂ)) -
          quadraticZetaSwappedEulerRemainder chi X‖ := by
      rw [hmain, hswap]
      dsimp [P]
      ring_nf
    _ ≤ ‖((X : ℂ) / 2) *
          (P - DirichletCharacter.LFunction chi (1 : ℂ))‖ +
        ‖quadraticZetaSwappedEulerRemainder chi X‖ := norm_sub_le _ _
    _ ≤ 2 * S + B := add_le_add hscaled hB
    _ = 2 * Real.sqrt (q : ℝ) * Real.log (q : ℝ) + B := by
      dsimp [S]
      ring

end BoundedGaps.Maynard
