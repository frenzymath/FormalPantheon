import BoundedGaps.BombieriVinogradov.Analytic.SquareRootLogRange

/-!
# Raw primitive-character endpoint maxima

This file formalizes the centered-to-raw replacement on
Akbary--Hambrook2013v2, Section 7, p. 25. The replacement is made only on the
rough primitive-conductor side of SEM-425; the original all-character sum
remains centered.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable section

noncomputable local instance roughModulusAboveDecidableForRawMaxima
    (Q1 : ℝ) : DecidablePred (roughModulusAbove Q1) :=
  Classical.decPred _

/-- A primitive character at a level greater than one is nonprincipal. -/
theorem primitiveCharacter_ne_one_of_one_lt
    {d : ℕ} (hd : 1 < d) (ψ : primitiveCharacters d) :
    ψ.1 ≠ (1 : DirichletCharacter ℂ d) := by
  letI : NeZero d := ⟨by omega⟩
  intro hψ
  have hconductorOne : ψ.1.conductor = 1 :=
    (DirichletCharacter.eq_one_iff_conductor_eq_one).mp hψ
  have hconductorLevel : ψ.1.conductor = d :=
    (DirichletCharacter.isPrimitive_def ψ.1).mp ψ.2
  omega

/-- A primitive nonprincipal character has identical centered and raw
von Mangoldt twists. -/
theorem centeredTwistedChebyshevSum_eq_twisted_of_primitive
    {y d : ℕ} (hd : 1 < d) (ψ : primitiveCharacters d) :
    centeredTwistedChebyshevSum y d ψ.1 =
      twistedChebyshevSum y d ψ.1 := by
  classical
  simp [centeredTwistedChebyshevSum,
    primitiveCharacter_ne_one_of_one_lt hd ψ]

/-- Maximum raw primitive twist over the natural endpoints `2 <= y <= x`. -/
noncomputable def primitiveRawEndpointMaximum
    (x d : ℕ) (ψ : primitiveCharacters d) : ℝ :=
  if hx : 2 ≤ x then
    (Finset.Icc 2 x).sup' (weightedEndpointRange_nonempty hx)
      (fun y ↦ ‖twistedChebyshevSum y d ψ.1‖)
  else 0

/-- A raw primitive endpoint maximum is nonnegative. -/
theorem primitiveRawEndpointMaximum_nonneg
    (x d : ℕ) (ψ : primitiveCharacters d) :
    0 ≤ primitiveRawEndpointMaximum x d ψ := by
  unfold primitiveRawEndpointMaximum
  split_ifs with hx
  · exact (norm_nonneg _).trans (Finset.le_sup'
      (fun y ↦ ‖twistedChebyshevSum y d ψ.1‖)
      (weightedEndpointRange_nonempty hx).choose_spec)
  · rfl

/-- The full raw primitive-character endpoint mass is nonnegative. -/
theorem sum_primitiveRawEndpointMaximum_nonneg (x d : ℕ) :
    0 ≤ ∑ ψ : primitiveCharacters d,
      primitiveRawEndpointMaximum x d ψ := by
  apply Finset.sum_nonneg
  intro ψ hψ
  exact primitiveRawEndpointMaximum_nonneg x d ψ

/-- Centered and raw primitive endpoint maxima agree above level one. -/
theorem primitiveCenteredEndpointMaximum_eq_raw
    (x : ℕ) {d : ℕ} (hd : 1 < d)
    (ψ : primitiveCharacters d) :
    primitiveCenteredEndpointMaximum x d ψ =
      primitiveRawEndpointMaximum x d ψ := by
  classical
  unfold primitiveCenteredEndpointMaximum primitiveRawEndpointMaximum
  split_ifs with hx
  · apply Finset.sup'_congr (weightedEndpointRange_nonempty hx) rfl
    intro y hy
    rw [centeredTwistedChebyshevSum_eq_twisted_of_primitive hd ψ]
  · rfl

/-- Sum the centered-to-raw equality over all primitive characters at a
nontrivial level. -/
theorem sum_primitiveCenteredEndpointMaximum_eq_raw
    (x : ℕ) {d : ℕ} (hd : 1 < d) :
    (∑ ψ : primitiveCharacters d,
      primitiveCenteredEndpointMaximum x d ψ) =
      ∑ ψ : primitiveCharacters d,
        primitiveRawEndpointMaximum x d ψ := by
  apply Fintype.sum_congr
  intro ψ
  exact primitiveCenteredEndpointMaximum_eq_raw x hd ψ

/-- Replace centered primitive masses by raw masses on the rough conductor
support. The explicit roughness guard supplies `1 < d`. -/
theorem sum_conductorRough_invTotient_primitiveCentered_eq_raw
    (x Q : ℕ) (Q1 : ℝ) :
    (∑ d ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 d,
      (d.totient : ℝ)⁻¹ *
        ∑ ψ : primitiveCharacters d,
          primitiveCenteredEndpointMaximum x d ψ) =
      ∑ d ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 d,
        (d.totient : ℝ)⁻¹ *
          ∑ ψ : primitiveCharacters d,
            primitiveRawEndpointMaximum x d ψ := by
  apply Finset.sum_congr rfl
  intro d hdmem
  have hrough : roughModulusAbove Q1 d :=
    (Finset.mem_filter.mp hdmem).2
  rw [sum_primitiveCenteredEndpointMaximum_eq_raw x hrough.1]

/-- Source-facing form: the original centered all-character sum is bounded
by `5 * log x` times the raw primitive-conductor mass. -/
theorem sum_weightedInducingPrimitiveCenteredEndpointMaximum_le_five_log_raw
    (x Q : ℕ) (Q1 : ℝ) (hx : 4 ≤ x)
    (hQsqrt : (Q : ℝ) ≤ Real.sqrt (x : ℝ)) :
    (∑ q ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 q,
      (q.totient : ℝ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ q,
          inducingPrimitiveCenteredEndpointMaximum x q χ) ≤
      (5 * Real.log (x : ℝ)) *
        ∑ d ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 d,
          (d.totient : ℝ)⁻¹ *
            ∑ ψ : primitiveCharacters d,
              primitiveRawEndpointMaximum x d ψ := by
  calc
    _ ≤ (5 * Real.log (x : ℝ)) *
        ∑ d ∈ Finset.Ioc 0 Q with roughModulusAbove Q1 d,
          (d.totient : ℝ)⁻¹ *
            ∑ ψ : primitiveCharacters d,
              primitiveCenteredEndpointMaximum x d ψ :=
      sum_weightedInducingPrimitiveCenteredEndpointMaximum_le_five_log
        x Q Q1 hx hQsqrt
    _ = _ := by
      rw [sum_conductorRough_invTotient_primitiveCentered_eq_raw]

end

end BoundedGaps.Maynard
