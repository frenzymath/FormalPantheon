import BoundedGaps.BombieriVinogradov.Analytic.CenteredCharacterReduction
import BoundedGaps.BombieriVinogradov.Analytic.PrimitiveConductorFibers

/-!
# Centered primitive-character endpoint maxima

This file lifts the centered character estimate on Akbary--Hambrook2013v2,
Section 7, pp. 24--25, to the natural endpoint maximum and then partitions the
inducing primitive characters by conductor. The outer modulus reindex and
reciprocal-totient estimate are deliberately separate.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators ArithmeticFunction.vonMangoldt

noncomputable section

/-- Maximum centered twist of one primitive character over `2 <= y <= x`. -/
noncomputable def primitiveCenteredEndpointMaximum
    (x d : ℕ) (ψ : primitiveCharacters d) : ℝ :=
  if hx : 2 ≤ x then
    (Finset.Icc 2 x).sup' (weightedEndpointRange_nonempty hx)
      (fun y ↦ ‖centeredTwistedChebyshevSum y d ψ.1‖)
  else 0

/-- Endpoint maximum of the canonical primitive character inducing `χ`. -/
noncomputable def inducingPrimitiveCenteredEndpointMaximum
    (x q : ℕ) (χ : DirichletCharacter ℂ q) : ℝ :=
  primitiveCenteredEndpointMaximum x χ.conductor
    ⟨χ.primitiveCharacter, χ.primitiveCharacter_isPrimitive⟩

/-- The pointwise centered progression estimate, maximized over endpoints. -/
theorem centeredProgressionEndpointMaximum_le_log_sq_add_primitive
    {x q a : ℕ} (hx : 2 ≤ x) (hq : 1 ≤ q)
    (ha : Nat.Coprime a q) :
    (Finset.Icc 2 x).sup' (weightedEndpointRange_nonempty hx) (fun y ↦
      |chebyshevProgressionSum y q a -
        Chebyshev.psi (y : ℝ) / (q.totient : ℝ)|) ≤
      (Real.log ((q * x : ℕ) : ℝ)) ^ 2 +
        (q.totient : ℝ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q,
            inducingPrimitiveCenteredEndpointMaximum x q χ := by
  have hq0 : q ≠ 0 := by omega
  letI : NeZero q := ⟨hq0⟩
  apply Finset.sup'_le (weightedEndpointRange_nonempty hx)
  intro y hy
  have hyBounds : 2 ≤ y ∧ y ≤ x := Finset.mem_Icc.mp hy
  have hqyPos : 0 < q * y := Nat.mul_pos (by omega) (by omega)
  have hqyOne : 1 ≤ q * y := Nat.one_le_iff_ne_zero.mpr hqyPos.ne'
  have hlogNonneg : 0 ≤ Real.log ((q * y : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast hqyOne
  have hlogLe :
      Real.log ((q * y : ℕ) : ℝ) ≤
        Real.log ((q * x : ℕ) : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast hqyPos
    · exact_mod_cast Nat.mul_le_mul_left q hyBounds.2
  have hlogSq :
      (Real.log ((q * y : ℕ) : ℝ)) ^ 2 ≤
        (Real.log ((q * x : ℕ) : ℝ)) ^ 2 :=
    (sq_le_sq₀ hlogNonneg (hlogNonneg.trans hlogLe)).2 hlogLe
  have hprimitive (χ : DirichletCharacter ℂ q) :
      ‖centeredTwistedChebyshevSum
          y χ.conductor χ.primitiveCharacter‖ ≤
        inducingPrimitiveCenteredEndpointMaximum x q χ := by
    unfold inducingPrimitiveCenteredEndpointMaximum
      primitiveCenteredEndpointMaximum
    rw [dif_pos hx]
    simpa using (Finset.le_sup'
      (fun z ↦ ‖centeredTwistedChebyshevSum
        z χ.conductor χ.primitiveCharacter‖) hy)
  have hsum :
      (q.totient : ℝ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q,
            ‖centeredTwistedChebyshevSum
              y χ.conductor χ.primitiveCharacter‖ ≤
        (q.totient : ℝ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q,
            inducingPrimitiveCenteredEndpointMaximum x q χ := by
    apply mul_le_mul_of_nonneg_left
    · apply Finset.sum_le_sum
      intro χ hχ
      exact hprimitive χ
    · positivity
  exact
    (abs_chebyshevProgressionSum_sub_global_le_log_sq_add_primitive_average
      hyBounds.1 hq ha).trans (add_le_add hlogSq hsum)

/-- The endpoint estimate with the reduced-residue maximum in source order. -/
theorem centeredProgressionResidueEndpointMaximum_le_log_sq_add_primitive
    {x q : ℕ} (hx : 2 ≤ x) (hq : 1 ≤ q) :
    (Finset.Icc 2 x).sup' (weightedEndpointRange_nonempty hx) (fun y ↦
      (coprimeResidues q).sup'
          (coprimeResidues_nonempty (by omega)) (fun a ↦
        |chebyshevProgressionSum y q a -
          Chebyshev.psi (y : ℝ) / (q.totient : ℝ)|)) ≤
      (Real.log ((q * x : ℕ) : ℝ)) ^ 2 +
        (q.totient : ℝ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q,
            inducingPrimitiveCenteredEndpointMaximum x q χ := by
  apply Finset.sup'_le (weightedEndpointRange_nonempty hx)
  intro y hy
  apply Finset.sup'_le (coprimeResidues_nonempty (by omega))
  intro a ha
  have haCoprime : Nat.Coprime a q := by
    unfold coprimeResidues at ha
    exact (Finset.mem_filter.mp ha).2
  exact (Finset.le_sup'
      (fun z ↦ |chebyshevProgressionSum z q a -
        Chebyshev.psi (z : ℝ) / (q.totient : ℝ)|) hy).trans
    (centeredProgressionEndpointMaximum_le_log_sq_add_primitive
      hx hq haCoprime)

/-- The centered endpoint maximum vanishes at primitive level one. -/
theorem primitiveCenteredEndpointMaximum_one
    (x : ℕ) (ψ : primitiveCharacters 1) :
    primitiveCenteredEndpointMaximum x 1 ψ = 0 := by
  classical
  unfold primitiveCenteredEndpointMaximum
  split_ifs with hx
  · rw [Finset.sup'_eq_of_forall]
    intro y hy
    rw [show (ψ.1 : DirichletCharacter ℂ 1) = 1 by
      exact DirichletCharacter.level_one ψ.1]
    simp [centeredTwistedChebyshevSum_one]
  · rfl

/-- The full primitive-character sum at level one vanishes. -/
theorem sum_primitiveCenteredEndpointMaximum_one (x : ℕ) :
    (∑ ψ : primitiveCharacters 1,
      primitiveCenteredEndpointMaximum x 1 ψ) = 0 := by
  apply Fintype.sum_eq_zero
  intro ψ
  exact primitiveCenteredEndpointMaximum_one x ψ

/-- A primitive character agrees pointwise with its canonical primitive
representative. The pointwise form avoids an ill-typed equality of character
types whose levels are only propositionally equal. -/
theorem primitiveCharacter_apply_eq_of_isPrimitive
    {d : ℕ} (ψ : primitiveCharacters d) (a : ℤ) :
    ψ.1.primitiveCharacter a = ψ.1 a := by
  by_cases hcop : IsCoprime a d
  · simpa using ψ.1.primitiveCharacter_apply_of_isCoprime hcop
  · have hcon : ψ.1.conductor = d :=
      (DirichletCharacter.isPrimitive_def ψ.1).mp ψ.2
    have hcop' : ¬IsCoprime a ψ.1.conductor := by
      simpa [hcon] using hcop
    have hzero1 : ψ.1.primitiveCharacter a = 0 :=
      (DirichletCharacter.apply_eq_zero_iff _ _).2 hcop'
    have hzero2 : ψ.1 a = 0 :=
      (DirichletCharacter.apply_eq_zero_iff _ _).2 hcop
    rw [hzero1, hzero2]

/-- The inducing primitive centered twist of a lifted primitive character is
the original primitive centered twist. -/
theorem centeredTwistedChebyshevSum_changeLevel_primitive
    {y q d : ℕ} (hq : 0 < q) (hd : d ∣ q)
    (ψ : primitiveCharacters d) :
    centeredTwistedChebyshevSum y
        (DirichletCharacter.changeLevel hd ψ.1).conductor
        (DirichletCharacter.changeLevel hd ψ.1).primitiveCharacter =
      centeredTwistedChebyshevSum y d ψ.1 := by
  letI : NeZero q := ⟨by omega⟩
  have hcon :
      (DirichletCharacter.changeLevel hd ψ.1).conductor = d := by
    rw [DirichletCharacter.conductor_changeLevel]
    exact (DirichletCharacter.isPrimitive_def ψ.1).mp ψ.2
  have hval (n : ℕ) :
      (DirichletCharacter.changeLevel hd ψ.1).primitiveCharacter n =
        ψ.1 n := by
    have h₁ := DirichletCharacter.primitiveCharacter_changeLevel_apply hd ψ.1
      (n : ℤ)
    have h₂ := primitiveCharacter_apply_eq_of_isPrimitive ψ (n : ℤ)
    simpa using h₁.trans h₂
  have hprincipal :
      ((DirichletCharacter.changeLevel hd ψ.1).primitiveCharacter = 1) ↔
        (ψ.1 = 1) := by
    rw [primitiveCharacter_eq_one_iff]
    exact DirichletCharacter.changeLevel_eq_one_iff hd
  unfold centeredTwistedChebyshevSum
  congr 1
  · unfold twistedChebyshevSum
    apply Finset.sum_congr rfl
    intro n hn
    rw [hval]
  · by_cases h :
        (DirichletCharacter.changeLevel hd ψ.1).primitiveCharacter = 1
    · rw [if_pos h, if_pos (hprincipal.mp h)]
    · rw [if_neg h, if_neg (fun hp ↦ h (hprincipal.mpr hp))]

/-- Inducing endpoint maxima are unchanged by lifting a primitive character. -/
theorem inducingPrimitiveCenteredEndpointMaximum_changeLevel
    {x q d : ℕ} (hq : 0 < q) (hd : d ∣ q)
    (ψ : primitiveCharacters d) :
    inducingPrimitiveCenteredEndpointMaximum x q
        (DirichletCharacter.changeLevel hd ψ.1) =
      primitiveCenteredEndpointMaximum x d ψ := by
  classical
  unfold inducingPrimitiveCenteredEndpointMaximum
    primitiveCenteredEndpointMaximum
  split_ifs with hx
  · apply Finset.sup'_congr (weightedEndpointRange_nonempty hx) rfl
    intro y hy
    rw [centeredTwistedChebyshevSum_changeLevel_primitive hq hd ψ]
  · rfl

/-- Partition the inducing maxima over all characters by primitive conductor. -/
theorem sum_inducingPrimitiveCenteredEndpointMaximum_eq_divisors
    {x q : ℕ} (hq : 0 < q) :
    (∑ χ : DirichletCharacter ℂ q,
      inducingPrimitiveCenteredEndpointMaximum x q χ) =
      ∑ d : q.divisors,
        ∑ ψ : primitiveCharacters d.1,
          primitiveCenteredEndpointMaximum x d.1 ψ := by
  rw [sum_characters_eq_sum_divisor_primitive hq]
  apply Fintype.sum_congr
  intro d
  apply Fintype.sum_congr
  intro ψ
  exact inducingPrimitiveCenteredEndpointMaximum_changeLevel hq
    (Nat.dvd_of_mem_divisors d.2) ψ

/-- Remove precisely the zero primitive conductor-one term. -/
theorem sum_inducingPrimitiveCenteredEndpointMaximum_eq_divisors_ne_one
    {x q : ℕ} (hq : 0 < q) :
    (∑ χ : DirichletCharacter ℂ q,
      inducingPrimitiveCenteredEndpointMaximum x q χ) =
      ∑ d ∈ q.divisors with d ≠ 1,
        ∑ ψ : primitiveCharacters d,
          primitiveCenteredEndpointMaximum x d ψ := by
  rw [sum_inducingPrimitiveCenteredEndpointMaximum_eq_divisors hq]
  let G : ℕ → ℝ := fun d ↦
    ∑ ψ : primitiveCharacters d,
      primitiveCenteredEndpointMaximum x d ψ
  have hzero : ∀ d ∈ q.divisors, d = 1 → G d = 0 := by
    intro d hd h1
    subst d
    apply Fintype.sum_eq_zero
    intro ψ
    exact primitiveCenteredEndpointMaximum_one x ψ
  change (∑ d : q.divisors, G d.1) =
    ∑ d ∈ q.divisors with d ≠ 1, G d
  rw [← Finset.sum_subtype q.divisors (fun _ ↦ Iff.rfl) G]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases h : d ≠ 1
  · simp [h]
  · have h1 : d = 1 := by
      exact Classical.byContradiction (fun hn ↦ h hn)
    simp [h, hzero d hd h1]

end

end BoundedGaps.Maynard
