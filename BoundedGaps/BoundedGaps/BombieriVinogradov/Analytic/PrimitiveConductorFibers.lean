import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-!
# Primitive-character conductor fibers

This file formalizes the finite conductor classification used after the
centered `psi'` estimate in Akbary--Hambrook2013v2, Section 7, p. 25. A
positive-level character is partitioned by its conductor, and each conductor
fiber is equivalent to the primitive characters at that conductor. The later
`1 / phi (k * d)` weighting, least-prime cutoff, and analytic mean value are
deliberately outside this finite module.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable section

abbrev primitiveCharacters (d : ℕ) :=
  {ψ : DirichletCharacter ℂ d // ψ.IsPrimitive}

abbrev charactersOfConductor (q d : ℕ) :=
  {χ : DirichletCharacter ℂ q // χ.conductor = d}

noncomputable instance primitiveCharactersFintype (d : ℕ) :
    Fintype (primitiveCharacters d) := Fintype.ofFinite _

noncomputable instance charactersOfConductorFintype (q d : ℕ) :
    Fintype (charactersOfConductor q d) := Fintype.ofFinite _

/-- At a positive level, the number of primitive complex characters is at
most the total number `phi(q)` of characters. -/
theorem card_primitiveCharacters_le_totient
    {q : ℕ} (hq : 0 < q) :
    Fintype.card (primitiveCharacters q) ≤ q.totient := by
  letI : NeZero q := ⟨hq.ne'⟩
  calc
    Fintype.card (primitiveCharacters q) ≤
        Fintype.card (DirichletCharacter ℂ q) :=
      Fintype.card_subtype_le _
    _ = Nat.card (DirichletCharacter ℂ q) :=
      Nat.card_eq_fintype_card.symm
    _ = q.totient :=
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q

noncomputable def primitiveCharactersEquivConductorFiber
    {q d : ℕ} (hq : 0 < q) (hd : d ∣ q) :
    primitiveCharacters d ≃ charactersOfConductor q d := by
  letI : NeZero q := ⟨by omega⟩
  let f : primitiveCharacters d → charactersOfConductor q d := fun ψ ↦
    ⟨DirichletCharacter.changeLevel hd ψ.1, by
      rw [DirichletCharacter.conductor_changeLevel ψ.1 hd]
      exact (DirichletCharacter.isPrimitive_def ψ.1).mp ψ.2⟩
  have hf_injective : Function.Injective f := by
    intro ψ ψ' h
    apply Subtype.ext
    apply DirichletCharacter.changeLevel_injective hd
    exact congrArg Subtype.val h
  have hf_surjective : Function.Surjective f := by
    intro χ
    rcases χ with ⟨χ, hχ⟩
    subst d
    refine ⟨⟨χ.primitiveCharacter, χ.primitiveCharacter_isPrimitive⟩, ?_⟩
    apply Subtype.ext
    exact χ.changeLevel_primitiveCharacter
  exact Equiv.ofBijective f ⟨hf_injective, hf_surjective⟩

theorem sum_characters_of_conductor_eq_sum_primitive
    {q d : ℕ} (hq : 0 < q) (hd : d ∣ q)
    {M : Type*} [AddCommMonoid M]
    (F : DirichletCharacter ℂ q → M) :
    (∑ χ : charactersOfConductor q d, F χ.1) =
      ∑ ψ : primitiveCharacters d,
        F (DirichletCharacter.changeLevel hd ψ.1) := by
  letI : NeZero q := ⟨by omega⟩
  apply Fintype.sum_equiv (primitiveCharactersEquivConductorFiber hq hd).symm
      (fun χ : charactersOfConductor q d ↦ F χ.1)
      (fun ψ : primitiveCharacters d ↦
        F (DirichletCharacter.changeLevel hd ψ.1))
  intro χ
  have hχ := (primitiveCharactersEquivConductorFiber hq hd).apply_symm_apply χ
  exact (congrArg (fun z : charactersOfConductor q d ↦ F z.1) hχ).symm

noncomputable def conductorDivisor {q : ℕ} (hq : 0 < q)
    (χ : DirichletCharacter ℂ q) : q.divisors :=
  ⟨χ.conductor, Nat.mem_divisors.mpr ⟨χ.conductor_dvd_level, by omega⟩⟩

noncomputable def conductorFiberEquiv {q : ℕ} (hq : 0 < q)
    (d : q.divisors) :
    {χ : DirichletCharacter ℂ q // conductorDivisor hq χ = d} ≃
      charactersOfConductor q d.1 where
  toFun χ := ⟨χ.1, congrArg Subtype.val χ.2⟩
  invFun χ := ⟨χ.1, Subtype.ext χ.2⟩
  left_inv χ := by
    apply Subtype.ext
    rfl
  right_inv χ := by
    apply Subtype.ext
    rfl

theorem sum_characters_eq_sum_conductor_fibers
    {q : ℕ} (hq : 0 < q)
    {M : Type*} [AddCommMonoid M]
    (F : DirichletCharacter ℂ q → M) :
    (∑ χ : DirichletCharacter ℂ q, F χ) =
      ∑ d : q.divisors,
        ∑ χ : charactersOfConductor q d.1, F χ.1 := by
  let g := conductorDivisor hq
  have hfiber := Fintype.sum_fiberwise g F
  rw [← hfiber]
  apply Fintype.sum_congr
  intro d
  exact Fintype.sum_equiv (conductorFiberEquiv hq d)
    (fun χ : {χ : DirichletCharacter ℂ q // g χ = d} ↦ F χ.1)
    (fun χ : charactersOfConductor q d.1 ↦ F χ.1)
    (fun χ ↦ rfl)

theorem sum_characters_eq_sum_divisor_primitive
    {q : ℕ} (hq : 0 < q)
    {M : Type*} [AddCommMonoid M]
    (F : DirichletCharacter ℂ q → M) :
    (∑ χ : DirichletCharacter ℂ q, F χ) =
      ∑ d : q.divisors,
        ∑ ψ : primitiveCharacters d.1,
          F (DirichletCharacter.changeLevel
            (Nat.dvd_of_mem_divisors d.2) ψ.1) := by
  rw [sum_characters_eq_sum_conductor_fibers hq F]
  apply Fintype.sum_congr
  intro d
  exact sum_characters_of_conductor_eq_sum_primitive hq
    (Nat.dvd_of_mem_divisors d.2) F

theorem card_conductor_fiber_eq_card_primitive
    {q d : ℕ} (hq : 0 < q) (hd : d ∣ q) :
    Fintype.card (charactersOfConductor q d) =
      Fintype.card (primitiveCharacters d) := by
  exact Fintype.card_congr (primitiveCharactersEquivConductorFiber hq hd).symm

theorem card_characters_eq_sum_primitive_cards
    {q : ℕ} (hq : 0 < q) :
    Fintype.card (DirichletCharacter ℂ q) =
      ∑ d : q.divisors, Fintype.card (primitiveCharacters d.1) := by
  have h := sum_characters_eq_sum_divisor_primitive
    (M := ℕ) hq (fun _ ↦ 1)
  simpa using h

theorem totient_eq_sum_primitive_cards
    {q : ℕ} (hq : 0 < q) :
    q.totient =
      ∑ d : q.divisors, Fintype.card (primitiveCharacters d.1) := by
  letI : NeZero q := ⟨by omega⟩
  calc
    q.totient = Nat.card (DirichletCharacter ℂ q) :=
      (DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q).symm
    _ = Fintype.card (DirichletCharacter ℂ q) := Nat.card_eq_fintype_card
    _ = ∑ d : q.divisors, Fintype.card (primitiveCharacters d.1) :=
      card_characters_eq_sum_primitive_cards hq

end

end BoundedGaps.Maynard
