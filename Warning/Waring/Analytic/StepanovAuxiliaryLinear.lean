import Waring.Analytic.StepanovReducedPolynomials
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.RingTheory.Polynomial.DegreeLT

/-!
# The linear kernel for the Stepanov auxiliary polynomial

The free coefficients are indexed by `p * (K + 1) * S` coordinates.  The
reduced Hasse conditions have only `R * D` possible coefficients.  The strict
dimension inequality therefore supplies a nonzero family satisfying every
condition.
-/

namespace Waring.Analytic

open Polynomial
open scoped BigOperators

namespace Stepanov

/-- Scalar coefficients of the auxiliary coefficient polynomials. -/
abbrev AuxiliaryCoefficients (E : Type*) (p h : Nat) :=
  Fin p -> Fin (K p h + 1) -> Fin (S p h) -> E

/-- Scalar coefficients of all reduced derivative conditions. -/
abbrev AuxiliaryConditions (E : Type*) (p h d : Nat) :=
  Fin (R p h) -> Fin (D p h d) -> E

/-- The coefficient polynomial encoded by one slice of an auxiliary
coefficient family. -/
noncomputable def auxiliaryCoefficientPolynomial
    {E : Type*} [Field E] {p h : Nat}
    (a : AuxiliaryCoefficients E p h) (i : Fin p)
    (k : Fin (K p h + 1)) : E[X] :=
  ((degreeLTEquiv E (S p h)).symm (a i k)).1

/-- An encoded coefficient polynomial has degree below `S`. -/
theorem natDegree_auxiliaryCoefficientPolynomial_lt
    {E : Type*} [Field E] {p h : Nat}
    (hp : 0 < p)
    (a : AuxiliaryCoefficients E p h) (i : Fin p)
    (k : Fin (K p h + 1)) :
    (auxiliaryCoefficientPolynomial a i k).natDegree < S p h := by
  let q := (degreeLTEquiv E (S p h)).symm (a i k)
  by_cases hq : (q.1 : E[X]) = 0
  · change q.1.natDegree < S p h
    rw [hq, natDegree_zero]
    exact Nat.pow_pos hp
  have hmem := q.2
  rw [mem_degreeLT, degree_eq_natDegree hq, Nat.cast_lt] at hmem
  exact hmem

private theorem auxiliaryCoefficientPolynomial_add
    {E : Type*} [Field E] {p h : Nat}
    (a b : AuxiliaryCoefficients E p h) (i : Fin p)
    (k : Fin (K p h + 1)) :
    auxiliaryCoefficientPolynomial (a + b) i k =
      auxiliaryCoefficientPolynomial a i k +
        auxiliaryCoefficientPolynomial b i k := by
  simp [auxiliaryCoefficientPolynomial]

private theorem auxiliaryCoefficientPolynomial_smul
    {E : Type*} [Field E] {p h : Nat} (z : E)
    (a : AuxiliaryCoefficients E p h) (i : Fin p)
    (k : Fin (K p h + 1)) :
    auxiliaryCoefficientPolynomial (z • a) i k =
      z • auxiliaryCoefficientPolynomial a i k := by
  simp [auxiliaryCoefficientPolynomial]

/-- The sum of all reduced terms for one derivative order. -/
noncomputable def reducedAuxiliaryConditionPolynomial
    {E : Type*} [Field E] (p h : Nat) (c : E) (r : Nat)
    (f : E[X]) (a : AuxiliaryCoefficients E p h) : E[X] :=
  ∑ i : Fin p, ∑ k : Fin (K p h + 1),
    reducedAuxiliaryTerm p h c r i k
      (auxiliaryCoefficientPolynomial a i k) f

private theorem reducedAuxiliaryConditionPolynomial_add
    {E : Type*} [Field E] (p h : Nat) (c : E) (r : Nat)
    (f : E[X]) (a b : AuxiliaryCoefficients E p h) :
    reducedAuxiliaryConditionPolynomial p h c r f (a + b) =
      reducedAuxiliaryConditionPolynomial p h c r f a +
        reducedAuxiliaryConditionPolynomial p h c r f b := by
  simp only [reducedAuxiliaryConditionPolynomial,
    auxiliaryCoefficientPolynomial_add, reducedAuxiliaryTerm, map_add,
    add_mul, Finset.sum_add_distrib]

private theorem reducedAuxiliaryConditionPolynomial_smul
    {E : Type*} [Field E] (p h : Nat) (c : E) (r : Nat)
    (f : E[X]) (z : E) (a : AuxiliaryCoefficients E p h) :
    reducedAuxiliaryConditionPolynomial p h c r f (z • a) =
      z • reducedAuxiliaryConditionPolynomial p h c r f a := by
  simp only [reducedAuxiliaryConditionPolynomial,
    auxiliaryCoefficientPolynomial_smul, reducedAuxiliaryTerm,
    LinearMap.map_smul_of_tower, smul_mul_assoc, Finset.smul_sum]

/-- The linear map whose kernel consists of coefficient families satisfying
all reduced derivative conditions. -/
noncomputable def reducedAuxiliaryConditionLinear
    {E : Type*} [Field E] (p h d : Nat) (c : E) (f : E[X]) :
    AuxiliaryCoefficients E p h →ₗ[E] AuxiliaryConditions E p h d where
  toFun a r j :=
    (reducedAuxiliaryConditionPolynomial p h c r f a).coeff j
  map_add' a b := by
    funext r j
    rw [reducedAuxiliaryConditionPolynomial_add, coeff_add]
    rfl
  map_smul' z a := by
    funext r j
    rw [reducedAuxiliaryConditionPolynomial_smul, coeff_smul]
    rfl

private theorem finrank_auxiliaryCoefficients
    {E : Type*} [Field E] (p h : Nat) :
    Module.finrank E (AuxiliaryCoefficients E p h) =
      p * S p h * (K p h + 1) := by
  simp [AuxiliaryCoefficients, Module.finrank_pi_fintype]
  ring

private theorem finrank_auxiliaryConditions
    {E : Type*} [Field E] (p h d : Nat) :
    Module.finrank E (AuxiliaryConditions E p h d) =
      R p h * D p h d := by
  simp [AuxiliaryConditions, Module.finrank_pi_fintype]

/-- The strict parameter count gives a nonzero coefficient family satisfying
every reduced derivative condition. -/
theorem exists_nonzero_auxiliaryCoefficients
    {E : Type*} [Field E] {p h d : Nat} (hp : 1 < p) (hd : d < p)
    (c : E) (f : E[X]) :
    ∃ a : AuxiliaryCoefficients E p h,
      a ≠ 0 ∧ reducedAuxiliaryConditionLinear p h d c f a = 0 := by
  let T := reducedAuxiliaryConditionLinear p h d c f
  have hker : LinearMap.ker T ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective T := LinearMap.ker_eq_bot.mp hbot
    have hle := T.finrank_le_finrank_of_injective hinj
    rw [finrank_auxiliaryCoefficients p h,
      finrank_auxiliaryConditions p h d] at hle
    exact (not_le_of_gt (constraints_lt_coefficients (h := h) hp hd)) hle
  obtain ⟨a, ha, hane⟩ := (LinearMap.ker T).ne_bot_iff.mp hker
  exact ⟨a, hane, ha⟩

end Stepanov

end Waring.Analytic
