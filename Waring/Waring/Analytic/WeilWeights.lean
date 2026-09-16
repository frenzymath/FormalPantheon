import Waring.Analytic.WeilPowerSums
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Multiplicative polynomial weights for the degree-five Weil estimate

This file packages the first five formal root power sums into the additive
phase and multiplicative character weight used by the Artin `L`-function.
-/

namespace Waring.Analytic

open Polynomial
open scoped BigOperators

namespace Weil

variable {R : Type*} [CommRing R]

/-- A polynomial phase with coefficients indexed by the exponents `1,...,5`. -/
def pointPhase (b : Fin 5 → R) (x : R) : R :=
  ∑ i : Fin 5, b i * x ^ (i.val + 1)

/-- The sum of `pointPhase b` over the formal roots of a monic polynomial,
expressed entirely through its coefficients. -/
noncomputable def formalRootPhase (b : Fin 5 → R) (F : R[X]) : R :=
  ∑ i : Fin 5, b i * formalRootPowerSum (i.val + 1) F

/-- Pointwise phases commute with a ring map. -/
theorem pointPhase_map {S : Type*} [CommRing S] (f : R →+* S)
    (b : Fin 5 → R) (x : R) :
    f (pointPhase b x) = pointPhase (f ∘ b) (f x) := by
  simp [pointPhase, map_sum]

/-- Formal root phases of monic polynomials commute with a ring map. -/
theorem formalRootPhase_map {S : Type*} [CommRing S] [Nontrivial S]
    (f : R →+* S)
    (b : Fin 5 → R) {F : R[X]} (hF : F.Monic) :
    formalRootPhase (f ∘ b) (F.map f) = f (formalRootPhase b F) := by
  simp [formalRootPhase, formalRootPowerSum_map f hF, map_sum]

/-- Formal root phases are additive under products of monic polynomials. -/
theorem formalRootPhase_mul_of_monic [IsDomain R] (b : Fin 5 → R) {F G : R[X]}
    (hF : F.Monic) (hG : G.Monic) :
    formalRootPhase b (F * G) = formalRootPhase b F + formalRootPhase b G := by
  simp only [formalRootPhase]
  calc
    ∑ i : Fin 5, b i * formalRootPowerSum (i.val + 1) (F * G) =
        ∑ i : Fin 5, b i *
          (formalRootPowerSum (i.val + 1) F +
            formalRootPowerSum (i.val + 1) G) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [formalRootPowerSum_mul_of_monic hF hG (Nat.succ_pos i.val)
        (Nat.succ_le_iff.mpr i.isLt)]
    _ = (∑ i : Fin 5, b i * formalRootPowerSum (i.val + 1) F) +
        ∑ i : Fin 5, b i * formalRootPowerSum (i.val + 1) G := by
      simp_rw [mul_add, Finset.sum_add_distrib]

/-- For a split monic polynomial, the coefficient phase is the sum of the
pointwise phase over its roots, counted with multiplicity. -/
theorem formalRootPhase_eq_sum_roots [IsDomain R] (b : Fin 5 → R) {F : R[X]}
    (hF : F.Monic) (hSplit : F.Splits) :
    formalRootPhase b F = (F.roots.map (pointPhase b)).sum := by
  have rearrange (s : Multiset R) :
      (∑ i : Fin 5, b i * (s.map (fun a ↦ a ^ (i.val + 1))).sum) =
        (s.map (pointPhase b)).sum := by
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
        simp only [Multiset.map_cons, Multiset.sum_cons, mul_add,
          Finset.sum_add_distrib, pointPhase, ih]
  rw [formalRootPhase]
  calc
    ∑ i : Fin 5, b i * formalRootPowerSum (i.val + 1) F =
        ∑ i : Fin 5, b i *
          (F.roots.map (fun a ↦ a ^ (i.val + 1))).sum := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [formalRootPowerSum_eq_sum_roots hF hSplit (Nat.succ_pos i.val)
        (Nat.succ_le_iff.mpr i.isLt)]
    _ = (F.roots.map (pointPhase b)).sum := rearrange F.roots

/-- Interpret a formal root phase after mapping a monic polynomial to a
splitting ring. -/
theorem formalRootPhase_eq_sum_roots_map {S : Type*} [CommRing S] [IsDomain S]
    (f : R →+* S) (b : Fin 5 → R) {F : R[X]} (hF : F.Monic)
    (hSplit : (F.map f).Splits) :
    f (formalRootPhase b F) =
      ((F.map f).roots.map (pointPhase (f ∘ b))).sum := by
  rw [← formalRootPhase_map f b hF,
    formalRootPhase_eq_sum_roots (f ∘ b) (hF.map f) hSplit]

/-- The additive-character weight attached to the formal root phase. -/
noncomputable def formalRootWeight (character : AddChar R Complex)
    (b : Fin 5 → R) (F : R[X]) : Complex :=
  character (formalRootPhase b F)

/-- The formal root weight is multiplicative on monic polynomials. -/
theorem formalRootWeight_mul_of_monic (character : AddChar R Complex)
    [IsDomain R] (b : Fin 5 → R) {F G : R[X]} (hF : F.Monic) (hG : G.Monic) :
    formalRootWeight character b (F * G) =
      formalRootWeight character b F * formalRootWeight character b G := by
  change character (formalRootPhase b (F * G)) =
    character (formalRootPhase b F) * character (formalRootPhase b G)
  rw [formalRootPhase_mul_of_monic b hF hG,
    character.map_add_eq_mul]

end Weil

end Waring.Analytic
