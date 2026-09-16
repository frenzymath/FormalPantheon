import Waring.Analytic.WeilMonicFactors
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Minpoly.ConjRootClass

/-!
# Closed points of a finite-field extension

For the chosen degree-`n` extension of a finite field `K`, conjugacy classes
of elements are equivalent to monic irreducible polynomials over `K` whose
degrees divide `n`.  This gives the exact fiberwise reindexing used to pass
between extension-field sums and Euler sums over irreducible polynomials.
-/

namespace Waring.Analytic

open Polynomial
open scoped BigOperators

namespace Weil

/-- A monic irreducible polynomial whose degree divides `n`.  The redundant
degree bound makes this a subtype of the finite Euler indexing type. -/
def ExtensionClosedPoint (K : Type*) [Field K] (n : Nat) :=
  {P : MonicIrreducibleLE K n // P.poly.natDegree ∣ n}

namespace ExtensionClosedPoint

variable {K : Type*} [Field K] {n : Nat}

/-- The polynomial underlying a finite-extension closed point. -/
def poly (P : ExtensionClosedPoint K n) : K[X] := P.1.poly

/-- A closed-point polynomial is monic. -/
theorem monic (P : ExtensionClosedPoint K n) : P.poly.Monic := P.1.monic

/-- A closed-point polynomial is irreducible. -/
theorem irreducible (P : ExtensionClosedPoint K n) : Irreducible P.poly :=
  P.1.irreducible

/-- The degree of a closed point divides the extension degree. -/
theorem natDegree_dvd (P : ExtensionClosedPoint K n) : P.poly.natDegree ∣ n :=
  P.2

end ExtensionClosedPoint

variable (K : Type*) [Field K] [Fintype K]
variable (p n : Nat) [Fact p.Prime] [CharP K p] [NeZero n]

/-- The chosen finite-field extension has a finite enumeration. This instance
remains unnamed to preserve its baseline-recorded generated name. -/
@[nolint defsWithUnderscore]
noncomputable local instance : Fintype (FiniteField.Extension K p n) :=
  Fintype.ofFinite _

private noncomputable def conjugacyClassClosedPoint
    (c : ConjRootClass K (FiniteField.Extension K p n)) :
    ExtensionClosedPoint K n := by
  let P : K[X] := c.minpoly
  have hdiv : P.natDegree ∣ n := by
    rw [← FiniteField.finrank_extension K p n]
    exact c.irreducible_minpoly.natDegree_dvd_finrank c.splits_minpoly
  exact
    ⟨{ poly := P
       irreducible := c.irreducible_minpoly
       monic := c.monic_minpoly
       natDegree_le := Nat.le_of_dvd (NeZero.pos n) hdiv }, hdiv⟩

private theorem conjugacyClassClosedPoint_injective :
    Function.Injective (conjugacyClassClosedPoint K p n) := by
  intro c d h
  apply ConjRootClass.minpoly_injective
  exact congrArg (fun P : ExtensionClosedPoint K n ↦ P.poly) h

private theorem exists_minpoly_eq_closedPoint
    (P : ExtensionClosedPoint K n) :
    ∃ x : FiniteField.Extension K p n, minpoly K x = P.poly := by
  letI : Fact (Irreducible P.poly) := ⟨P.irreducible⟩
  have hfinrank : Module.finrank K (AdjoinRoot P.poly) = P.poly.natDegree := by
    rw [(AdjoinRoot.powerBasis P.irreducible.ne_zero).finrank,
      AdjoinRoot.powerBasis_dim]
  have hdvd : Module.finrank K (AdjoinRoot P.poly) ∣
      Module.finrank K (FiniteField.Extension K p n) := by
    rw [hfinrank, FiniteField.finrank_extension K p n]
    exact P.natDegree_dvd
  let f : AdjoinRoot P.poly →ₐ[K] FiniteField.Extension K p n :=
    (FiniteField.nonempty_algHom_of_finrank_dvd hdvd).some
  let x : FiniteField.Extension K p n := f (AdjoinRoot.root P.poly)
  refine ⟨x, ?_⟩
  have hroot : aeval (AdjoinRoot.root P.poly) P.poly = 0 := by
    rw [Polynomial.aeval_def]
    exact AdjoinRoot.eval₂_root P.poly
  have hminpoly : minpoly K (AdjoinRoot.root P.poly) = P.poly := by
    have h := minpoly.eq_of_irreducible P.irreducible hroot
    simpa [P.monic.leadingCoeff] using h.symm
  calc
    minpoly K x = minpoly K (AdjoinRoot.root P.poly) :=
      minpoly.algHom_eq f f.injective _
    _ = P.poly := hminpoly

private theorem conjugacyClassClosedPoint_surjective :
    Function.Surjective (conjugacyClassClosedPoint K p n) := by
  intro P
  obtain ⟨x, hx⟩ := exists_minpoly_eq_closedPoint K p n P
  refine ⟨ConjRootClass.mk K x, ?_⟩
  apply Subtype.ext
  apply MonicIrreducibleLE.poly_injective
  exact hx

/-- Conjugacy classes in the degree-`n` extension correspond exactly to
monic irreducibles whose degrees divide `n`. -/
noncomputable def conjugacyClassEquivClosedPoint :
    ConjRootClass K (FiniteField.Extension K p n) ≃ ExtensionClosedPoint K n :=
  Equiv.ofBijective (conjugacyClassClosedPoint K p n)
    ⟨conjugacyClassClosedPoint_injective K p n,
      conjugacyClassClosedPoint_surjective K p n⟩

/-- Closed points inherit a finite enumeration from their bounded polynomial
representation. -/
noncomputable local instance : Fintype (ExtensionClosedPoint K n) := by
  unfold ExtensionClosedPoint
  infer_instance

/-- Conjugacy classes inherit a finite enumeration from closed points; the
generated compatibility name is retained to preserve its baseline-recorded name. -/
@[nolint defsWithUnderscore]
noncomputable local instance :
    Fintype (ConjRootClass K (FiniteField.Extension K p n)) :=
  Fintype.ofEquiv (ExtensionClosedPoint K n)
    (conjugacyClassEquivClosedPoint K p n).symm

/-- Each conjugacy-class carrier is finite. This instance remains unnamed to
preserve its baseline-recorded generated name. -/
@[nolint defsWithUnderscore]
noncomputable local instance
    (c : ConjRootClass K (FiniteField.Extension K p n)) : Fintype c.carrier :=
  Fintype.ofFinite _

/-- A conjugacy class has as many elements as the degree of its minimal
polynomial. -/
theorem card_conjugacyClass_carrier
    (c : ConjRootClass K (FiniteField.Extension K p n)) :
    Fintype.card c.carrier = c.minpoly.natDegree := by
  calc
    Fintype.card c.carrier = Fintype.card (c.minpoly.rootSet
        (FiniteField.Extension K p n)) :=
      Fintype.card_congr
        (Equiv.setCongr c.rootSet_minpoly_eq_carrier).symm
    _ = c.minpoly.natDegree :=
      Polynomial.card_rootSet_eq_natDegree c.separable_minpoly c.splits_minpoly

/-- Reindex a sum over the extension field by conjugacy classes and their
minimal polynomials. -/
theorem sum_extension_eq_sum_conjugacyClasses
    {A : Type*} [AddCommMonoid A] (f : K[X] → A) :
    (∑ x : FiniteField.Extension K p n, f (minpoly K x)) =
      ∑ c : ConjRootClass K (FiniteField.Extension K p n),
        c.minpoly.natDegree • f c.minpoly := by
  classical
  rw [← Fintype.sum_fiberwise (ConjRootClass.mk K)
    (fun x : FiniteField.Extension K p n ↦ f (minpoly K x))]
  apply Finset.sum_congr rfl
  intro c hc
  calc
    (∑ x : {x : FiniteField.Extension K p n // ConjRootClass.mk K x = c},
        f (minpoly K x.1)) =
        ∑ _x : {x : FiniteField.Extension K p n //
          ConjRootClass.mk K x = c}, f c.minpoly := by
      apply Fintype.sum_congr
      intro x
      rw [← ConjRootClass.minpoly_mk (K := K) x.1, x.2]
    _ = Fintype.card {x : FiniteField.Extension K p n //
          ConjRootClass.mk K x = c} • f c.minpoly := by
      simp
    _ = Fintype.card c.carrier • f c.minpoly := by
      congr 1
      apply Fintype.card_congr
      exact
        { toFun := fun x ↦ ⟨x.1, x.2⟩
          invFun := fun x ↦ ⟨x.1, x.2⟩
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl }
    _ = c.minpoly.natDegree • f c.minpoly := by
      rw [card_conjugacyClass_carrier K p n c]

/-- Exact closed-point reindexing: an extension-field sum depending only on
the minimal polynomial is the corresponding degree-weighted Euler sum. -/
theorem sum_extension_eq_irreducibleSum
    {A : Type*} [AddCommMonoid A] (f : K[X] → A) :
    (∑ x : FiniteField.Extension K p n, f (minpoly K x)) =
      ∑ P : MonicIrreducibleLE K n,
        if P.poly.natDegree ∣ n then P.poly.natDegree • f P.poly else 0 := by
  classical
  rw [sum_extension_eq_sum_conjugacyClasses K p n]
  calc
    (∑ c : ConjRootClass K (FiniteField.Extension K p n),
        c.minpoly.natDegree • f c.minpoly) =
        ∑ P : ExtensionClosedPoint K n, P.poly.natDegree • f P.poly := by
      exact (conjugacyClassEquivClosedPoint K p n).sum_comp
        (fun P ↦ P.poly.natDegree • f P.poly)
    _ = ∑ P ∈ (Finset.univ : Finset (MonicIrreducibleLE K n)).filter
          (fun P ↦ P.poly.natDegree ∣ n), P.poly.natDegree • f P.poly := by
      symm
      apply Finset.sum_subtype
      intro P
      simp
    _ = ∑ P : MonicIrreducibleLE K n,
          if P.poly.natDegree ∣ n then P.poly.natDegree • f P.poly else 0 := by
      exact Finset.sum_filter _ _

/-- Specialization of the closed-point reindexing to the powered formal-root
weight appearing in the logarithmic derivative of the Euler product. -/
theorem sum_extension_minpolyWeight_eq_irreducibleSum
    (character : AddChar K Complex) (b : Fin 5 → K) :
    (∑ x : FiniteField.Extension K p n,
      formalRootWeight character b (minpoly K x) ^
        (n / (minpoly K x).natDegree)) =
      ∑ P : MonicIrreducibleLE K n,
        if P.poly.natDegree ∣ n then
          (P.poly.natDegree : Complex) *
            formalRootWeight character b P.poly ^ (n / P.poly.natDegree)
        else 0 := by
  simpa only [nsmul_eq_mul] using
    (sum_extension_eq_irreducibleSum K p n
      (fun P ↦ formalRootWeight character b P ^ (n / P.natDegree)))

end Weil

end Waring.Analytic
