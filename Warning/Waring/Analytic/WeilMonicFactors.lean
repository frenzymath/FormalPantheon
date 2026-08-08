import Waring.Analytic.WeilPolynomiality
import Mathlib.Data.Finsupp.Weight
import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp

/-!
# Weighted factorization of monic polynomials

This file identifies monic polynomials of fixed degree with weighted
multiplicity functions on the finite set of bounded-degree monic irreducibles.
It is the finite combinatorial backbone of the Artin `L`-function Euler product.
-/

namespace Waring.Analytic

open Polynomial

namespace Weil

/-- A monic irreducible polynomial whose degree is at most `N`. -/
structure MonicIrreducibleLE (K : Type*) [CommRing K] (N : Nat) where
  /-- The underlying monic irreducible polynomial. -/
  poly : K[X]
  irreducible : Irreducible poly
  monic : poly.Monic
  natDegree_le : poly.natDegree ≤ N

namespace MonicIrreducibleLE

variable {K : Type*} [Field K] {N : Nat}

/-- A bounded monic irreducible, regarded as a bounded-degree polynomial. -/
noncomputable def toDegreeLT (P : MonicIrreducibleLE K N) :
    degreeLT K (N + 1) :=
  ⟨P.poly, by
    rw [mem_degreeLT, degree_eq_natDegree P.irreducible.ne_zero]
    exact_mod_cast Nat.lt_succ_of_le P.natDegree_le⟩

/-- The bounded irreducible embedding into the degree-limited type is injective. -/
theorem toDegreeLT_injective :
    Function.Injective (toDegreeLT : MonicIrreducibleLE K N → degreeLT K (N + 1)) := by
  intro P Q h
  cases P
  cases Q
  simp only [toDegreeLT] at h
  cases h
  rfl

/-- There are finitely many bounded-degree monic irreducibles over a finite
field. -/
noncomputable instance [Fintype K] : Fintype (MonicIrreducibleLE K N) := by
  letI : Fintype (degreeLT K (N + 1)) :=
    Fintype.ofEquiv (Fin (N + 1) → K) (degreeLTEquiv K (N + 1)).toEquiv.symm
  exact Fintype.ofInjective toDegreeLT toDegreeLT_injective

/-- The polynomial projection from bounded irreducibles is injective. -/
theorem poly_injective :
    Function.Injective (MonicIrreducibleLE.poly : MonicIrreducibleLE K N → K[X]) := by
  intro P Q h
  cases P
  cases Q
  cases h
  rfl

/-- Every irreducible factor has positive polynomial degree. -/
theorem natDegree_pos (P : MonicIrreducibleLE K N) : 0 < P.poly.natDegree :=
  P.irreducible.natDegree_pos

end MonicIrreducibleLE

variable {K : Type*} [Field K] {N : Nat}

/-- The product represented by a finitely supported irreducible-factor
multiplicity function. -/
noncomputable def monicFactorProduct
    (m : MonicIrreducibleLE K N →₀ Nat) : K[X] :=
  (m.toMultiset.map MonicIrreducibleLE.poly).prod

/-- The degree weight on irreducible-factor multiplicities. -/
noncomputable def monicFactorWeight :
    (MonicIrreducibleLE K N →₀ Nat) →+ Nat :=
  Finsupp.weight (fun P ↦ P.poly.natDegree)

/-- A product represented by a multiplicity function is monic. -/
theorem monicFactorProduct_monic
    (m : MonicIrreducibleLE K N →₀ Nat) :
    (monicFactorProduct m).Monic := by
  apply monic_multiset_prod_of_monic
  intro P hP
  exact P.monic

private theorem sum_map_toMultiset
    (m : MonicIrreducibleLE K N →₀ Nat)
    (w : MonicIrreducibleLE K N → Nat) :
    (m.toMultiset.map w).sum = m.sum (fun P c ↦ c • w P) := by
  classical
  refine m.induction ?_ ?_
  · simp [Finsupp.toMultiset_zero]
  · intro P n f hP hn ih
    rw [Finsupp.toMultiset_add, Multiset.map_add, Multiset.sum_add, ih,
      Finsupp.sum_add_index' (by simp) (by intros; exact add_nsmul _ _ _),
      Finsupp.sum_single_index (by simp), Finsupp.toMultiset_single,
      Multiset.map_nsmul, Multiset.map_singleton, Multiset.sum_nsmul,
      Multiset.sum_singleton]

/-- The degree of the represented product is its weighted factor degree. -/
theorem natDegree_monicFactorProduct
    (m : MonicIrreducibleLE K N →₀ Nat) :
    (monicFactorProduct m).natDegree = monicFactorWeight m := by
  have hmonic :
      ∀ f ∈ (m.toMultiset.map MonicIrreducibleLE.poly), f.Monic := by
    intro f hf
    obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hf
    exact P.monic
  rw [monicFactorProduct, natDegree_multiset_prod_of_monic _ hmonic,
    monicFactorWeight, Finsupp.weight_apply]
  simpa only [Multiset.map_map, Function.comp_apply] using
    sum_map_toMultiset m (fun P ↦ P.poly.natDegree)

variable [DecidableEq K]

/-- The normalized factors of a represented product are exactly its factor
multiset. -/
theorem normalizedFactors_monicFactorProduct
    (m : MonicIrreducibleLE K N →₀ Nat) :
    UniqueFactorizationMonoid.normalizedFactors (monicFactorProduct m) =
      m.toMultiset.map MonicIrreducibleLE.poly := by
  let s := m.toMultiset.map MonicIrreducibleLE.poly
  have hirr : ∀ f ∈ s, Irreducible f := by
    intro f hf
    obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hf
    exact P.irreducible
  change UniqueFactorizationMonoid.normalizedFactors s.prod = s
  rw [UniqueFactorizationMonoid.normalizedFactors_prod_eq s hirr]
  calc
    s.map normalize = s.map id := by
      apply Multiset.map_congr rfl
      intro f hf
      obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hf
      exact P.monic.normalize_eq_self
    _ = s := Multiset.map_id s

/-- The represented product map is injective. -/
theorem monicFactorProduct_injective :
    Function.Injective
      (monicFactorProduct : (MonicIrreducibleLE K N →₀ Nat) → K[X]) := by
  classical
  intro m r h
  have hmaps :
      m.toMultiset.map MonicIrreducibleLE.poly =
        r.toMultiset.map MonicIrreducibleLE.poly := by
    rw [← normalizedFactors_monicFactorProduct,
      ← normalizedFactors_monicFactorProduct, h]
  have hmulti : m.toMultiset = r.toMultiset :=
    Multiset.map_injective MonicIrreducibleLE.poly_injective hmaps
  calc
    m = Multiset.toFinsupp m.toMultiset :=
      (Finsupp.toMultiset_toFinsupp m).symm
    _ = Multiset.toFinsupp r.toMultiset := congrArg Multiset.toFinsupp hmulti
    _ = r := Finsupp.toMultiset_toFinsupp r

/-- Package a normalized factor of `F` as a bounded monic irreducible. -/
noncomputable def boundedNormalizedFactor
    {n : Nat} (hnN : n ≤ N)
    (F : {F : K[X] // F.Monic ∧ F.natDegree = n})
    (P : {P // P ∈ UniqueFactorizationMonoid.normalizedFactors F.1}) :
    MonicIrreducibleLE K N := by
  classical
  have hdata := (Polynomial.mem_normalizedFactors_iff F.2.1.ne_zero).mp P.2
  exact
    { poly := P.1
      irreducible := hdata.1
      monic := hdata.2.1
      natDegree_le :=
        (Polynomial.natDegree_le_of_dvd hdata.2.2 F.2.1.ne_zero).trans
          (F.2.2.le.trans hnN) }

/-- The normalized factors of a fixed-degree monic polynomial, packaged in
the bounded irreducible type. -/
noncomputable def boundedNormalizedFactors {n : Nat} (hnN : n ≤ N)
    (F : {F : K[X] // F.Monic ∧ F.natDegree = n}) :
    Multiset (MonicIrreducibleLE K N) :=
  (UniqueFactorizationMonoid.normalizedFactors F.1).attach.map
    (boundedNormalizedFactor hnN F)

/-- Mapping packaged bounded factors back to polynomials recovers normalized factors. -/
theorem map_boundedNormalizedFactors {n : Nat} (hnN : n ≤ N)
    (F : {F : K[X] // F.Monic ∧ F.natDegree = n}) :
    (boundedNormalizedFactors hnN F).map MonicIrreducibleLE.poly =
      UniqueFactorizationMonoid.normalizedFactors F.1 := by
  rw [boundedNormalizedFactors, Multiset.map_map]
  exact Multiset.attach_map_val _

/-- The weighted factor multiplicity attached to a monic polynomial. -/
noncomputable def monicFactorization {n : Nat} (hnN : n ≤ N)
    (F : {F : K[X] // F.Monic ∧ F.natDegree = n}) :
    MonicIrreducibleLE K N →₀ Nat := by
  classical
  exact Multiset.toFinsupp (boundedNormalizedFactors hnN F)

/-- The multiplicity factorization of a monic polynomial reproduces that polynomial. -/
theorem monicFactorProduct_factorization {n : Nat} (hnN : n ≤ N)
    (F : {F : K[X] // F.Monic ∧ F.natDegree = n}) :
    monicFactorProduct (monicFactorization hnN F) = F.1 := by
  classical
  rw [monicFactorProduct, monicFactorization,
    Multiset.toFinsupp_toMultiset, map_boundedNormalizedFactors,
    UniqueFactorizationMonoid.prod_normalizedFactors_eq F.2.1.ne_zero,
    F.2.1.normalize_eq_self]

/-- The multiplicity factorization has the original polynomial degree as weight. -/
theorem monicFactorWeight_factorization {n : Nat} (hnN : n ≤ N)
    (F : {F : K[X] // F.Monic ∧ F.natDegree = n}) :
    monicFactorWeight (monicFactorization hnN F) = n := by
  rw [← natDegree_monicFactorProduct, monicFactorProduct_factorization hnN F,
    F.2.2]

/-- A weighted factor multiplicity of total degree `n` determines a monic
degree-`n` polynomial. -/
noncomputable def weightedFactorsToMonic (n : Nat) :
    {m : MonicIrreducibleLE K N →₀ Nat // monicFactorWeight m = n} →
      {F : K[X] // F.Monic ∧ F.natDegree = n} :=
  fun m ↦ ⟨monicFactorProduct m.1, monicFactorProduct_monic m.1,
    (natDegree_monicFactorProduct m.1).trans m.2⟩

/-- Weighted bounded irreducible factorizations of degree `n` are equivalent
to monic degree-`n` polynomials. -/
noncomputable def weightedFactorsEquivMonic {n : Nat} (hnN : n ≤ N) :
    {m : MonicIrreducibleLE K N →₀ Nat // monicFactorWeight m = n} ≃
      {F : K[X] // F.Monic ∧ F.natDegree = n} :=
  Equiv.ofBijective (weightedFactorsToMonic n) ⟨by
    intro m r h
    apply Subtype.ext
    apply monicFactorProduct_injective
    exact congrArg Subtype.val h, by
    intro F
    let m : MonicIrreducibleLE K N →₀ Nat := monicFactorization hnN F
    have hm : monicFactorWeight m = n := monicFactorWeight_factorization hnN F
    refine ⟨⟨m, hm⟩, ?_⟩
    apply Subtype.ext
    exact monicFactorProduct_factorization hnN F⟩

end Weil

end Waring.Analytic
