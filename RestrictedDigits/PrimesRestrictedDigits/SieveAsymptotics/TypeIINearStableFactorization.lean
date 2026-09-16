import PrimesRestrictedDigits.SieveAsymptotics.TypeIIStrictRoughFactorArity
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIRegionSupport

/-!
# Near-product stable factorization

This file places the complete stable prime-factor tuple in the ordered exponent simplex after
normalization by its represented product. It also records the explicit source-region support
landing used by the strict Type II adapters.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- A nontrivial stable complete factorization, normalized by its represented
product `N`, lies in the ordered `eta`-simplex. -/
theorem normalized_typeIIStableFactorTuple_mem_exponentSimplex
    {X N ell m : Nat} {eta : Real} {outer : Fin ell -> Nat}
    (heta : 0 < eta) (hm : m ≠ 0)
    (houterPrime : forall i, (outer i).Prime)
    (houterLower : forall i, (X : Real) ^ eta <= (outer i : Real))
    (hrough : strictRoughPredicate ((X : Real) ^ eta) m)
    (hproduct : primeTupleProduct outer * m = N)
    (hN : 1 < N) (hNX : N < X) :
    (fun i => normalizedPrimeLog N
      (typeIIStableFactorTuple outer m i)) ∈
      typeIIExponentSimplex eta := by
  let p := typeIIStableFactorTuple outer m
  have hpPrime : forall i, (p i).Prime :=
    prime_typeIIStableFactorTuple outer m houterPrime
  have hpProduct : primeTupleProduct p = N := by
    calc
      primeTupleProduct p = primeTupleProduct outer * m := by
        simpa only [p] using
          primeTupleProduct_typeIIStableFactorTuple outer m hm
      _ = N := hproduct
  have hcoordinates :=
    normalizedPrimeLog_product_coordinates hN hpPrime hpProduct
  have hpLowerX : forall i, (X : Real) ^ eta <= (p i : Real) :=
    typeIIStableFactorTuple_rpow_lower houterLower hrough
  have hNLeX : (N : Real) <= (X : Real) := by
    exact_mod_cast hNX.le
  have hpLowerN : forall i, (N : Real) ^ eta <= (p i : Real) := by
    intro i
    exact (Real.rpow_le_rpow (by positivity) hNLeX heta.le).trans
      (hpLowerX i)
  have hNReal : (1 : Real) < (N : Real) := by
    exact_mod_cast hN
  have hlogLower : forall i, eta <= normalizedPrimeLog N (p i) := by
    intro i
    change eta <= Real.logb (N : Real) (p i : Real)
    exact (Real.le_logb_iff_rpow_le hNReal
      (by exact_mod_cast (hpPrime i).pos)).2 (hpLowerN i)
  have hlogMonotone :
      Monotone (fun i => normalizedPrimeLog N (p i)) := by
    intro i j hij
    change Real.logb (N : Real) (p i : Real) <=
      Real.logb (N : Real) (p j : Real)
    exact Real.logb_le_logb_of_le hNReal
      (by exact_mod_cast (hpPrime i).pos)
      (by exact_mod_cast (monotone_typeIIStableFactorTuple outer m hij))
  exact by
    simpa only [p] using
      (show (fun i => normalizedPrimeLog N (p i)) ∈
          typeIIExponentSimplex eta from
        ⟨hlogLower, hlogMonotone, hcoordinates.1⟩)

/-- Explicit membership of the stable normalized point in a source region
places its represented product in the corresponding finite support. -/
theorem typeIIStableFactorProduct_mem_originalRegionSupport
    {X N ell m : Nat} {outer : Fin ell -> Nat}
    {region : Set (Fin (ell + m.primeFactorsList.length) -> Real)}
    (hNX : N < X) (hm : m ≠ 0)
    (houterPrime : forall i, (outer i).Prime)
    (hproduct : primeTupleProduct outer * m = N)
    (hregion : (fun i => normalizedPrimeLog N
      (typeIIStableFactorTuple outer m i)) ∈ region) :
    N ∈ typeIIOriginalRegionSupport X region := by
  have hpPrime : forall i,
      (typeIIStableFactorTuple outer m i).Prime :=
    prime_typeIIStableFactorTuple outer m houterPrime
  have hpProduct :
      primeTupleProduct (typeIIStableFactorTuple outer m) = N := by
    calc
      primeTupleProduct (typeIIStableFactorTuple outer m) =
          primeTupleProduct outer * m :=
        primeTupleProduct_typeIIStableFactorTuple outer m hm
      _ = N := hproduct
  exact mem_typeIIOriginalRegionSupport.mpr
    ⟨hNX, typeIIStableFactorTuple outer m, hpPrime, hpProduct, hregion⟩

end

end PrimesRestrictedDigits
