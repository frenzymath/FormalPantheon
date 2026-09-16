import PrimesRestrictedDigits.GenericMinorArcs.PrimeTupleL2
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIReduction

/-!
# Prime-tuple multiplicity for the Type II reduction

This file supplies the finite counting and strict-roughness bridges used in the shortened
route through Maynard's Eq. (9.11).
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- Coordinatewise strict lower bounds on a prime tuple make its product
strictly rough at the same threshold. -/
theorem strictRoughPredicate_primeTupleProduct
    {ell : Nat} {z : Real} {p : Fin ell -> Nat}
    (hprime : forall i, (p i).Prime)
    (hlower : forall i, z < (p i : Real)) :
    strictRoughPredicate z (primeTupleProduct p) := by
  intro r hr hdiv
  rw [primeTupleProduct] at hdiv
  obtain ⟨i, _hi, hri⟩ := (hr.prime.dvd_finsetProd_iff p).mp hdiv
  have hir : r = p i :=
    (Nat.prime_dvd_prime_iff_eq hr (hprime i)).mp hri
  simpa [hir] using hlower i

/-- Ordered prime tuples landing in a finite carrier are bounded by the
factorial product-fiber multiplicity times its strict-sifted cardinality. -/
theorem card_primeTuples_product_mem_le_factorial_mul_sifted
    {ell : Nat} (C : Finset Nat) (z : Real)
    (tuples : Finset (Fin ell -> Nat))
    (hprime : ∀ p ∈ tuples, ∀ i, (p i).Prime)
    (hrough : ∀ p ∈ tuples,
      strictRoughPredicate z (primeTupleProduct p)) :
    (tuples.filter fun p => primeTupleProduct p ∈ C).card <=
      Nat.factorial ell * (strictSiftedCarrier C z).card := by
  classical
  apply Finset.card_le_mul_card_image_of_maps_to
      (f := primeTupleProduct)
      (s := tuples.filter fun p => primeTupleProduct p ∈ C)
      (t := strictSiftedCarrier C z)
  · intro p hp
    rw [mem_strictSiftedCarrier]
    exact ⟨(Finset.mem_filter.mp hp).2,
      hrough p (Finset.mem_filter.mp hp).1⟩
  · intro n _hn
    apply card_primeTupleProductFiber_le_factorial
    intro p hp i
    exact hprime p (Finset.mem_filter.mp hp).1 i

/-- The real arity bound implies the corresponding natural factorial cap. -/
theorem factorial_le_arityCeil
    {ell : Nat} {eta : Real}
    (hell : (ell : Real) <= 2 / eta) :
    Nat.factorial ell <= Nat.factorial (Nat.ceil (2 / eta)) := by
  apply Nat.monotone_factorial
  exact_mod_cast hell.trans (Nat.le_ceil (2 / eta))

/-- A major-arc prime tuple is strictly rough at the lowered `eta/8`
threshold, including at the weak endpoint for its final coordinate. -/
theorem majorArcPrimeTuple_strictRough_etaEighth
    {X k : Nat} {a : Fin k -> Real} {delta eta : Real}
    (hX : 1 < X) (heta : 0 < eta)
    (ha : forall i, eta / 2 <= a i)
    {p : Fin (k + 1) -> Nat}
    (hp : p ∈ majorArcPrimeTuples X a delta eta) :
    strictRoughPredicate ((X : Real) ^ (eta / 8))
      (primeTupleProduct p) := by
  have hpData := mem_majorArcPrimeTuples_iff.mp hp
  have hprime : forall i, (p i).Prime := fun i =>
    Nat.prime_of_mem_primesLE (hpData.1 i)
  apply strictRoughPredicate_primeTupleProduct hprime
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have hlastNormalized :
        max (eta / 4)
            (1 - (∑ j, a j) - ((k + 1 : Nat) : Real) * delta) <=
          normalizedPrimeLog X (p (Fin.last k)) := by
      exact hpData.2.2.2
    have hlastLower :
        (X : Real) ^ (eta / 4) <= (p (Fin.last k) : Real) :=
      ((max_le_normalizedPrimeLog_iff_rpow_le hX
        (hprime (Fin.last k)) _ _).mp hlastNormalized).1
    exact (Real.rpow_lt_rpow_of_exponent_lt
      (by exact_mod_cast hX) (by linarith)).trans_le hlastLower
  · have hbox :
        normalizedPrimeLog X (p j.castSucc) ∈
          Set.Ioc (a j) (a j + delta) := by
      simpa [majorArcLogRegion, projectedLogBox, Fin.init_def] using
        hpData.2.1 j
    have hlower : (X : Real) ^ (a j) < (p j.castSucc : Real) :=
      ((normalizedPrimeLog_mem_Ioc_iff_rpow hX
        (hprime j.castSucc) _ _).mp hbox).1
    have hexponent : eta / 8 < a j := by
      linarith [ha j]
    exact (Real.rpow_lt_rpow_of_exponent_lt
      (by exact_mod_cast hX) hexponent).trans hlower

end

end PrimesRestrictedDigits
