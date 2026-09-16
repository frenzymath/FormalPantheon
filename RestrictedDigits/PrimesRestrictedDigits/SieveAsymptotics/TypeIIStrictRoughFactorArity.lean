import PrimesRestrictedDigits.SieveAsymptotics.TypeIIStableLabeledFactorization
import PrimesRestrictedDigits.MajorArcs.Factorization
import PrimesRestrictedDigits.SieveDecomposition.Definitions
import Mathlib.Data.Nat.Factors
import Mathlib.Tactic.Positivity

/-!
# Strict rough factors and total Type II arity

This is the finite bridge used by the strict version of the Type II transfer. It keeps the
residual endpoint strict, the outer endpoint weak, and uses the strict complete-product cutoff
to obtain a strict normalized-log budget.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- For a nonzero cofactor, strict roughness is equivalent to a lower bound on
every entry of its canonical prime-factor list (with multiplicity). -/
theorem strictRoughPredicate_iff_forall_mem_primeFactorsList
    {z : Real} {m : Nat} (hm : m ≠ 0) :
    strictRoughPredicate z m ↔
      ∀ q, q ∈ m.primeFactorsList → z < (q : Real) := by
  constructor
  · intro h q hq
    exact h q (Nat.prime_of_mem_primeFactorsList hq)
      (Nat.dvd_of_mem_primeFactorsList hq)
  · intro h q hqPrime hqDvd
    exact h q ((Nat.mem_primeFactorsList hm).2 ⟨hqPrime, hqDvd⟩)

/-- Every coordinate of the stable complete tuple is at least the common
real-power threshold.  The outer hypothesis is intentionally weak; strict
roughness is weakened only in this forward coordinate bound. -/
theorem typeIIStableFactorTuple_rpow_lower
    {X : Nat} {ell m : Nat} {eta : Real} {outer : Fin ell → Nat}
    (houterLower : ∀ i, (X : Real) ^ eta ≤ (outer i : Real))
    (hrough : strictRoughPredicate ((X : Real) ^ eta) m) :
    ∀ i, (X : Real) ^ eta ≤
      (typeIIStableFactorTuple outer m i : Real) := by
  intro i
  let σ := typeIIStableFactorPermutation outer m
  have hraw : (X : Real) ^ eta ≤
      (typeIICombinedLabeledFactors outer m (σ i) : Real) := by
    refine Fin.addCases ?_ ?_ (σ i)
    · intro j
      simpa [typeIICombinedLabeledFactors] using houterLower j
    · intro j
      have hj : m.primeFactorsList.get j ∈ m.primeFactorsList :=
        List.get_mem _ j
      have hjPrime : (m.primeFactorsList.get j).Prime := by
        exact Nat.prime_of_mem_primeFactorsList hj
      have hjDvd : m.primeFactorsList.get j ∣ m :=
        Nat.dvd_of_mem_primeFactorsList hj
      have hstrict := hrough (m.primeFactorsList.get j) hjPrime hjDvd
      have hweak : (X : Real) ^ eta ≤
          (m.primeFactorsList.get j : Real) := hstrict.le
      simpa [typeIICombinedLabeledFactors] using hweak
  simpa [typeIIStableFactorTuple, Function.comp_apply, σ] using hraw

/-- Strict product size and coordinate lower bounds force the total number of
prime factors to consume strictly less than the unit logarithmic budget. -/
theorem typeIIStableFactorArity_mul_eta_lt_one
    {X ell m : Nat} {eta : Real} {outer : Fin ell → Nat}
    (hX : 1 < X) (heta : 0 < eta) (hm : m ≠ 0)
    (houterPrime : ∀ i, (outer i).Prime)
    (houterLower : ∀ i, (X : Real) ^ eta ≤ (outer i : Real))
    (hrough : strictRoughPredicate ((X : Real) ^ eta) m)
    (hproduct : primeTupleProduct outer * m < X) :
    (((ell + m.primeFactorsList.length : Nat) : Real) * eta) < 1 := by
  have heta_nonneg : 0 ≤ eta := heta.le
  let r := ell + m.primeFactorsList.length
  let p := typeIIStableFactorTuple outer m
  have hpPrime : ∀ i, (p i).Prime := by
    intro i
    exact prime_typeIIStableFactorTuple outer m houterPrime i
  have hpLower : ∀ i, (X : Real) ^ eta ≤ (p i : Real) := by
    intro i
    exact typeIIStableFactorTuple_rpow_lower houterLower hrough i
  have hXreal : (1 : Real) < (X : Real) := by
    exact_mod_cast hX
  have hnormalized : ∀ i, eta ≤ normalizedPrimeLog X (p i) := by
    intro i
    have hpiPos : (0 : Real) < (p i : Real) := by
      exact_mod_cast (hpPrime i).pos
    change eta ≤ Real.logb (X : Real) (p i : Real)
    exact (Real.le_logb_iff_rpow_le hXreal hpiPos).2 (hpLower i)
  have hsumLower : ((r : Nat) : Real) * eta ≤
      ∑ i, normalizedPrimeLog X (p i) := by
    calc
      ((r : Nat) : Real) * eta = ∑ _ : Fin r, eta := by
        simp [r]
      _ ≤ ∑ i, normalizedPrimeLog X (p i) := by
        apply Finset.sum_le_sum
        intro i hi
        exact hnormalized i
  have hpProduct : primeTupleProduct p < X := by
    rw [primeTupleProduct_typeIIStableFactorTuple outer m hm]
    exact hproduct
  have hsumUpper : (∑ i, normalizedPrimeLog X (p i)) < 1 :=
    sum_normalizedPrimeLog_lt_one_of_product_lt hX
      (fun i => hpPrime i) hpProduct
  exact lt_of_le_of_lt hsumLower hsumUpper

/-- The arity cap accepted by Proposition 7.2 follows from the strict budget
bound, with a deliberately weak factor of two. -/
theorem typeIIStableFactorArity_le_two_div_eta
    {X ell m : Nat} {eta : Real} {outer : Fin ell → Nat}
    (hX : 1 < X) (heta : 0 < eta) (hm : m ≠ 0)
    (houterPrime : ∀ i, (outer i).Prime)
    (houterLower : ∀ i, (X : Real) ^ eta ≤ (outer i : Real))
    (hrough : strictRoughPredicate ((X : Real) ^ eta) m)
    (hproduct : primeTupleProduct outer * m < X) :
    (((ell + m.primeFactorsList.length : Nat) : Real) ≤ 2 / eta) := by
  have hstrict := typeIIStableFactorArity_mul_eta_lt_one hX heta hm
    houterPrime houterLower hrough hproduct
  let r : Real := ((ell + m.primeFactorsList.length : Nat) : Real)
  have hr : r < 1 / eta := by
    apply (lt_div_iff₀ heta).2
    simpa [r, mul_comm] using hstrict
  have hone : (1 : Real) / eta ≤ 2 / eta := by
    apply (div_le_div_iff_of_pos_right heta).2
    norm_num
  exact hr.le.trans hone

end

end PrimesRestrictedDigits
