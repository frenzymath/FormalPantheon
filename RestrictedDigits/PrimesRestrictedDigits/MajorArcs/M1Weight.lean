import PrimesRestrictedDigits.MajorArcs.Factorization
import PrimesRestrictedDigits.MajorArcs.WeightedPhaseSum

/-!
# Trivial region transform bound for the first major-arc class

This proves the explicit version of the bound
`S_(R_X)(theta) << X * (log X)^ell` used on
`MAYNARD-PRD-PUBLISHED`, p. 186.
-/

namespace PrimesRestrictedDigits

private theorem prime_of_mem_majorArcPrimeTuples
    (X : Nat) {r : Nat} (a : Fin r → Real) (delta regionEta : Real)
    (p : Fin (r + 1) → Nat)
    (hp : p ∈ majorArcPrimeTuples X a delta regionEta)
    (i : Fin (r + 1)) : (p i).Prime :=
  Nat.prime_of_mem_primesLE ((mem_majorArcPrimeTuples_iff.mp hp).1 i)

/-- The source region transform is bounded by its explicit total
logarithmic tuple mass. -/
theorem norm_majorArcRegionWeightedPhaseSum_le_log_pow
    (X : Nat) {r : Nat} (a : Fin r → Real)
    (delta regionEta theta : Real) (hX : 3 ≤ X) :
    ‖majorArcWeightedPhaseSum (Finset.range X)
        (fun n =>
          (majorArcRegionWeightAtProduct X a delta regionEta n : Complex))
        theta‖ ≤
      (X : Real) *
        (2 * Real.log 4 * Real.log (X : Real)) ^ (r + 1) := by
  apply (norm_majorArcWeightedPhaseSum_real_le_sum
    (Finset.range X) (majorArcRegionWeightAtProduct X a delta regionEta)
    (fun n hn => primeTupleWeightAtProduct_nonneg
      (majorArcPrimeTuples X a delta regionEta) n) theta).trans
  exact sum_primeTupleWeightAtProduct_le_mul_log_pow X
    (majorArcPrimeTuples X a delta regionEta)
    (fun p hp i =>
      prime_of_mem_majorArcPrimeTuples X a delta regionEta p hp i) hX

end PrimesRestrictedDigits
