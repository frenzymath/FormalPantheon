import PrimesRestrictedDigits.ExceptionalMinorArcs.SplitProductScales

/-!
# Coordinate fibers for the two localized prime products

The paired product-scale fiber factors into two independent positive coordinate fibers. This
is the exact carrier used when extending a localized Perron sum to the source intervals in
Lemma 13.1.
-/

namespace PrimesRestrictedDigits

/-- Positive naturals below the decimal ambient scale with one canonical
factor-ten index. -/
def splitProductCoordinateFiber (length i : Nat) : Finset Nat :=
  (Finset.Ico 1 (10 ^ length)).filter fun n => factorTenIndex n = i

@[simp]
theorem mem_splitProductCoordinateFiber_iff
    {length i n : Nat} :
    n ∈ splitProductCoordinateFiber length i ↔
      n ∈ Finset.Ico 1 (10 ^ length) ∧ factorTenIndex n = i := by
  simp [splitProductCoordinateFiber]

/-- The paired canonical fiber is exactly the product of its two coordinate
fibers. -/
theorem splitProductScaleFiber_eq_coordinateProduct
    (length : Nat) (key : Nat × Nat) :
    splitProductScaleFiber length key =
      (splitProductCoordinateFiber length key.1).product
        (splitProductCoordinateFiber length key.2) := by
  ext nm
  simp only [mem_splitProductScaleFiber_iff, splitProductScaleKey]
  aesop

/-- Membership in a coordinate fiber identifies its represented real scale
with the input's canonical factor-ten scale. -/
theorem splitProductScaleAt_eq_factorTenScale_of_mem
    {length i n : Nat}
    (hn : n ∈ splitProductCoordinateFiber length i) :
    splitProductScaleAt i = (factorTenScale n : Real) := by
  have hindex := (mem_splitProductCoordinateFiber_iff.mp hn).2
  rw [← hindex, splitProductScaleAt_factorTenIndex]

/-- Every coordinate-fiber member lies in the literal source interval
represented by that fiber. -/
theorem splitProductCoordinateFiber_mem_sourceInterval
    {length i n : Nat}
    (hn : n ∈ splitProductCoordinateFiber length i) :
    n ∈ sourceFactorTenNaturalInterval (splitProductScaleAt i) := by
  rw [splitProductScaleAt_eq_factorTenScale_of_mem hn]
  exact mem_sourceFactorTenNaturalInterval_factorTenScale
    (Finset.mem_Ico.mp (mem_splitProductCoordinateFiber_iff.mp hn).1).1

/-- Coordinate fibers contain only positive naturals. -/
theorem splitProductCoordinateFiber_pos
    {length i n : Nat}
    (hn : n ∈ splitProductCoordinateFiber length i) :
    0 < n :=
  (Finset.mem_Ico.mp (mem_splitProductCoordinateFiber_iff.mp hn).1).1

/-- Coordinate fibers retain the strict ambient cutoff, including at the
terminal decimal index. -/
theorem splitProductCoordinateFiber_lt_ambient
    {length i n : Nat}
    (hn : n ∈ splitProductCoordinateFiber length i) :
    n < 10 ^ length :=
  (Finset.mem_Ico.mp (mem_splitProductCoordinateFiber_iff.mp hn).1).2

end PrimesRestrictedDigits
