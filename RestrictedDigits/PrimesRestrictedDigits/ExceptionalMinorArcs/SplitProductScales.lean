import PrimesRestrictedDigits.ExceptionalMinorArcs.SplitPrimeBounds
import PrimesRestrictedDigits.ExceptionalMinorArcs.BilinearIntervals
import PrimesRestrictedDigits.LatticeEstimates.DecompositionScales

/-!
# Canonical decimal scales for the two prime products

This implements the exact two-product factor-ten localization.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- Canonical pair of decimal indices for two positive natural products. -/
def splitProductScaleKey (nm : Nat × Nat) : Nat × Nat :=
  (factorTenIndex nm.1, factorTenIndex nm.2)

/-- All product-scale keys below decimal ambient scale `10^length`. -/
def splitProductScaleKeys (length : Nat) : Finset (Nat × Nat) :=
  (Finset.range (length + 1)).product (Finset.range (length + 1))

/-- Positive product pairs below `10^length` assigned to one canonical key. -/
def splitProductScaleFiber
    (length : Nat) (key : Nat × Nat) : Finset (Nat × Nat) :=
  ((Finset.Ico 1 (10 ^ length)).product
      (Finset.Ico 1 (10 ^ length))).filter fun nm =>
    splitProductScaleKey nm = key

/-- Real upper scale represented by one product index. -/
def splitProductScaleAt (i : Nat) : Real :=
  ((10 ^ i : Nat) : Real)

@[simp]
theorem mem_splitProductScaleFiber_iff
    {length : Nat} {key nm : Nat × Nat} :
    nm ∈ splitProductScaleFiber length key ↔
      nm.1 ∈ Finset.Ico 1 (10 ^ length) ∧
      nm.2 ∈ Finset.Ico 1 (10 ^ length) ∧
        splitProductScaleKey nm = key := by
  simp [splitProductScaleFiber, and_assoc]

/-- A positive value below `10^length` has canonical index at most
`length`. -/
theorem factorTenIndex_le_length_of_mem_Ico
    {length n : Nat} (hn : n ∈ Finset.Ico 1 (10 ^ length)) :
    factorTenIndex n <= length := by
  apply factorTenIndex_le_of_le_ten_pow
  exact (Finset.mem_Ico.mp hn).2.le

/-- Every positive product pair below the ambient scale has a key. -/
theorem splitProductScaleKey_mem
    {length : Nat} {nm : Nat × Nat}
    (hnm : nm ∈ (Finset.Ico 1 (10 ^ length)).product
      (Finset.Ico 1 (10 ^ length))) :
    splitProductScaleKey nm ∈ splitProductScaleKeys length := by
  rw [splitProductScaleKeys]
  apply Finset.mem_product.mpr
  have hdata := Finset.mem_product.mp hnm
  change factorTenIndex nm.1 ∈ Finset.range (length + 1) ∧
    factorTenIndex nm.2 ∈ Finset.range (length + 1)
  exact ⟨Finset.mem_range.mpr <| Nat.lt_succ_of_le
      (factorTenIndex_le_length_of_mem_Ico hdata.1),
    Finset.mem_range.mpr <| Nat.lt_succ_of_le
      (factorTenIndex_le_length_of_mem_Ico hdata.2)⟩

/-- Exact disjoint recovery of every finite pair sum from its canonical
product-scale fibers. -/
theorem sum_splitProductScaleFibers
    {M : Type*} [AddCommMonoid M]
    (length : Nat) (f : Nat × Nat -> M) :
    (∑ key ∈ splitProductScaleKeys length,
      ∑ nm ∈ splitProductScaleFiber length key, f nm) =
      ∑ nm ∈ (Finset.Ico 1 (10 ^ length)).product
        (Finset.Ico 1 (10 ^ length)), f nm := by
  classical
  unfold splitProductScaleFiber
  apply Finset.sum_fiberwise_of_maps_to
  intro nm hnm
  exact splitProductScaleKey_mem hnm

@[simp]
theorem card_splitProductScaleKeys (length : Nat) :
    (splitProductScaleKeys length).card = (length + 1) ^ 2 := by
  simp [splitProductScaleKeys, pow_two]

/-- A positive natural lies in the literal source interval represented by its
canonical scale. -/
theorem mem_sourceFactorTenNaturalInterval_factorTenScale
    {n : Nat} (hn : 0 < n) :
    n ∈ sourceFactorTenNaturalInterval (factorTenScale n : Real) := by
  rw [mem_sourceFactorTenNaturalInterval_iff (by positivity)]
  exact factorTenScale_band n hn

@[simp]
theorem splitProductScaleAt_factorTenIndex (n : Nat) :
    splitProductScaleAt (factorTenIndex n) = (factorTenScale n : Real) := by
  rfl

/-- Canonical scales of an active product pair lose strictly less than a
factor one hundred. -/
theorem factorTenScales_mul_lt_hundred_mul
    {X n m : Nat} (hn : 0 < n) (hm : 0 < m) (hnm : n * m < X) :
    (factorTenScale n : Real) * (factorTenScale m : Real) <
      100 * (X : Real) := by
  have hnScale : (factorTenScale n : Real) < 10 * (n : Real) := by
    exact_mod_cast factorTenScale_lt_ten_mul hn
  have hmScale : (factorTenScale m : Real) < 10 * (m : Real) := by
    exact_mod_cast factorTenScale_lt_ten_mul hm
  have hmScalePos : (0 : Real) < factorTenScale m := by
    exact_mod_cast factorTenScale_pos m
  have hnTenPos : (0 : Real) < 10 * n := by positivity
  have hnmReal : ((n * m : Nat) : Real) < (X : Real) := by
    exact_mod_cast hnm
  calc
    (factorTenScale n : Real) * (factorTenScale m : Real) <
        (10 * (n : Real)) * (factorTenScale m : Real) :=
      mul_lt_mul_of_pos_right hnScale hmScalePos
    _ < (10 * (n : Real)) * (10 * (m : Real)) :=
      mul_lt_mul_of_pos_left hmScale hnTenPos
    _ = 100 * ((n * m : Nat) : Real) := by
      norm_num only [Nat.cast_mul]
      ring
    _ < 100 * (X : Real) := by nlinarith

/-- A pair in one canonical fiber lies in the two literal source intervals
represented by that key. -/
theorem splitProductScaleFiber_mem_sourceIntervals
    {length : Nat} {key nm : Nat × Nat}
    (hnm : nm ∈ splitProductScaleFiber length key) :
    nm.1 ∈ sourceFactorTenNaturalInterval (splitProductScaleAt key.1) ∧
      nm.2 ∈ sourceFactorTenNaturalInterval (splitProductScaleAt key.2) := by
  have hdata := mem_splitProductScaleFiber_iff.mp hnm
  have hfirst := congrArg Prod.fst hdata.2.2
  have hsecond := congrArg Prod.snd hdata.2.2
  simp only [splitProductScaleKey] at hfirst hsecond
  rw [← hfirst, ← hsecond, splitProductScaleAt_factorTenIndex,
    splitProductScaleAt_factorTenIndex]
  exact ⟨mem_sourceFactorTenNaturalInterval_factorTenScale
      (Finset.mem_Ico.mp hdata.1).1,
    mem_sourceFactorTenNaturalInterval_factorTenScale
      (Finset.mem_Ico.mp hdata.2.1).1⟩

end

end PrimesRestrictedDigits
