import PrimesRestrictedDigits.SieveDecomposition.SectionSixFirstRepeatedCarriers
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Pair regions in the first strict Section 6 branches

This file defines the finite ten-way partition of the two strict nested prime sums. The
retained and residual classes use the endpoint assignment in the product walls `z2`, `z3`,
`z5`, and `z6` are closed on the residual bands, while equality at `p q^2 = z6` is on the
large central side.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

abbrev SectionSixFirstStrictIndex := SectionSixFirstSecondRepeatedIndex

noncomputable def sectionSixFirstLowStrictIndices
    (epsilon : Real) (length : Nat) :
    Finset SectionSixFirstStrictIndex :=
  let X : Real := ((10 ^ length : Nat) : Real)
  sectionSixFirstSecondRepeatedIndices length
    (sectionSixZOne epsilon X) (sectionSixZOne epsilon X)
    (sectionSixZTwo epsilon X)

noncomputable def sectionSixFirstHighStrictIndices
    (epsilon : Real) (length : Nat) :
    Finset SectionSixFirstStrictIndex :=
  let X : Real := ((10 ^ length : Nat) : Real)
  sectionSixFirstSecondRepeatedIndices length
    (sectionSixZOne epsilon X) (sectionSixZThree epsilon X)
    (sectionSixZFour X)

noncomputable def sectionSixFirstStrictIndices
    (epsilon : Real) (length : Nat) :
    Finset SectionSixFirstStrictIndex :=
  sectionSixFirstLowStrictIndices epsilon length ∪
    sectionSixFirstHighStrictIndices epsilon length

/-- Reindex the low strict branch by its existing dependent Sigma carrier. -/
theorem sectionSixFirstSecondStrictSum_eq_indexSum
    (digit : Fin 10) (length : Nat) (z a b : Real) :
    sectionSixFirstSecondStrictSum digit length z a b =
      ∑ index ∈ sectionSixFirstSecondRepeatedIndices length z a b,
        sectionSixStrictPrimeTerm digit length
          (Nat.toPNat' index.1) index.2 := by
  unfold sectionSixFirstSecondStrictSum
    sectionSixFirstSecondRepeatedIndices
  rw [Finset.sum_sigma']

def sectionSixFirstPairProduct (index : SectionSixFirstStrictIndex) : Nat :=
  index.1 * index.2

def sectionSixFirstPairSquareProduct
    (index : SectionSixFirstStrictIndex) : Nat :=
  index.1 * index.2 * index.2

inductive SectionSixFirstPairPiece
  | lowBelow
  | lowFar
  | lowCentralLarge
  | lowCentralSmall
  | lowBandFirst
  | lowBandSecond
  | highFar
  | highCentralLarge
  | highCentralSmall
  | highBandSecond
  deriving DecidableEq

def sectionSixFirstPairMem
    (epsilon : Real) (length : Nat)
    (piece : SectionSixFirstPairPiece)
    (index : SectionSixFirstStrictIndex) : Prop :=
  let X : Real := ((10 ^ length : Nat) : Real)
  let z1 : Real := sectionSixZOne epsilon X
  let z2 : Real := sectionSixZTwo epsilon X
  let z3 : Real := sectionSixZThree epsilon X
  let z5 : Real := sectionSixZFive epsilon X
  let z6 : Real := sectionSixZSix epsilon X
  let product : Real := (sectionSixFirstPairProduct index : Real)
  let squareProduct : Real :=
    (sectionSixFirstPairSquareProduct index : Real)
  match piece with
  | .lowBelow => index ∈ sectionSixFirstLowStrictIndices epsilon length ∧
      z1 < product ∧ product < z2
  | .lowFar => index ∈ sectionSixFirstLowStrictIndices epsilon length ∧
      z6 < product
  | .lowCentralLarge =>
      index ∈ sectionSixFirstLowStrictIndices epsilon length ∧
      z3 < product ∧ product < z5 ∧ z6 <= squareProduct
  | .lowCentralSmall =>
      index ∈ sectionSixFirstLowStrictIndices epsilon length ∧
      z3 < product ∧ product < z5 ∧ squareProduct < z6
  | .lowBandFirst => index ∈ sectionSixFirstLowStrictIndices epsilon length ∧
      z2 <= product ∧ product <= z3
  | .lowBandSecond => index ∈ sectionSixFirstLowStrictIndices epsilon length ∧
      z5 <= product ∧ product <= z6
  | .highFar => index ∈ sectionSixFirstHighStrictIndices epsilon length ∧
      z6 < product
  | .highCentralLarge =>
      index ∈ sectionSixFirstHighStrictIndices epsilon length ∧
      z3 < product ∧ product < z5 ∧ z6 <= squareProduct
  | .highCentralSmall =>
      index ∈ sectionSixFirstHighStrictIndices epsilon length ∧
      z3 < product ∧ product < z5 ∧ squareProduct < z6
  | .highBandSecond =>
      index ∈ sectionSixFirstHighStrictIndices epsilon length ∧
      z5 <= product ∧ product <= z6

private theorem sectionSixFirst_hX
    {length : Nat} (hlength : 1 <= length) :
    (1 : Real) < ((10 ^ length : Nat) : Real) := by
  exact_mod_cast Nat.one_lt_pow (by omega : length ≠ 0)
    (by norm_num : 1 < (10 : Nat))

private theorem sectionSixFirst_horder
    {epsilon : Real} {length : Nat}
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length) :
    sectionSixZOne epsilon ((10 ^ length : Nat) : Real) <
        sectionSixZTwo epsilon ((10 ^ length : Nat) : Real) ∧
      sectionSixZTwo epsilon ((10 ^ length : Nat) : Real) <
        sectionSixZThree epsilon ((10 ^ length : Nat) : Real) ∧
      sectionSixZThree epsilon ((10 ^ length : Nat) : Real) <
        sectionSixZFour ((10 ^ length : Nat) : Real) ∧
      sectionSixZFour ((10 ^ length : Nat) : Real) <
        sectionSixZFive epsilon ((10 ^ length : Nat) : Real) ∧
      sectionSixZFive epsilon ((10 ^ length : Nat) : Real) <
        sectionSixZSix epsilon ((10 ^ length : Nat) : Real) :=
  sectionSix_cutoffs_strict hepsilon hepsilonSmall
    (sectionSixFirst_hX hlength)

private theorem sectionSixFirst_low_high_disjoint
    {epsilon : Real} {length : Nat}
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length) {index : SectionSixFirstStrictIndex}
    (hLow : index ∈ sectionSixFirstLowStrictIndices epsilon length)
    (hHigh : index ∈ sectionSixFirstHighStrictIndices epsilon length) :
    False := by
  have ho := sectionSixFirst_horder hepsilon hepsilonSmall hlength
  have hlo := (mem_sectionSixFirstSecondRepeatedIndices.mp hLow).1
  have hhi := (mem_sectionSixFirstSecondRepeatedIndices.mp hHigh).1
  have hlo' := mem_sievePrimeInterval.mp hlo
  have hhi' := mem_sievePrimeInterval.mp hhi
  linarith [hlo'.2.2, hhi'.2.1, ho.1, ho.2.1]

private theorem sectionSixFirst_index_product_gt_z3_low_or_high
    {epsilon : Real} {length : Nat}
    {index : SectionSixFirstStrictIndex}
    (hHigh : index ∈ sectionSixFirstHighStrictIndices epsilon length) :
    sectionSixZThree epsilon ((10 ^ length : Nat) : Real) <
      (sectionSixFirstPairProduct index : Real) := by
  have hdata := mem_sectionSixFirstSecondRepeatedIndices.mp hHigh
  have hpData := mem_sievePrimeInterval.mp hdata.1
  have hqData := mem_sievePrimeInterval.mp hdata.2
  have hqOne : (1 : Real) <= (index.2 : Real) := by
    have hqPrime : index.2.Prime := hqData.1
    exact_mod_cast hqPrime.one_le
  have hpPos : (0 : Real) <= (index.1 : Real) := by
    exact_mod_cast (Nat.zero_le index.1)
  have hprod : (index.1 : Real) <=
      (index.1 : Real) * (index.2 : Real) := by
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left hqOne hpPos)
  simpa only [sectionSixFirstPairProduct, Nat.cast_mul] using
    hpData.2.1.trans_le hprod

private theorem sectionSixFirst_index_product_gt_z1_of_low
    {epsilon : Real} {length : Nat}
    {index : SectionSixFirstStrictIndex}
    (hLow : index ∈ sectionSixFirstLowStrictIndices epsilon length) :
    sectionSixZOne epsilon ((10 ^ length : Nat) : Real) <
      (sectionSixFirstPairProduct index : Real) := by
  have hdata := mem_sectionSixFirstSecondRepeatedIndices.mp hLow
  have hpData := mem_sievePrimeInterval.mp hdata.1
  have hqData := mem_sievePrimeInterval.mp hdata.2
  have hpLower := hpData.2.1
  have hqOne : (1 : Real) <= (index.2 : Real) := by
    exact_mod_cast hqData.1.one_le
  have hpNonneg : (0 : Real) <= (index.1 : Real) := by
    exact_mod_cast (Nat.zero_le index.1)
  have hprod : (index.1 : Real) <=
      (index.1 : Real) * (index.2 : Real) := by
    calc
      (index.1 : Real) = (index.1 : Real) * 1 := by ring
      _ <= (index.1 : Real) * (index.2 : Real) :=
        mul_le_mul_of_nonneg_left hqOne hpNonneg
  simpa only [sectionSixFirstPairProduct, Nat.cast_mul] using
    lt_of_lt_of_le hpLower hprod

set_option maxHeartbeats 1000000 in
theorem sectionSixFirstStrictIndices_partition
    (epsilon : Real) (length : Nat)
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon <= 1 / 64)
    (hlength : 1 <= length) {index : SectionSixFirstStrictIndex}
    (hIndex : index ∈ sectionSixFirstStrictIndices epsilon length) :
    ∃! piece : SectionSixFirstPairPiece,
      sectionSixFirstPairMem epsilon length piece index := by
  classical
  have ho := sectionSixFirst_horder hepsilon hepsilonSmall hlength
  have hlowOrHigh : index ∈ sectionSixFirstLowStrictIndices epsilon length ∨
      index ∈ sectionSixFirstHighStrictIndices epsilon length := by
    simpa [sectionSixFirstStrictIndices] using hIndex
  let X : Real := ((10 ^ length : Nat) : Real)
  let z1 : Real := sectionSixZOne epsilon X
  let z2 : Real := sectionSixZTwo epsilon X
  let z3 : Real := sectionSixZThree epsilon X
  let z5 : Real := sectionSixZFive epsilon X
  let z6 : Real := sectionSixZSix epsilon X
  let product : Real := (sectionSixFirstPairProduct index : Real)
  let squareProduct : Real :=
    (sectionSixFirstPairSquareProduct index : Real)
  have ho23 : z2 < z3 := by simpa [z2, z3, X] using ho.2.1
  have ho35 : z3 < z5 := by
    simpa [z3, z5, X] using ho.2.2.1.trans ho.2.2.2.1
  have ho56 : z5 < z6 := by simpa [z5, z6, X] using ho.2.2.2.2
  have ho23' : sectionSixZTwo epsilon ((10 ^ length : Nat) : Real) <
      sectionSixZThree epsilon ((10 ^ length : Nat) : Real) :=
    by simpa [z2, z3, X] using ho23
  have ho35' : sectionSixZThree epsilon ((10 ^ length : Nat) : Real) <
      sectionSixZFive epsilon ((10 ^ length : Nat) : Real) :=
    by simpa [z3, z5, X] using ho35
  have ho56' : sectionSixZFive epsilon ((10 ^ length : Nat) : Real) <
      sectionSixZSix epsilon ((10 ^ length : Nat) : Real) :=
    by simpa [z5, z6, X] using ho56
  have hpiece : ∃ piece, sectionSixFirstPairMem epsilon length piece index := by
    rcases hlowOrHigh with hLow | hHigh
    · by_cases h12 : product < z2
      · have h1 := sectionSixFirst_index_product_gt_z1_of_low
          hLow
        exact ⟨.lowBelow, by
          simpa [sectionSixFirstPairMem, X, z1, z2, product] using
            And.intro hLow (And.intro h1 h12)⟩
      have h2 : z2 <= product := le_of_not_gt h12
      by_cases h23 : product <= z3
      · exact ⟨.lowBandFirst, by simpa [sectionSixFirstPairMem, X, z2, z3, product] using And.intro hLow (And.intro h2 h23)⟩
      have h3 : z3 < product := lt_of_not_ge h23
      by_cases h35 : product < z5
      · by_cases hs : z6 <= squareProduct
        · exact ⟨.lowCentralLarge, by simpa [sectionSixFirstPairMem, X, z3, z5, z6, product, squareProduct] using And.intro hLow (And.intro h3 (And.intro h35 hs))⟩
        · exact ⟨.lowCentralSmall, by simpa [sectionSixFirstPairMem, X, z3, z5, z6, product, squareProduct] using And.intro hLow (And.intro h3 (And.intro h35 (lt_of_not_ge hs)))⟩
      have h5 : z5 <= product := le_of_not_gt h35
      by_cases h56 : product <= z6
      · exact ⟨.lowBandSecond, by simpa [sectionSixFirstPairMem, X, z5, z6, product] using And.intro hLow (And.intro h5 h56)⟩
      · exact ⟨.lowFar, by simpa [sectionSixFirstPairMem, X, z6, product] using And.intro hLow (lt_of_not_ge h56)⟩
    · have h3 : z3 < product := by
        exact sectionSixFirst_index_product_gt_z3_low_or_high
          hHigh
      by_cases h35 : product < z5
      · by_cases hs : z6 <= squareProduct
        · exact ⟨.highCentralLarge, by simpa [sectionSixFirstPairMem, X, z3, z5, z6, product, squareProduct] using And.intro hHigh (And.intro h3 (And.intro h35 hs))⟩
        · exact ⟨.highCentralSmall, by simpa [sectionSixFirstPairMem, X, z3, z5, z6, product, squareProduct] using And.intro hHigh (And.intro h3 (And.intro h35 (lt_of_not_ge hs)))⟩
      have h5 : z5 <= product := le_of_not_gt h35
      by_cases h56 : product <= z6
      · exact ⟨.highBandSecond, by simpa [sectionSixFirstPairMem, X, z5, z6, product] using And.intro hHigh (And.intro h5 h56)⟩
      · exact ⟨.highFar, by simpa [sectionSixFirstPairMem, X, z6, product] using And.intro hHigh (lt_of_not_ge h56)⟩
  rcases hpiece with ⟨piece, hpiece⟩
  refine ⟨piece, hpiece, ?_⟩
  intro piece' hpiece'
  cases piece <;> cases piece' <;>
    simp only [sectionSixFirstPairMem] at hpiece hpiece' ⊢ <;>
    try { linarith [ho23', ho35', ho56'] } <;>
    try { exfalso; exact (sectionSixFirst_low_high_disjoint
      hepsilon hepsilonSmall hlength hpiece.1 hpiece'.1) } <;>
    try { exfalso; exact (sectionSixFirst_low_high_disjoint
      hepsilon hepsilonSmall hlength hpiece'.1 hpiece.1) }

end

end PrimesRestrictedDigits
