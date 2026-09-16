import PrimesRestrictedDigits.ExceptionalMinorArcs.LinePrimitiveHeightClasses
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# Canonical normalized second-moment data

This repackages one primitive-height witness pair from `MAYNARD-PRD-PUBLISHED`, Lemma 15.2,
pp. 210--212, as the corrected complete `N_3` tuple. The defective normalized equations in the
source are not used.
-/

namespace PrimesRestrictedDigits

/-- The complete source-ordered normalized tuple attached to two relations. -/
structure LineNormalizedSecondMomentData (X : Nat) where
  /-- Second member of the unprimed relation. -/
  a2 : Fin X
  /-- Second member of the primed relation. -/
  a2Prime : Fin X
  /-- Common first member of both relations. -/
  a1 : Fin X
  /-- Positive gcd of the two raw first coefficients. -/
  d : Nat
  /-- Unprimed signed primitive first coefficient. -/
  u : Int
  /-- Primed signed primitive first coefficient. -/
  uPrime : Int
  /-- Unprimed second coefficient. -/
  v2 : Int
  /-- Unprimed scale coefficient. -/
  v3 : Int
  /-- Unprimed constant coefficient. -/
  v4 : Int
  /-- Primed second coefficient. -/
  v2Prime : Int
  /-- Primed scale coefficient. -/
  v3Prime : Int
  /-- Primed constant coefficient. -/
  v4Prime : Int
  deriving DecidableEq

namespace LineNormalizedSecondMomentData

/-- Sup height of the two signed primitive first coefficients. -/
def primitiveHeight {X : Nat}
    (data : LineNormalizedSecondMomentData X) : Nat :=
  max data.u.natAbs data.uPrime.natAbs

/-- Exact source-facing properties inherited by a normalized witness pair. -/
structure IsValid {X : Nat} (C D : Finset (Fin X)) (V : Real)
    (data : LineNormalizedSecondMomentData X) : Prop where
  a2_mem : data.a2 ∈ D
  a2Prime_mem : data.a2Prime ∈ D
  a1_mem : data.a1 ∈ C
  a2_pos : 0 < data.a2.val
  a2Prime_pos : 0 < data.a2Prime.val
  a1_pos : 0 < data.a1.val
  d_pos : 0 < data.d
  u_ne : data.u ≠ 0
  uPrime_ne : data.uPrime ≠ 0
  primitive_gcd : Int.gcd data.u data.uPrime = 1
  canonical_gcd :
    Int.gcd ((data.d : Int) * data.u)
      ((data.d : Int) * data.uPrime) = data.d
  v2_ne : data.v2 ≠ 0
  v3_ne : data.v3 ≠ 0
  v4_ne : data.v4 ≠ 0
  v2Prime_ne : data.v2Prime ≠ 0
  v3Prime_ne : data.v3Prime ≠ 0
  v4Prime_ne : data.v4Prime ≠ 0
  u_abs_le : abs ((data.u : Int) : Real) ≤ V
  uPrime_abs_le : abs ((data.uPrime : Int) : Real) ≤ V
  first_abs_le : abs (((data.d : Int) * data.u : Int) : Real) ≤ V
  firstPrime_abs_le :
    abs (((data.d : Int) * data.uPrime : Int) : Real) ≤ V
  v2_abs_le : abs ((data.v2 : Int) : Real) ≤ V
  v3_abs_le : abs ((data.v3 : Int) : Real) ≤ V
  v4_abs_le : abs ((data.v4 : Int) : Real) ≤ V
  v2Prime_abs_le : abs ((data.v2Prime : Int) : Real) ≤ V
  v3Prime_abs_le : abs ((data.v3Prime : Int) : Real) ≤ V
  v4Prime_abs_le : abs ((data.v4Prime : Int) : Real) ≤ V
  relation :
    (data.d : Int) * data.u * (data.a1.val : Int) +
      data.v2 * (data.a2.val : Int) +
      data.v3 * (X : Int) + data.v4 = 0
  relationPrime :
    (data.d : Int) * data.uPrime * (data.a1.val : Int) +
      data.v2Prime * (data.a2Prime.val : Int) +
      data.v3Prime * (X : Int) + data.v4Prime = 0

/-- Exchange all primed and unprimed fields, retaining the common data. -/
def swap {X : Nat} (data : LineNormalizedSecondMomentData X) :
    LineNormalizedSecondMomentData X :=
  { a2 := data.a2Prime
    a2Prime := data.a2
    a1 := data.a1
    d := data.d
    u := data.uPrime
    uPrime := data.u
    v2 := data.v2Prime
    v3 := data.v3Prime
    v4 := data.v4Prime
    v2Prime := data.v2
    v3Prime := data.v3
    v4Prime := data.v4 }

@[simp]
theorem swap_swap {X : Nat} (data : LineNormalizedSecondMomentData X) :
    data.swap.swap = data := by
  cases data
  rfl

@[simp]
theorem primitiveHeight_swap {X : Nat}
    (data : LineNormalizedSecondMomentData X) :
    data.swap.primitiveHeight = data.primitiveHeight := by
  simp [primitiveHeight, swap, max_comm]

/-- The corrected divisor target has a negative right side and no extra `X`. -/
theorem IsValid.first_divisor_target
    {X : Nat} {C D : Finset (Fin X)} {V : Real}
    {data : LineNormalizedSecondMomentData X}
    (hdata : data.IsValid C D V) :
    (data.d : Int) * data.u * (data.a1.val : Int) =
      -(data.v2 * (data.a2.val : Int) +
        data.v3 * (X : Int) + data.v4) := by
  linear_combination hdata.relation

/-- The primed corrected divisor target. -/
theorem IsValid.second_divisor_target
    {X : Nat} {C D : Finset (Fin X)} {V : Real}
    {data : LineNormalizedSecondMomentData X}
    (hdata : data.IsValid C D V) :
    (data.d : Int) * data.uPrime * (data.a1.val : Int) =
      -(data.v2Prime * (data.a2Prime.val : Int) +
        data.v3Prime * (X : Int) + data.v4Prime) := by
  linear_combination hdata.relationPrime

end LineNormalizedSecondMomentData

/-- Normalize a pair by its positive gcd and signed canonical quotients. -/
def lineNormalizedSecondMomentDataOfPair {X : Nat}
    (pair : LowHeightPlaneWitness X × LowHeightPlaneWitness X) :
    LineNormalizedSecondMomentData X :=
  let primitive := linePrimitiveFirstCoefficients
    (pair.1.v 0) (pair.2.v 0)
  { a2 := pair.1.a2
    a2Prime := pair.2.a2
    a1 := pair.1.a1
    d := Int.gcd (pair.1.v 0) (pair.2.v 0)
    u := primitive.1
    uPrime := primitive.2
    v2 := pair.1.v 1
    v3 := pair.1.v 2
    v4 := pair.1.v4
    v2Prime := pair.2.v 1
    v3Prime := pair.2.v 2
    v4Prime := pair.2.v4 }

/-- Rebuild the ordered witness pair encoded by a normalized tuple. -/
def lineNormalizedSecondMomentDataToPair {X : Nat}
    (data : LineNormalizedSecondMomentData X) :
    LowHeightPlaneWitness X × LowHeightPlaneWitness X :=
  ({ a1 := data.a1
     a2 := data.a2
     v := ![(data.d : Int) * data.u, data.v2, data.v3]
     v4 := data.v4 },
   { a1 := data.a1
     a2 := data.a2Prime
     v := ![(data.d : Int) * data.uPrime, data.v2Prime, data.v3Prime]
     v4 := data.v4Prime })

@[simp]
theorem LineNormalizedSecondMomentData.primitiveHeight_ofPair
    {X : Nat}
    (pair : LowHeightPlaneWitness X × LowHeightPlaneWitness X) :
    (lineNormalizedSecondMomentDataOfPair pair).primitiveHeight =
      lineSecondMomentPrimitiveHeight pair :=
  rfl

/-- Reconstruction is a left inverse exactly on the shared-first domain. -/
theorem lineNormalizedSecondMomentDataToPair_ofPair
    {X : Nat}
    {pair : LowHeightPlaneWitness X × LowHeightPlaneWitness X}
    (ha1 : pair.1.a1 = pair.2.a1) :
    lineNormalizedSecondMomentDataToPair
        (lineNormalizedSecondMomentDataOfPair pair) = pair := by
  apply Prod.ext
  · apply LowHeightPlaneWitness.ext
    · rfl
    · rfl
    · funext i
      fin_cases i
      · exact gcd_mul_linePrimitiveFirstCoefficients_fst
          (pair.1.v 0) (pair.2.v 0)
      · rfl
      · rfl
    · rfl
  · apply LowHeightPlaneWitness.ext
    · exact ha1
    · rfl
    · funext i
      fin_cases i
      · exact gcd_mul_linePrimitiveFirstCoefficients_snd
          (pair.1.v 0) (pair.2.v 0)
      · rfl
      · rfl
    · rfl

theorem lineNormalizedSecondMomentDataOfPair_injOn_sameFirst
    {X : Nat} :
    Set.InjOn lineNormalizedSecondMomentDataOfPair
      {pair : LowHeightPlaneWitness X × LowHeightPlaneWitness X |
        pair.1.a1 = pair.2.a1} := by
  intro pair hpair pair' hpair' heq
  calc
    pair = lineNormalizedSecondMomentDataToPair
        (lineNormalizedSecondMomentDataOfPair pair) :=
      (lineNormalizedSecondMomentDataToPair_ofPair hpair).symm
    _ = lineNormalizedSecondMomentDataToPair
        (lineNormalizedSecondMomentDataOfPair pair') := congrArg _ heq
    _ = pair' := lineNormalizedSecondMomentDataToPair_ofPair hpair'

theorem lineNormalizedSecondMomentDataOfPair_injOn_heightClass
    {length : Nat} {C D : Finset (Fin (10 ^ length))} {V : Real}
    {j : Fin (length + 1)} :
    Set.InjOn
      (lineNormalizedSecondMomentDataOfPair (X := 10 ^ length))
      ↑(linePrimitiveHeightWitnessClass length C D V j) := by
  intro pair hpair pair' hpair' heq
  apply lineNormalizedSecondMomentDataOfPair_injOn_sameFirst
  · exact (mem_lineSecondMomentWitnessPairs.mp
      (mem_linePrimitiveHeightWitnessClass.mp hpair).1).2.2.1
  · exact (mem_lineSecondMomentWitnessPairs.mp
      (mem_linePrimitiveHeightWitnessClass.mp hpair').1).2.2.1
  · exact heq

/-- Normalization commutes with swap on the shared-first domain. -/
theorem lineNormalizedSecondMomentDataOfPair_swap
    {X : Nat}
    (pair : LowHeightPlaneWitness X × LowHeightPlaneWitness X)
    (ha1 : pair.1.a1 = pair.2.a1) :
    lineNormalizedSecondMomentDataOfPair pair.swap =
      (lineNormalizedSecondMomentDataOfPair pair).swap := by
  rcases pair with ⟨w, w'⟩
  rcases w with ⟨a1, a2, v, v4⟩
  rcases w' with ⟨a1', a2', v', v4'⟩
  have ha1Fields : a1 = a1' := by
    simpa using ha1
  simp [lineNormalizedSecondMomentDataOfPair,
    LineNormalizedSecondMomentData.swap,
    linePrimitiveFirstCoefficients, Int.gcd_comm, ha1Fields]

@[simp]
theorem lineSecondMomentPrimitiveHeight_swap
    {X : Nat}
    (pair : LowHeightPlaneWitness X × LowHeightPlaneWitness X) :
    lineSecondMomentPrimitiveHeight pair.swap =
      lineSecondMomentPrimitiveHeight pair := by
  simp [lineSecondMomentPrimitiveHeight,
    linePrimitiveFirstCoefficientHeight, linePrimitiveFirstCoefficients,
    Int.gcd_comm, max_comm]

theorem linePrimitiveHeightWitnessClass_swap_mem
    {length : Nat} {C D : Finset (Fin (10 ^ length))} {V : Real}
    {j : Fin (length + 1)}
    {pair : LowHeightPlaneWitness (10 ^ length) ×
      LowHeightPlaneWitness (10 ^ length)}
    (hpair : pair ∈ linePrimitiveHeightWitnessClass length C D V j) :
    pair.swap ∈ linePrimitiveHeightWitnessClass length C D V j := by
  have hp := mem_linePrimitiveHeightWitnessClass.mp hpair
  have hw := mem_lineSecondMomentWitnessPairs.mp hp.1
  apply mem_linePrimitiveHeightWitnessClass.mpr
  refine ⟨mem_lineSecondMomentWitnessPairs.mpr ?_, ?_⟩
  · exact ⟨hw.2.1, hw.1, hw.2.2.1.symm,
      hw.2.2.2.2, hw.2.2.2.1⟩
  · rw [lineSecondMomentPrimitiveHeight_swap]
    exact hp.2

theorem swap_mem_linePrimitiveHeightWitnessClass_iff
    {length : Nat} {C D : Finset (Fin (10 ^ length))} {V : Real}
    {j : Fin (length + 1)}
    {pair : LowHeightPlaneWitness (10 ^ length) ×
      LowHeightPlaneWitness (10 ^ length)} :
    pair.swap ∈ linePrimitiveHeightWitnessClass length C D V j ↔
      pair ∈ linePrimitiveHeightWitnessClass length C D V j := by
  constructor
  · intro hpair
    have := linePrimitiveHeightWitnessClass_swap_mem hpair
    simpa using this
  · exact linePrimitiveHeightWitnessClass_swap_mem

end PrimesRestrictedDigits
