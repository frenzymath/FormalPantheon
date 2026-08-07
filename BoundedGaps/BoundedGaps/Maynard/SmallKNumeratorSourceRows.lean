import BoundedGaps.Maynard.SmallKNumeratorGeneratedData
import BoundedGaps.Maynard.SmallKNumeratorBridge

/-!
# Chunked source encoding for the scaled small-k numerator

The 42 source rows are checked in six seven-row chunks so the kernel never
retains the complete expanded arithmetic certificate at once.
-/

namespace BoundedGaps.Maynard

def smallKNumeratorSourceEncodingRow (i : Fin 42) : ℤ :=
  ∑ cp : Fin 6,
    smallKIntegratedIntegerCoefficient i cp *
      smallKIntegratedGroupedCoefficientBase ^
        smallKExponentPairIndex (smallKIntegratedExponentPair (i, cp))

def smallKNumeratorSourceRowIndex (offset : ℕ) (i : Fin 7)
    (h : offset + 7 ≤ 42) : Fin 42 :=
  ⟨offset + i.1, by omega⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem smallK_numeratorSourceRows_0 (i : Fin 7) :
    smallKNumeratorSourceEncodingRow (smallKNumeratorSourceRowIndex 0 i (by omega)) =
      smallKNumeratorGeneratedSourceEncodingRowValues.getD i.1 0 := by
  fin_cases i <;>
    norm_num (config := { maxSteps := 1000000 })
      [smallKNumeratorSourceEncodingRow, smallKNumeratorSourceRowIndex,
        smallKIntegratedIntegerCoefficient, smallKIntegerCoefficient, Nat.choose,
        smallKCoefficient, smallKExponentB, smallKExponentC,
        smallKIntegratedExponentPair, smallKExponentPairIndex,
        smallKIntegratedGroupedCoefficientBase,
        smallKNumeratorGeneratedSourceEncodingRowValues, Fin.sum_univ_succ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem smallK_numeratorSourceRows_7 (i : Fin 7) :
    smallKNumeratorSourceEncodingRow (smallKNumeratorSourceRowIndex 7 i (by omega)) =
      smallKNumeratorGeneratedSourceEncodingRowValues.getD (7 + i.1) 0 := by
  fin_cases i <;>
    norm_num (config := { maxSteps := 1000000 })
      [smallKNumeratorSourceEncodingRow, smallKNumeratorSourceRowIndex,
        smallKIntegratedIntegerCoefficient, smallKIntegerCoefficient, Nat.choose,
        smallKCoefficient, smallKExponentB, smallKExponentC,
        smallKIntegratedExponentPair, smallKExponentPairIndex,
        smallKIntegratedGroupedCoefficientBase,
        smallKNumeratorGeneratedSourceEncodingRowValues, Fin.sum_univ_succ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem smallK_numeratorSourceRows_14 (i : Fin 7) :
    smallKNumeratorSourceEncodingRow (smallKNumeratorSourceRowIndex 14 i (by omega)) =
      smallKNumeratorGeneratedSourceEncodingRowValues.getD (14 + i.1) 0 := by
  fin_cases i <;>
    norm_num (config := { maxSteps := 1000000 })
      [smallKNumeratorSourceEncodingRow, smallKNumeratorSourceRowIndex,
        smallKIntegratedIntegerCoefficient, smallKIntegerCoefficient, Nat.choose,
        smallKCoefficient, smallKExponentB, smallKExponentC,
        smallKIntegratedExponentPair, smallKExponentPairIndex,
        smallKIntegratedGroupedCoefficientBase,
        smallKNumeratorGeneratedSourceEncodingRowValues, Fin.sum_univ_succ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem smallK_numeratorSourceRows_21 (i : Fin 7) :
    smallKNumeratorSourceEncodingRow (smallKNumeratorSourceRowIndex 21 i (by omega)) =
      smallKNumeratorGeneratedSourceEncodingRowValues.getD (21 + i.1) 0 := by
  fin_cases i <;>
    norm_num (config := { maxSteps := 1000000 })
      [smallKNumeratorSourceEncodingRow, smallKNumeratorSourceRowIndex,
        smallKIntegratedIntegerCoefficient, smallKIntegerCoefficient, Nat.choose,
        smallKCoefficient, smallKExponentB, smallKExponentC,
        smallKIntegratedExponentPair, smallKExponentPairIndex,
        smallKIntegratedGroupedCoefficientBase,
        smallKNumeratorGeneratedSourceEncodingRowValues, Fin.sum_univ_succ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem smallK_numeratorSourceRows_28 (i : Fin 7) :
    smallKNumeratorSourceEncodingRow (smallKNumeratorSourceRowIndex 28 i (by omega)) =
      smallKNumeratorGeneratedSourceEncodingRowValues.getD (28 + i.1) 0 := by
  fin_cases i <;>
    norm_num (config := { maxSteps := 1000000 })
      [smallKNumeratorSourceEncodingRow, smallKNumeratorSourceRowIndex,
        smallKIntegratedIntegerCoefficient, smallKIntegerCoefficient, Nat.choose,
        smallKCoefficient, smallKExponentB, smallKExponentC,
        smallKIntegratedExponentPair, smallKExponentPairIndex,
        smallKIntegratedGroupedCoefficientBase,
        smallKNumeratorGeneratedSourceEncodingRowValues, Fin.sum_univ_succ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem smallK_numeratorSourceRows_35 (i : Fin 7) :
    smallKNumeratorSourceEncodingRow (smallKNumeratorSourceRowIndex 35 i (by omega)) =
      smallKNumeratorGeneratedSourceEncodingRowValues.getD (35 + i.1) 0 := by
  fin_cases i <;>
    norm_num (config := { maxSteps := 1000000 })
      [smallKNumeratorSourceEncodingRow, smallKNumeratorSourceRowIndex,
        smallKIntegratedIntegerCoefficient, smallKIntegerCoefficient, Nat.choose,
        smallKCoefficient, smallKExponentB, smallKExponentC,
        smallKIntegratedExponentPair, smallKExponentPairIndex,
        smallKIntegratedGroupedCoefficientBase,
        smallKNumeratorGeneratedSourceEncodingRowValues, Fin.sum_univ_succ]

end BoundedGaps.Maynard
