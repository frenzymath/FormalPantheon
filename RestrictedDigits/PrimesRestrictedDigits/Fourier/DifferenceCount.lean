import PrimesRestrictedDigits.Fourier.DecimalEndpointPhase
import PrimesRestrictedDigits.Fourier.RationalCosineCertificate
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Signed digit-difference counts

The allowed double sum is regrouped exactly by the signed difference. This
reduces later rational phase-sum certificates to nineteen terms.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

def signedDifference (k : Fin 19) : ℤ := (k : ℤ) - 9

def signedDifferenceCountTable : Fin 10 → Fin 19 → ℕ :=
  ![
    ![0,1,2,3,4,5,6,7,8,9,8,7,6,5,4,3,2,1,0],
    ![1,1,2,3,4,5,6,7,7,9,7,7,6,5,4,3,2,1,1],
    ![1,2,2,3,4,5,6,6,7,9,7,6,6,5,4,3,2,2,1],
    ![1,2,3,3,4,5,5,6,7,9,7,6,5,5,4,3,3,2,1],
    ![1,2,3,4,4,4,5,6,7,9,7,6,5,4,4,4,3,2,1],
    ![1,2,3,4,4,4,5,6,7,9,7,6,5,4,4,4,3,2,1],
    ![1,2,3,3,4,5,5,6,7,9,7,6,5,5,4,3,3,2,1],
    ![1,2,2,3,4,5,6,6,7,9,7,6,6,5,4,3,2,2,1],
    ![1,1,2,3,4,5,6,7,7,9,7,7,6,5,4,3,2,1,1],
    ![0,1,2,3,4,5,6,7,8,9,8,7,6,5,4,3,2,1,0]
  ]

theorem signedDifferenceCountTable_sum (a : Fin 10) (F : ℤ → ℝ) :
    (∑ d ∈ allowedDecimalDigits a, ∑ e ∈ allowedDecimalDigits a,
      F ((e : ℤ) - (d : ℤ))) =
      ∑ k : Fin 19, (signedDifferenceCountTable a k : ℝ) * F (signedDifference k) := by
  fin_cases a <;>
    norm_num [allowedDecimalDigits, Finset.sum_filter, Finset.sum_range_succ,
      signedDifferenceCountTable, signedDifference, Fin.sum_univ_succ]
  all_goals ring

noncomputable def signedDifferencePhaseTerm (window : Fin 5 → Fin 10) (offset : ℤ)
    (k : Fin 19) : ℝ :=
  rationalCosineUpper20D20
    (centeredRationalPart
      (signedDifference k * (digitWindowNumeratorFour window + offset)) 100000)

theorem windowPhaseCosineSum_eq_signedDifferenceTable
    (a : Fin 10) (window : Fin 5 → Fin 10) (offset : ℤ) :
    (∑ d ∈ allowedDecimalDigits a, ∑ e ∈ allowedDecimalDigits a,
      rationalCosineUpper20D20 (windowPhase window offset d e)) =
      ∑ k : Fin 19, (signedDifferenceCountTable a k : ℝ) *
        signedDifferencePhaseTerm window offset k := by
  simpa [windowPhase, signedDifferencePhaseTerm, signedDifference] using
    (signedDifferenceCountTable_sum a
      (fun n => rationalCosineUpper20D20
        (centeredRationalPart (n *
          (digitWindowNumeratorFour window + offset)) 100000)))

end PrimesRestrictedDigits
