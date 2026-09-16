import PrimesRestrictedDigits.Fourier.CertificateData.Moment235RowsDigit0
import PrimesRestrictedDigits.Fourier.CertificateData.Moment235RowsDigit1
import PrimesRestrictedDigits.Fourier.CertificateData.Moment235RowsDigit2
import PrimesRestrictedDigits.Fourier.CertificateData.Moment235RowsDigit3
import PrimesRestrictedDigits.Fourier.CertificateData.Moment235RowsDigit4
import PrimesRestrictedDigits.Fourier.Moment235CertificateStateBridge

/-!
# Kernel-checked rows for all five representative digits

These rows discharge the numerical certificate, the repaired exact form of
`MAYNARD-PRD-PUBLISHED`, Lemma 10.2, pp. 170--173.

Exact row reflection extends the lower-half bounds to each complete decimal
state space for the five representative digits.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

private theorem finFiveCases {predicate : Fin 5 -> Prop}
    (h0 : predicate 0) (h1 : predicate 1) (h2 : predicate 2)
    (h3 : predicate 3) (h4 : predicate 4)
    (index : Fin 5) : predicate index := by
  exact Fin.cases h0 (fun i => Fin.cases h1 (fun j =>
    Fin.cases h2 (fun k => Fin.cases h3 (fun l =>
      Fin.cases h4 (fun m => Fin.elim0 m) l) k) j) i) index

/-- Every indexed row for each of the five representative excluded digits. -/
theorem moment235IndexedRows (a : Fin 5) :
    forall future : Fin 10000, moment235IndexedRow a future :=
  finFiveCases
    (predicate := fun digit : Fin 5 =>
      forall future : Fin 10000, moment235IndexedRow digit future)
    moment235RowsDigit0 moment235RowsDigit1 moment235RowsDigit2
    moment235RowsDigit3 moment235RowsDigit4 a

/-- The five kernel-checked indexed row families transported to tuple states. -/
theorem moment235StateRows (a : Fin 5) :
    forall future : DigitWindowState 4,
      moment235CertificateGrowthDenominator *
          (∑ first : Fin 10,
            moment235WindowPoweredNumerator a
                (prependDigitWindow first future) *
              moment235StateVectorNumerator a
                (digitWindowPrefix (prependDigitWindow first future))) <=
        moment235CertificateDenominator *
          moment235CertificateGrowthNumerator *
            moment235StateVectorNumerator a future :=
  moment235StateRows_of_indexedRows a (moment235IndexedRows a)

end PrimesRestrictedDigits
