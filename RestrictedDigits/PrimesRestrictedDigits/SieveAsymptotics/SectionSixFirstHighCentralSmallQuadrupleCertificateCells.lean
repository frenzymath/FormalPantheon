import PrimesRestrictedDigits.BasicEstimates.CayleyLogUpper
import PrimesRestrictedDigits.BasicEstimates.UniformRealGrid
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
/-! # SectionSixFirstHighCentralSmallQuadrupleCertificateCells -/

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-!
# Directed cells for the high-central-small `I9` outer replay

The cells are the 2048 uniform `u` intervals (`Fin 32` shards of `Fin 64`
cells).  The payload is the tail-envelope `D` times the closed-fiber endpoint
majorant.  The separate manifest adds the exact `M-D` middle-box correction.
-/

structure SectionSixFirstHighCentralSmallQuadrupleCertificateCell where
  uLower : Real
  uUpper : Real
  cellUpper : Real

def SectionSixFirstHighCentralSmallQuadrupleCertificateCell.region
    (cell : SectionSixFirstHighCentralSmallQuadrupleCertificateCell) : Set Real :=
  Icc cell.uLower cell.uUpper

def SectionSixFirstHighCentralSmallQuadrupleCertificateCell.weight
    (cell : SectionSixFirstHighCentralSmallQuadrupleCertificateCell) : Real :=
  (cell.uUpper - cell.uLower) * cell.cellUpper

def sectionSixFirstHighCentralSmallQuadrupleCertificateDelta : Real :=
  1 / 1000000000

def sectionSixFirstHighCentralSmallQuadrupleCertificateBeta : Real :=
  212499999 / 500000000

def sectionSixFirstHighCentralSmallQuadrupleCertificateGap : Real :=
  16249999 / 250000000

def sectionSixFirstHighCentralSmallQuadrupleCertificateC : Real := 16 / 25

def sectionSixFirstHighCentralSmallQuadrupleCertificateTail : Real :=
  564383 / 1000000

def sectionSixFirstHighCentralSmallQuadrupleCertificateMiddle : Real :=
  70893 / 125000

def sectionSixFirstHighCentralSmallQuadrupleCertificateLogLower
    (q : Real) : Real :=
  2 * ∑ i ∈ Finset.range 10,
    (((q - 1) / (q + 1)) ^ (2 * i + 1) / (2 * i + 1))

def sectionSixFirstHighCentralSmallQuadrupleCertificateLogUpper
    (q : Real) : Real :=
  cayleyLogSeriesUpper ((q - 1) / (q + 1)) 10

def sectionSixFirstHighCentralSmallQuadrupleCertificateCell
    (index : Fin 32 × Fin 64) :
      SectionSixFirstHighCentralSmallQuadrupleCertificateCell :=
  let flat : Fin 2048 := finProdFinEquiv index
  let uLower := uniformRealGridLower
    sectionSixFirstHighCentralSmallQuadrupleCertificateBeta (1 / 2) flat
  let uUpper := uniformRealGridUpper
    sectionSixFirstHighCentralSmallQuadrupleCertificateBeta (1 / 2) flat
  let endpoint :=
    (sectionSixFirstHighCentralSmallQuadrupleCertificateC - uLower) / 2
  let ratio := endpoint /
    sectionSixFirstHighCentralSmallQuadrupleCertificateGap
  let lower :=
    sectionSixFirstHighCentralSmallQuadrupleCertificateLogLower ratio
  let upper :=
    sectionSixFirstHighCentralSmallQuadrupleCertificateLogUpper ratio
  let fiberUpper :=
    upper ^ 2 /
        (2 * sectionSixFirstHighCentralSmallQuadrupleCertificateGap) +
      1 / sectionSixFirstHighCentralSmallQuadrupleCertificateGap -
      1 / endpoint - lower /
        sectionSixFirstHighCentralSmallQuadrupleCertificateGap
  {
    uLower := uLower
    uUpper := uUpper
    cellUpper := sectionSixFirstHighCentralSmallQuadrupleCertificateTail *
      fiberUpper / uLower
  }

theorem highCentralSmallCertificateCell_bounds
    (index : Fin 32 × Fin 64) :
    let cell := sectionSixFirstHighCentralSmallQuadrupleCertificateCell index
    cell.uLower ≤ cell.uUpper ∧ 0 < cell.uLower ∧
      cell.uUpper ≤ (1 / 2 : Real) := by
  have h := uniformRealGrid_bounds (n := 2048)
    (a := sectionSixFirstHighCentralSmallQuadrupleCertificateBeta)
    (b := (1 / 2 : Real)) (by norm_num) (by
      norm_num [sectionSixFirstHighCentralSmallQuadrupleCertificateBeta])
      (finProdFinEquiv index)
  simpa [sectionSixFirstHighCentralSmallQuadrupleCertificateCell] using
    (show uniformRealGridLower
          sectionSixFirstHighCentralSmallQuadrupleCertificateBeta (1 / 2)
          (finProdFinEquiv index) ≤
        uniformRealGridUpper
          sectionSixFirstHighCentralSmallQuadrupleCertificateBeta (1 / 2)
          (finProdFinEquiv index) ∧
      0 < uniformRealGridLower
          sectionSixFirstHighCentralSmallQuadrupleCertificateBeta (1 / 2)
          (finProdFinEquiv index) ∧
      uniformRealGridUpper
          sectionSixFirstHighCentralSmallQuadrupleCertificateBeta (1 / 2)
          (finProdFinEquiv index) ≤ (1 / 2 : Real) by
      have hbeta : 0 <
          sectionSixFirstHighCentralSmallQuadrupleCertificateBeta := by
        norm_num [sectionSixFirstHighCentralSmallQuadrupleCertificateBeta]
      exact ⟨h.2.1, hbeta.trans_le h.1, h.2.2⟩)

theorem highCentralSmallCertificateCell_measure_mul_upper_eq_weight
    (index : Fin 32 × Fin 64) :
    volume.real
          (sectionSixFirstHighCentralSmallQuadrupleCertificateCell index).region *
        (sectionSixFirstHighCentralSmallQuadrupleCertificateCell index).cellUpper =
      (sectionSixFirstHighCentralSmallQuadrupleCertificateCell index).weight := by
  let cell := sectionSixFirstHighCentralSmallQuadrupleCertificateCell index
  have h := highCentralSmallCertificateCell_bounds index
  change volume.real (Icc cell.uLower cell.uUpper) * cell.cellUpper =
    (cell.uUpper - cell.uLower) * cell.cellUpper
  rw [Real.volume_real_Icc_of_le h.1]

end
end PrimesRestrictedDigits
