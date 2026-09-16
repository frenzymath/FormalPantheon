import PrimesRestrictedDigits.BasicEstimates.CayleyLogUpper
import PrimesRestrictedDigits.BasicEstimates.UniformRealGrid
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstHighFarFiberReduction
/-! # SectionSixFirstHighFarCertificateCells -/

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

structure SectionSixFirstHighFarCertificateCell where
  uLower : Real
  uUpper : Real
  cellUpper : Real

def SectionSixFirstHighFarCertificateCell.region
    (cell : SectionSixFirstHighFarCertificateCell) : Set Real :=
  Icc cell.uLower cell.uUpper

def SectionSixFirstHighFarCertificateCell.weight
    (cell : SectionSixFirstHighFarCertificateCell) : Real :=
  (cell.uUpper - cell.uLower) * cell.cellUpper

def sectionSixFirstHighFarCertificateCell
    (index : Fin 2 × Fin 160) : SectionSixFirstHighFarCertificateCell :=
  let uStart : Real :=
    if index.1 = 0 then 212499 / 500000 else 459997 / 1000000
  let uEnd : Real :=
    if index.1 = 0 then 459997 / 1000000 else 1 / 2
  let uLower := uniformRealGridLower uStart uEnd index.2
  let uUpper := uniformRealGridUpper uStart uEnd index.2
  let endpoint := if index.1 = 0 then uUpper else uLower
  let prefactor := 1 / (uLower * (1 - uLower))
  let ratio := (180001 / 500000 : Real) /
    (319999 / 500000 - endpoint)
  let cayley := (ratio - 1) / (ratio + 1)
  let logTwoUpper := cayleyLogSeriesUpper (1 / 3 : Real) 5
  let tail := (564663 / 1000000 : Real) *
    (1 + 2 * uUpper - 3 * (319999 / 500000)) /
      (uLower * (319999 / 500000 - uUpper) * (1 - uUpper))
  {
    uLower := uLower
    uUpper := uUpper
    cellUpper := if index.1 = 0 then
      prefactor * cayleyLogSeriesUpper cayley 5
      else prefactor * logTwoUpper + tail
  }

theorem highFarCertificateCell_bounds (index : Fin 2 × Fin 160) :
    let cell := sectionSixFirstHighFarCertificateCell index
    cell.uLower ≤ cell.uUpper ∧ 0 < cell.uLower ∧
      cell.uUpper ≤ (1 / 2 : Real) := by
  rcases index with ⟨branch, i⟩
  fin_cases branch
  · have h := uniformRealGrid_bounds (n := 160)
      (a := (212499 : Real) / 500000) (b := 459997 / 1000000)
      (by norm_num) (by norm_num) i
    simpa [sectionSixFirstHighFarCertificateCell] using
      (show uniformRealGridLower _ _ i ≤ uniformRealGridUpper _ _ i ∧
        0 < uniformRealGridLower _ _ i ∧
        uniformRealGridUpper _ _ i ≤ (1 / 2 : Real) by
        exact ⟨h.2.1, by linarith [h.1], by linarith [h.2.2]⟩)
  · have h := uniformRealGrid_bounds (n := 160)
      (a := (459997 : Real) / 1000000) (b := 1 / 2)
      (by norm_num) (by norm_num) i
    simpa [sectionSixFirstHighFarCertificateCell] using
      (show uniformRealGridLower _ _ i ≤ uniformRealGridUpper _ _ i ∧
        0 < uniformRealGridLower _ _ i ∧
        uniformRealGridUpper _ _ i ≤ (1 / 2 : Real) by
        exact ⟨by simpa [one_div] using h.2.1,
          by linarith [h.1], by simpa [one_div] using h.2.2⟩)

theorem highFarCertificateCell_measure_mul_upper_eq_weight
    (index : Fin 2 × Fin 160) :
    volume.real (sectionSixFirstHighFarCertificateCell index).region *
        (sectionSixFirstHighFarCertificateCell index).cellUpper =
      (sectionSixFirstHighFarCertificateCell index).weight := by
  let cell := sectionSixFirstHighFarCertificateCell index
  have h := highFarCertificateCell_bounds index
  change volume.real (Icc cell.uLower cell.uUpper) * cell.cellUpper =
    (cell.uUpper - cell.uLower) * cell.cellUpper
  rw [Real.volume_real_Icc_of_le h.1]

end
end PrimesRestrictedDigits
