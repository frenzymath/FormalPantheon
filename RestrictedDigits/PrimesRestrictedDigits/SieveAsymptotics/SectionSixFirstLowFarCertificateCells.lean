import PrimesRestrictedDigits.BasicEstimates.UniformRealGrid
/-! # SectionSixFirstLowFarCertificateCells -/

open Set

namespace PrimesRestrictedDigits

noncomputable section

structure SectionSixFirstLowFarCertificateCell where
  vLower : Real
  vUpper : Real
  uLower : Real
  uUpper : Real
  cellUpper : Real

def SectionSixFirstLowFarCertificateCell.region
    (cell : SectionSixFirstLowFarCertificateCell) : Set (Real × Real) :=
  Icc cell.vLower cell.vUpper ×ˢ Icc cell.uLower cell.uUpper

def SectionSixFirstLowFarCertificateCell.weight
    (cell : SectionSixFirstLowFarCertificateCell) : Real :=
  (cell.vUpper - cell.vLower) *
    (cell.uUpper - cell.uLower) * cell.cellUpper

def sectionSixFirstLowFarCertificateCell
    (index : Fin 2 × Fin 60 × Fin 5) :
    SectionSixFirstLowFarCertificateCell :=
  let vStart : Real :=
    if index.1 = 0 then 69999 / 250000 else 319999 / 1000000
  let vEnd : Real :=
    if index.1 = 0 then 319999 / 1000000 else 1 / 3
  let vLower := uniformRealGridLower vStart vEnd index.2.1
  let vUpper := uniformRealGridUpper vStart vEnd index.2.1
  let uStart : Real :=
    if index.1 = 0 then 1 - 180001 / 500000 - vUpper else vLower
  let uEnd : Real :=
    if index.1 = 0 then 180001 / 500000 else 1 - 2 * vLower
  let uLower := uniformRealGridLower uStart uEnd index.2.2
  let uUpper := uniformRealGridUpper uStart uEnd index.2.2
  {
    vLower := vLower
    vUpper := vUpper
    uLower := uLower
    uUpper := uUpper
    cellUpper := 1 / (uLower * vLower * (1 - uUpper - vUpper))
  }

end

end PrimesRestrictedDigits
