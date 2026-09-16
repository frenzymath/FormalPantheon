import PrimesRestrictedDigits.BasicEstimates.CayleyLogUpper
import PrimesRestrictedDigits.BasicEstimates.UniformRealGrid
/-! # SectionSixFirstLowCentralLargeTerminalCertificateCells -/

open Set

namespace PrimesRestrictedDigits

noncomputable section

structure SectionSixFirstLowCentralLargeTerminalCertificateCell where
  uLower : Real
  uUpper : Real
  cellUpper : Real

def SectionSixFirstLowCentralLargeTerminalCertificateCell.region
    (cell : SectionSixFirstLowCentralLargeTerminalCertificateCell) : Set Real :=
  Icc cell.uLower cell.uUpper

def SectionSixFirstLowCentralLargeTerminalCertificateCell.weight
    (cell : SectionSixFirstLowCentralLargeTerminalCertificateCell) : Real :=
  (cell.uUpper - cell.uLower) * cell.cellUpper

def sectionSixFirstLowCentralLargeTerminalCertificateCell
    (index : Fin 2 × Fin 800) :
    SectionSixFirstLowCentralLargeTerminalCertificateCell :=
  let uStart : Real :=
    if index.1 = 0 then 319999 / 1500000 else 287501 / 1000000
  let uEnd : Real :=
    if index.1 = 0 then 287501 / 1000000 else 180001 / 500000
  let uLower := uniformRealGridLower uStart uEnd index.2
  let uUpper := uniformRealGridUpper uStart uEnd index.2
  let endpoint := if index.1 = 0 then uUpper else uLower
  let ratio : Real :=
    if index.1 = 0 then
      endpoint * (680001 / 500000 - endpoint) /
        ((319999 / 500000 - endpoint) * (1 - 2 * endpoint))
    else
      (287501 / 500000 - endpoint) *
          (680001 / 500000 - endpoint) /
        ((212499 / 500000) * (319999 / 500000 - endpoint))
  let cayley := (ratio - 1) / (ratio + 1)
  {
    uLower := uLower
    uUpper := uUpper
    cellUpper :=
      1 / (uLower * (1 - uLower)) * cayleyLogSeriesUpper cayley 5
  }

end

end PrimesRestrictedDigits
