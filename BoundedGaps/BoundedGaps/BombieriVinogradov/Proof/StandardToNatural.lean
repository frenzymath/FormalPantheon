import BoundedGaps.BombieriVinogradov.Analytic.WeightedPrimeLevel

/-!
# Standard weighted to natural Maynard interface

This wrapper is intentionally conditional: its only analytic input is the
public weighted proposition.  In particular it cannot see an unconditional
weighted theorem or any closed natural Bombieri--Vinogradov export.
-/

namespace BoundedGaps.BombieriVinogradov

/-- Every fixed positive level below one half follows from the standard
weighted Bombieri--Vinogradov proposition. -/
theorem bombieriVinogradov_of_weightedBombieriVinogradov
    (hBV : weightedBombieriVinogradov) :
    BoundedGaps.Maynard.bombieriVinogradov := by
  intro theta htheta0 htheta
  exact hasPrimeLevel_of_weightedBombieriVinogradov hBV htheta0 htheta

end BoundedGaps.BombieriVinogradov
