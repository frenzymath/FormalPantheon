import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P0AmbientIntegrability

/-!
# Unconditional P0 ambient-cell Fubini transport

This is the fixed-branch composition of the ordered-outer transport with the product-cell
integrability theorem. It makes no source, projection, cap, branch-cover, or global-integral
claim.
-/

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

theorem sectionSixFirstLowCentralSmallI5P0AmbientCell_setIntegral_eq_iterated_unconditional
    (b : Fin 3) :
    (∫ z in sectionSixFirstLowCentralSmallI5P0AmbientCell b,
      sectionSixFirstLowCentralSmallQuadrupleKernel z
        ∂(volume.prod volume)) =
      ∫ x in sectionSixFirstLowCentralSmallI5P0AmbientOrderedBase b,
        (∫ t in
          sectionSixFirstLowCentralSmallI5P0AmbientLower b x..
            sectionSixFirstLowCentralSmallI5P0AmbientUpper b x,
          sectionSixFirstLowCentralSmallQuadrupleKernel (x, t)) ∂volume := by
  exact sectionSixFirstLowCentralSmallI5P0AmbientCell_setIntegral_eq_iterated b
    (sectionSixFirstLowCentralSmallI5P0AmbientCell_integrable b)

end

end PrimesRestrictedDigits
