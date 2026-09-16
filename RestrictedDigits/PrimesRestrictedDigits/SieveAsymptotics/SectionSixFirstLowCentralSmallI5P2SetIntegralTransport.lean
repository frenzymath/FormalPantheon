import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P2TransformedImageEquality
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# P2 fixed-delta set-integral transport

This module applies the affine set-integral identities to the fixed-delta P2 image and
preimage equalities. It makes no integrability, Jacobian, Fubini, numerical, or cap assertion.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.12).
-/

set_option autoImplicit false

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

theorem p2_kernel_target_setIntegral_eq_pullback :
    (∫ x in sectionSixFirstLowCentralSmallI5P2Target,
      sectionSixFirstLowCentralSmallQuadrupleKernel x
      ∂(volume : Measure SectionSixAffineT)) =
      ∫ z in sectionSixFirstLowCentralSmallI5P2Domain,
        sectionSixFirstLowCentralSmallQuadrupleKernel
          (sectionSixP2Phi (sectionSixThetaTwo (1 / 1000000 : Real)) z)
          ∂(volume : Measure SectionSixAffineT) := by
  rw [← sectionSixFirstLowCentralSmallI5P2Phi_image_eq_target]
  exact sectionSixP2Phi_setIntegral
    (sectionSixThetaTwo (1 / 1000000 : Real))
    sectionSixFirstLowCentralSmallQuadrupleKernel
    sectionSixFirstLowCentralSmallI5P2Domain

theorem p2_target_setIntegral_eq_pullback_via_preimage
    (g : SectionSixAffineT → Real) :
    (∫ x in sectionSixFirstLowCentralSmallI5P2Target,
      g (sectionSixP2Psi (sectionSixThetaTwo (1 / 1000000 : Real)) x)
      ∂(volume : Measure SectionSixAffineT)) =
      ∫ z in sectionSixFirstLowCentralSmallI5P2Domain, g z
        ∂(volume : Measure SectionSixAffineT) := by
  rw [← sectionSixFirstLowCentralSmallI5P2Psi_preimage_target_eq_domain]
  exact (sectionSixP2Psi_measurePreserving
      (sectionSixThetaTwo (1 / 1000000 : Real))).setIntegral_preimage_emb
    (sectionSixP2Psi_measurableEmbedding
      (sectionSixThetaTwo (1 / 1000000 : Real))) g
    sectionSixFirstLowCentralSmallI5P2Domain

end
end PrimesRestrictedDigits
