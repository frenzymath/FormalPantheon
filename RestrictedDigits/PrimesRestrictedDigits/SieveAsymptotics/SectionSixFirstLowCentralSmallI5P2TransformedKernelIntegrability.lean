import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P2TransformedKernel
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P2TransformedImageEquality
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5PairPatternIntegralAggregate
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# P2 transformed-kernel integrability

This module transports the existing fixed-pattern physical integrability to the exact
transformed domain and uses the pointwise identity. It makes no Jacobian, Fubini/Tonelli,
numerical, or cap claim.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.12).
-/

set_option autoImplicit false

open MeasureTheory Set
namespace PrimesRestrictedDigits

noncomputable section

private abbrev d748Domain : Set SectionSixAffineT :=
  sectionSixFirstLowCentralSmallI5P2Domain

private abbrev d748Beta : Real :=
  sectionSixThetaTwo (1 / 1000000 : Real)

private theorem d748Domain_measurable : MeasurableSet d748Domain := by
  unfold d748Domain sectionSixFirstLowCentralSmallI5P2Domain
  measurability

theorem sectionSixFirstLowCentralSmallI5P2TransformedKernel_integrableOn :
    IntegrableOn sectionSixFirstLowCentralSmallI5P2TransformedKernel
      sectionSixFirstLowCentralSmallI5P2Domain
      (volume : Measure SectionSixAffineT) := by
  have hphysical : IntegrableOn
      sectionSixFirstLowCentralSmallQuadrupleKernel
      (sectionSixFirstLowCentralSmallI5PairPatternTarget (2 : Fin 4)) :=
    sectionSixFirstLowCentralSmallI5PairPatternTarget_integrable (2 : Fin 4)
  have hpullback :
      IntegrableOn
        (sectionSixFirstLowCentralSmallQuadrupleKernel ∘ sectionSixP2Phi d748Beta)
        d748Domain (volume : Measure SectionSixAffineT) := by
    apply ((sectionSixP2Phi_measurePreserving d748Beta).integrableOn_image
      (sectionSixP2Phi_measurableEmbedding d748Beta) (f :=
        sectionSixFirstLowCentralSmallQuadrupleKernel) (s := d748Domain)).mp
    change IntegrableOn sectionSixFirstLowCentralSmallQuadrupleKernel
      (sectionSixP2Phi (sectionSixThetaTwo (1 / 1000000 : Real)) '' d748Domain)
      (volume : Measure SectionSixAffineT)
    rw [sectionSixFirstLowCentralSmallI5P2Phi_image_eq_target]
    exact hphysical
  apply hpullback.congr_fun ?_ d748Domain_measurable
  intro z hz
  change sectionSixFirstLowCentralSmallQuadrupleKernel
      (sectionSixP2Phi (sectionSixThetaTwo (1 / 1000000 : Real)) z) =
    sectionSixFirstLowCentralSmallI5P2TransformedKernel z
  simpa [Function.comp_def] using
    sectionSixFirstLowCentralSmallI5P2Kernel_comp_Phi_eq z

end
end PrimesRestrictedDigits
