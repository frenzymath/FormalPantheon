import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P2SetIntegralTransport
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallQuadrupleRegions
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.Ring

/-!
# P2 transformed-kernel formula

This module exposes the algebraic kernel rewrite after the set-integral transport. It makes no
integrability, Jacobian, Fubini, numerical, or cap assertion.

Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq. (6.12).
-/

set_option autoImplicit false

open MeasureTheory Set

namespace PrimesRestrictedDigits

noncomputable section

def sectionSixFirstLowCentralSmallI5P2TransformedKernel
    (z : SectionSixAffineT) : Real :=
  buchstabFunction
      ((1 - sectionSixThetaTwo (1 / 1000000 : Real) -
          2 * z.1.1.1 - z.1.1.2 - z.1.2 - z.2) /
        (z.1.1.1 + z.2)) /
    ((sectionSixThetaTwo (1 / 1000000 : Real) - z.1.1.1) *
      (z.1.1.1 + z.1.1.2) * (z.1.1.1 + z.1.2) *
      (z.1.1.1 + z.2) ^ (2 : Nat))

theorem sectionSixFirstLowCentralSmallI5P2Kernel_comp_Phi_eq :
    ∀ z : SectionSixAffineT,
      sectionSixFirstLowCentralSmallQuadrupleKernel
          (sectionSixP2Phi (sectionSixThetaTwo (1 / 1000000 : Real)) z) =
        sectionSixFirstLowCentralSmallI5P2TransformedKernel z := by
  intro z
  unfold sectionSixFirstLowCentralSmallQuadrupleKernel
    sectionSixFirstLowCentralSmallI5P2TransformedKernel
  simp [sectionSixP2Phi]
  congr 2; ring

private theorem sectionSixFirstLowCentralSmallI5P2Domain_measurable :
    MeasurableSet sectionSixFirstLowCentralSmallI5P2Domain := by
  unfold sectionSixFirstLowCentralSmallI5P2Domain
  measurability

theorem sectionSixFirstLowCentralSmallI5P2Target_setIntegral_eq_transformedKernel :
    (∫ x in sectionSixFirstLowCentralSmallI5P2Target,
      sectionSixFirstLowCentralSmallQuadrupleKernel x
      ∂(volume : Measure SectionSixAffineT)) =
      ∫ z in sectionSixFirstLowCentralSmallI5P2Domain,
        sectionSixFirstLowCentralSmallI5P2TransformedKernel z
          ∂(volume : Measure SectionSixAffineT) := by
  rw [p2_kernel_target_setIntegral_eq_pullback]
  exact setIntegral_congr_fun sectionSixFirstLowCentralSmallI5P2Domain_measurable
    (fun z hz => by
      simpa using sectionSixFirstLowCentralSmallI5P2Kernel_comp_Phi_eq z)

end
end PrimesRestrictedDigits
