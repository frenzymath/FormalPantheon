import PrimesRestrictedDigits.BasicEstimates.BuchstabBounds
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstUniformIntegralRegions
import Mathlib.Tactic.Linarith

/-!
# The low-central-small outer Buchstab argument

The fixed mixed outer carrier only gives a
Buchstab argument at least one; stronger middle/tail envelopes require separate branch
hypotheses and are intentionally absent. Source: `MAYNARD-PRD-PUBLISHED`, Section 6, Eq.
(6.12).
-/

namespace PrimesRestrictedDigits

theorem sectionSixFirstLowCentralSmallUniformOuter_argument_ge_one
    {delta : Real} {x : (((Real × Real) × Real) × Real)}
    (hgap : 0 < sectionSixThetaGap delta)
    (hx : x ∈ sectionSixFirstLowCentralSmallUniformOuterRegion delta) :
    1 <=
      (1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2 := by
  rcases hx with ⟨hwall, htw, hwv, hvu, hu, hsum, hmix, hcap,
    hpair₁, hpair₂, hpair₃, hpair₄, hpair₅⟩
  have htPos : 0 < x.2 := hgap.trans hwall
  apply (le_div_iff₀ htPos).2
  linarith

theorem sectionSixFirstLowCentralSmallUniformOuter_buchstab_le_one
    {delta : Real} {x : (((Real × Real) × Real) × Real)}
    (hgap : 0 < sectionSixThetaGap delta)
    (hx : x ∈ sectionSixFirstLowCentralSmallUniformOuterRegion delta) :
    buchstabFunction
        ((1 - x.1.1.1 - x.1.1.2 - x.1.2 - x.2) / x.2) <= 1 := by
  exact (buchstabFunction_mem_Icc
    (sectionSixFirstLowCentralSmallUniformOuter_argument_ge_one hgap hx)).2

end PrimesRestrictedDigits
