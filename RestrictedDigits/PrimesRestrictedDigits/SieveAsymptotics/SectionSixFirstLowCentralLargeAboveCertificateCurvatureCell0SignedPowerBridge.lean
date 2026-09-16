import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell0SignedCoeffCertificates
/-!
# Full signed-to-power bridge for Cell0

The finite row frontier handles `k < 22`; the separate degree bound handles
the outer tail.  No tensor declaration is imported or unfolded here.
-/
open scoped BigOperators Polynomial
namespace PrimesRestrictedDigits
noncomputable section
namespace SectionSixFirstLowCentralLargeAboveCell0Certificate

theorem cell0SignedCurvature_eq_power_cached :
    cell0SignedCurvature = cell0Power := by
  ext k l
  by_cases hk : k < 22
  · rw [cell0Power_outer_coeff k hk]
    interval_cases k <;> simp
  · have hk' : 22 ≤ k := Nat.le_of_not_gt hk
    have hs : cell0SignedCurvature.coeff k = 0 :=
      cell0SignedCurvature_coeff_zero k hk'
    have hp : cell0Power.coeff k = 0 := by
      rw [cell0Power, Polynomial.finsetSum_coeff]
      simp [hk']
    rw [hs, hp]

end SectionSixFirstLowCentralLargeAboveCell0Certificate
end
end PrimesRestrictedDigits
