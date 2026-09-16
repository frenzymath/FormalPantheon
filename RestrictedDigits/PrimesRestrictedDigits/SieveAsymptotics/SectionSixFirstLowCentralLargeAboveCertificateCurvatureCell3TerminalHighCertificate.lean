import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3Terminal1HighCertificate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3Terminal2HighCertificate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3Terminal3HighCertificate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3Terminal4HighCertificate

/-! Aggregated terminal cache and signed-to-Power bridges for Cell3. -/
open scoped BigOperators Polynomial

namespace PrimesRestrictedDigits

noncomputable section

namespace SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3

theorem cell3CachedSignedOuterRow_coeff_terminal
    (k l : Nat) (hk_low : 11 ≤ k) (hk_high : k ≤ 24) (hl : l < 10) :
    (cell3CachedSignedOuterRow k).coeff l =
      -(cell3StageValue 6 k l - cell3StageValue 7 k l +
        cell3StageValue 8 k l - cell3StageValue 9 k l) := by
  rw [cell3CachedSignedOuterRow]
  simp only [Polynomial.coeff_neg, Polynomial.coeff_sub, Polynomial.coeff_add]
  rw [cell3CachedTerm1Row_coeff_terminal k l hk_low hk_high hl,
    cell3CachedTerm2Row_coeff_terminal k l hk_low hk_high hl,
    cell3CachedTerm3Row_coeff_terminal k l hk_low hk_high hl,
    cell3CachedTerm4Row_coeff_terminal k l hk_low hk_high hl]

end SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3

end

end PrimesRestrictedDigits
