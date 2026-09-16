import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell1SignedCoeffSupport

/-! Terminal convolution rows for the high Cell1 signed certificate. -/
open scoped BigOperators Polynomial

namespace PrimesRestrictedDigits

noncomputable section

namespace SectionSixFirstLowCentralLargeAboveCell1Certificate

def cell1CachedTerm1Row (k : Nat) : Polynomial Rat :=
  cell1OuterConv cell1PDeriv2Coeff cell1CachedQQRow k

def cell1CachedTerm2Row (k : Nat) : Polynomial Rat :=
  cell1OuterConv cell1CachedTwoPdQRow cell1QDerivCoeff k

def cell1CachedTerm3Row (k : Nat) : Polynomial Rat :=
  cell1OuterConv cell1TwoPCoeff cell1CachedQdQdRow k

def cell1CachedTerm4Row (k : Nat) : Polynomial Rat :=
  cell1OuterConv cell1CachedPQRow cell1QDeriv2Coeff k

theorem cell1CachedSignedOuterRow_staged (k : Nat) :
    cell1CachedSignedOuterRow k =
      cell1CachedTerm1Row k - cell1CachedTerm2Row k +
        cell1CachedTerm3Row k - cell1CachedTerm4Row k := by
  rfl

end SectionSixFirstLowCentralLargeAboveCell1Certificate

end

end PrimesRestrictedDigits
