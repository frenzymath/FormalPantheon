import Mathlib.Tactic.IntervalCases
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell1StagePQCertificate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell1StageQQCertificate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell1StageQdQdCertificate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell1StageTwoPdQCertificate

/-! Cached product-stage assembly for the Cell1 signed certificate. -/
open scoped BigOperators Polynomial

namespace PrimesRestrictedDigits

noncomputable section

namespace SectionSixFirstLowCentralLargeAboveCell1Certificate

def cell1CachedQQRow (k : Nat) : Polynomial Rat :=
  if k < 11 then cell1StageRow 0 k else 0

def cell1CachedTwoPdQRow (k : Nat) : Polynomial Rat :=
  if k < 9 then cell1StageRow 1 k else 0

def cell1CachedQdQdRow (k : Nat) : Polynomial Rat :=
  if k < 9 then cell1StageRow 2 k else 0

def cell1CachedPQRow (k : Nat) : Polynomial Rat :=
  if k < 10 then cell1StageRow 3 k else 0

theorem cell1StageQQ_eq_cached (k : Nat) (hk : k < 13) :
    cell1StageProductRow 0 k = cell1CachedQQRow k := by
  interval_cases k <;> simp [cell1CachedQQRow]

theorem cell1StageTwoPdQ_eq_cached (k : Nat) (hk : k < 13) :
    cell1StageProductRow 1 k = cell1CachedTwoPdQRow k := by
  interval_cases k <;> simp [cell1CachedTwoPdQRow]

theorem cell1StageQdQd_eq_cached (k : Nat) (hk : k < 13) :
    cell1StageProductRow 2 k = cell1CachedQdQdRow k := by
  interval_cases k <;> simp [cell1CachedQdQdRow]

theorem cell1StagePQ_eq_cached (k : Nat) (hk : k < 13) :
    cell1StageProductRow 3 k = cell1CachedPQRow k := by
  interval_cases k <;> simp [cell1CachedPQRow]

theorem cell1OuterConv_congr_le
    {p p' q q' : Nat -> Polynomial Rat} {k : Nat}
    (hp : ∀ i, i ≤ k → p i = p' i) (hq : ∀ i, i ≤ k → q i = q' i) :
    cell1OuterConv p q k = cell1OuterConv p' q' k := by
  rw [cell1OuterConv, cell1OuterConv]
  apply Finset.sum_congr rfl
  intro a ha
  have hs := Finset.mem_antidiagonal.mp ha
  have ha1 : a.1 <= k := by
    calc
      a.1 <= a.1 + a.2 := Nat.le_add_right _ _
      _ = k := hs
  have ha2 : a.2 <= k := by
    calc
      a.2 <= a.1 + a.2 := Nat.le_add_left _ _
      _ = k := hs
  rw [hp a.1 ha1, hq a.2 ha2]

def cell1CachedSignedOuterRow (k : Nat) : Polynomial Rat :=
  cell1OuterConv cell1PDeriv2Coeff cell1CachedQQRow k -
    cell1OuterConv cell1CachedTwoPdQRow cell1QDerivCoeff k +
    cell1OuterConv cell1TwoPCoeff cell1CachedQdQdRow k -
    cell1OuterConv cell1CachedPQRow cell1QDeriv2Coeff k

theorem cell1SignedOuterRow_eq_cached (k : Nat) (hk : k < 13) :
    cell1SignedOuterRow k = cell1CachedSignedOuterRow k := by
  have h0 :
      cell1OuterConv cell1PDeriv2Coeff (cell1StageProductRow 0) k =
        cell1OuterConv cell1PDeriv2Coeff cell1CachedQQRow k := by
    apply cell1OuterConv_congr_le
    · intro i hi
      rfl
    · intro i hi
      exact cell1StageQQ_eq_cached i (lt_of_le_of_lt hi hk)
  have h1 :
      cell1OuterConv (cell1StageProductRow 1) cell1QDerivCoeff k =
        cell1OuterConv cell1CachedTwoPdQRow cell1QDerivCoeff k := by
    apply cell1OuterConv_congr_le
    · intro i hi
      exact cell1StageTwoPdQ_eq_cached i (lt_of_le_of_lt hi hk)
    · intro i hi
      rfl
  have h2 :
      cell1OuterConv cell1TwoPCoeff (cell1StageProductRow 2) k =
        cell1OuterConv cell1TwoPCoeff cell1CachedQdQdRow k := by
    apply cell1OuterConv_congr_le
    · intro i hi
      rfl
    · intro i hi
      exact cell1StageQdQd_eq_cached i (lt_of_le_of_lt hi hk)
  have h3 :
      cell1OuterConv (cell1StageProductRow 3) cell1QDeriv2Coeff k =
        cell1OuterConv cell1CachedPQRow cell1QDeriv2Coeff k := by
    apply cell1OuterConv_congr_le
    · intro i hi
      exact cell1StagePQ_eq_cached i (lt_of_le_of_lt hi hk)
    · intro i hi
      rfl
  unfold cell1SignedOuterRow cell1CachedSignedOuterRow
  rw [h0, h1, h2, h3]

end SectionSixFirstLowCentralLargeAboveCell1Certificate

end

end PrimesRestrictedDigits
