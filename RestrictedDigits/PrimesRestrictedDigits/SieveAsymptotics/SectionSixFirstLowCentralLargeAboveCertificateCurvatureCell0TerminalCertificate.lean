import Mathlib.Tactic.IntervalCases
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell0Terminal1Certificate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell0Terminal2Certificate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell0Terminal3Certificate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell0Terminal4Certificate

/-!
# Aggregated static terminal cache for Cell0

The bounded coefficient theorems are the intended signed-coordinate API:
after staging the signed coefficient, rewrite its four unsigned terms and
finish the resulting exact rational identity with `norm_num`.
-/
open scoped BigOperators Polynomial

namespace PrimesRestrictedDigits

noncomputable section

namespace SectionSixFirstLowCentralLargeAboveCell0Certificate

theorem cell0CachedTerm1Row_eq_terminal (k : Nat) (hk : k < 22) :
    cell0CachedTerm1Row k = cell0Terminal1Row k := by
  interval_cases k <;> simp only [cell0Term1_row_0, cell0Term1_row_1,
    cell0Term1_row_2, cell0Term1_row_3, cell0Term1_row_4, cell0Term1_row_5,
    cell0Term1_row_6, cell0Term1_row_7, cell0Term1_row_8, cell0Term1_row_9,
    cell0Term1_row_10, cell0Term1_row_11, cell0Term1_row_12, cell0Term1_row_13,
    cell0Term1_row_14, cell0Term1_row_15, cell0Term1_row_16, cell0Term1_row_17,
    cell0Term1_row_18, cell0Term1_row_19, cell0Term1_row_20, cell0Term1_row_21]

theorem cell0CachedTerm2Row_eq_terminal (k : Nat) (hk : k < 22) :
    cell0CachedTerm2Row k = cell0Terminal2Row k := by
  interval_cases k <;> simp only [cell0Term2_row_0, cell0Term2_row_1,
    cell0Term2_row_2, cell0Term2_row_3, cell0Term2_row_4, cell0Term2_row_5,
    cell0Term2_row_6, cell0Term2_row_7, cell0Term2_row_8, cell0Term2_row_9,
    cell0Term2_row_10, cell0Term2_row_11, cell0Term2_row_12, cell0Term2_row_13,
    cell0Term2_row_14, cell0Term2_row_15, cell0Term2_row_16, cell0Term2_row_17,
    cell0Term2_row_18, cell0Term2_row_19, cell0Term2_row_20, cell0Term2_row_21]

theorem cell0CachedTerm3Row_eq_terminal (k : Nat) (hk : k < 22) :
    cell0CachedTerm3Row k = cell0Terminal3Row k := by
  interval_cases k <;> simp only [cell0Term3_row_0, cell0Term3_row_1,
    cell0Term3_row_2, cell0Term3_row_3, cell0Term3_row_4, cell0Term3_row_5,
    cell0Term3_row_6, cell0Term3_row_7, cell0Term3_row_8, cell0Term3_row_9,
    cell0Term3_row_10, cell0Term3_row_11, cell0Term3_row_12, cell0Term3_row_13,
    cell0Term3_row_14, cell0Term3_row_15, cell0Term3_row_16, cell0Term3_row_17,
    cell0Term3_row_18, cell0Term3_row_19, cell0Term3_row_20, cell0Term3_row_21]

theorem cell0CachedTerm4Row_eq_terminal (k : Nat) (hk : k < 22) :
    cell0CachedTerm4Row k = cell0Terminal4Row k := by
  interval_cases k <;> simp only [cell0Term4_row_0, cell0Term4_row_1,
    cell0Term4_row_2, cell0Term4_row_3, cell0Term4_row_4, cell0Term4_row_5,
    cell0Term4_row_6, cell0Term4_row_7, cell0Term4_row_8, cell0Term4_row_9,
    cell0Term4_row_10, cell0Term4_row_11, cell0Term4_row_12, cell0Term4_row_13,
    cell0Term4_row_14, cell0Term4_row_15, cell0Term4_row_16, cell0Term4_row_17,
    cell0Term4_row_18, cell0Term4_row_19, cell0Term4_row_20, cell0Term4_row_21]

theorem cell0CachedSignedOuterRow_eq_terminal_rows (k : Nat) (hk : k < 22) :
    cell0CachedSignedOuterRow k =
      -(cell0Terminal1Row k - cell0Terminal2Row k +
        cell0Terminal3Row k - cell0Terminal4Row k) := by
  rw [cell0CachedSignedOuterRow_staged,
    cell0CachedTerm1Row_eq_terminal k hk,
    cell0CachedTerm2Row_eq_terminal k hk,
    cell0CachedTerm3Row_eq_terminal k hk,
    cell0CachedTerm4Row_eq_terminal k hk]

theorem cell0CachedTerm1Row_coeff_terminal
    (k l : Nat) (hk : k < 22) (hl : l < 12) :
    (cell0CachedTerm1Row k).coeff l = cell0Terminal1Value k l := by
  rw [cell0CachedTerm1Row_eq_terminal k hk, cell0Terminal1Row_coeff, if_pos hl]

theorem cell0CachedTerm2Row_coeff_terminal
    (k l : Nat) (hk : k < 22) (hl : l < 12) :
    (cell0CachedTerm2Row k).coeff l = cell0Terminal2Value k l := by
  rw [cell0CachedTerm2Row_eq_terminal k hk, cell0Terminal2Row_coeff, if_pos hl]

theorem cell0CachedTerm3Row_coeff_terminal
    (k l : Nat) (hk : k < 22) (hl : l < 12) :
    (cell0CachedTerm3Row k).coeff l = cell0Terminal3Value k l := by
  rw [cell0CachedTerm3Row_eq_terminal k hk, cell0Terminal3Row_coeff, if_pos hl]

theorem cell0CachedTerm4Row_coeff_terminal
    (k l : Nat) (hk : k < 22) (hl : l < 12) :
    (cell0CachedTerm4Row k).coeff l = cell0Terminal4Value k l := by
  rw [cell0CachedTerm4Row_eq_terminal k hk, cell0Terminal4Row_coeff, if_pos hl]

theorem cell0CachedSignedOuterRow_coeff_staged (k l : Nat) :
    (cell0CachedSignedOuterRow k).coeff l =
      -((cell0CachedTerm1Row k).coeff l -
        (cell0CachedTerm2Row k).coeff l +
        (cell0CachedTerm3Row k).coeff l -
        (cell0CachedTerm4Row k).coeff l) := by
  rw [cell0CachedSignedOuterRow_staged]
  simp only [Polynomial.coeff_neg, Polynomial.coeff_sub, Polynomial.coeff_add]

theorem cell0CachedSignedOuterRow_coeff_terminal_values
    (k l : Nat) (hk : k < 22) (hl : l < 12) :
    (cell0CachedSignedOuterRow k).coeff l =
      -(cell0Terminal1Value k l - cell0Terminal2Value k l +
        cell0Terminal3Value k l - cell0Terminal4Value k l) := by
  rw [cell0CachedSignedOuterRow_coeff_staged,
    cell0CachedTerm1Row_coeff_terminal k l hk hl,
    cell0CachedTerm2Row_coeff_terminal k l hk hl,
    cell0CachedTerm3Row_coeff_terminal k l hk hl,
    cell0CachedTerm4Row_coeff_terminal k l hk hl]

end SectionSixFirstLowCentralLargeAboveCell0Certificate

end

end PrimesRestrictedDigits
