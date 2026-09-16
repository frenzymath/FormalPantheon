import Mathlib.Tactic.IntervalCases
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3StagePQCertificate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3StageQQCertificate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3StageQdQdCertificate
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3StageTwoPdQCertificate

/-! Static terminal convolution rows for the high Cell3 certificate.

The four cached stage rows retain exactly the specialized finite supports from
the stage shards.  The signed row below deliberately keeps the outer minus
from `cell3SignedOuterRow`; this is the convention consumed by the curvature
assembly.
-/
open scoped BigOperators Polynomial

namespace PrimesRestrictedDigits

noncomputable section

namespace SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3

open Polynomial (C X)

def cell3CachedQQRow (k : Nat) : Polynomial Rat :=
  if k < 19 then cell3StageRow 0 k else 0

def cell3CachedTwoPdQRow (k : Nat) : Polynomial Rat :=
  if k < 17 then cell3StageRow 1 k else 0

def cell3CachedQdQdRow (k : Nat) : Polynomial Rat :=
  if k < 17 then cell3StageRow 2 k else 0

def cell3CachedPQRow (k : Nat) : Polynomial Rat :=
  if k < 18 then cell3StageRow 3 k else 0

theorem cell3StageQQ_eq_cached (k : Nat) (hk : k < 25) :
    cell3StageProductRow 0 k = cell3CachedQQRow k := by
  interval_cases k <;> simp [cell3CachedQQRow]

theorem cell3StageTwoPdQ_eq_cached (k : Nat) (hk : k < 25) :
    cell3StageProductRow 1 k = cell3CachedTwoPdQRow k := by
  interval_cases k <;> simp [cell3CachedTwoPdQRow]

theorem cell3StageQdQd_eq_cached (k : Nat) (hk : k < 25) :
    cell3StageProductRow 2 k = cell3CachedQdQdRow k := by
  interval_cases k <;> simp [cell3CachedQdQdRow]

theorem cell3StagePQ_eq_cached (k : Nat) (hk : k < 25) :
    cell3StageProductRow 3 k = cell3CachedPQRow k := by
  interval_cases k <;> simp [cell3CachedPQRow]

theorem cell3OuterConv_congr_le
    {p p' q q' : Nat → Polynomial Rat} {k : Nat}
    (hp : ∀ i, i ≤ k → p i = p' i)
    (hq : ∀ i, i ≤ k → q i = q' i) :
    cell3OuterConv p q k = cell3OuterConv p' q' k := by
  rw [cell3OuterConv, cell3OuterConv]
  apply Finset.sum_congr rfl
  intro a ha
  have hs := Finset.mem_antidiagonal.mp ha
  have ha1 : a.1 ≤ k := by
    calc
      a.1 ≤ a.1 + a.2 := Nat.le_add_right _ _
      _ = k := hs
  have ha2 : a.2 ≤ k := by
    calc
      a.2 ≤ a.1 + a.2 := Nat.le_add_left _ _
      _ = k := hs
  rw [hp a.1 ha1, hq a.2 ha2]

def cell3CachedTerm1Row (k : Nat) : Polynomial Rat :=
  cell3OuterConv cell3PDeriv2Coeff cell3CachedQQRow k

def cell3CachedTerm2Row (k : Nat) : Polynomial Rat :=
  cell3OuterConv cell3CachedTwoPdQRow cell3QDerivCoeff k

def cell3CachedTerm3Row (k : Nat) : Polynomial Rat :=
  cell3OuterConv cell3TwoPCoeff cell3CachedQdQdRow k

def cell3CachedTerm4Row (k : Nat) : Polynomial Rat :=
  cell3OuterConv cell3CachedPQRow cell3QDeriv2Coeff k

def cell3CachedSignedOuterRow (k : Nat) : Polynomial Rat :=
  -(cell3CachedTerm1Row k - cell3CachedTerm2Row k +
      cell3CachedTerm3Row k - cell3CachedTerm4Row k)

theorem cell3CachedSignedOuterRow_staged (k : Nat) :
    cell3CachedSignedOuterRow k =
      -(cell3CachedTerm1Row k - cell3CachedTerm2Row k +
        cell3CachedTerm3Row k - cell3CachedTerm4Row k) := by
  rfl

theorem cell3SignedOuterRow_eq_cached (k : Nat) (hk : k < 25) :
    cell3SignedOuterRow k = cell3CachedSignedOuterRow k := by
  have h0 :
      cell3OuterConv cell3PDeriv2Coeff (cell3StageProductRow 0) k =
        cell3OuterConv cell3PDeriv2Coeff cell3CachedQQRow k := by
    apply cell3OuterConv_congr_le
    · intro i hi
      rfl
    · intro i hi
      exact cell3StageQQ_eq_cached i (lt_of_le_of_lt hi hk)
  have h1 :
      cell3OuterConv (cell3StageProductRow 1) cell3QDerivCoeff k =
        cell3OuterConv cell3CachedTwoPdQRow cell3QDerivCoeff k := by
    apply cell3OuterConv_congr_le
    · intro i hi
      exact cell3StageTwoPdQ_eq_cached i (lt_of_le_of_lt hi hk)
    · intro i hi
      rfl
  have h2 :
      cell3OuterConv cell3TwoPCoeff (cell3StageProductRow 2) k =
        cell3OuterConv cell3TwoPCoeff cell3CachedQdQdRow k := by
    apply cell3OuterConv_congr_le
    · intro i hi
      rfl
    · intro i hi
      exact cell3StageQdQd_eq_cached i (lt_of_le_of_lt hi hk)
  have h3 :
      cell3OuterConv (cell3StageProductRow 3) cell3QDeriv2Coeff k =
        cell3OuterConv cell3CachedPQRow cell3QDeriv2Coeff k := by
    apply cell3OuterConv_congr_le
    · intro i hi
      exact cell3StagePQ_eq_cached i (lt_of_le_of_lt hi hk)
    · intro i hi
      rfl
  unfold cell3SignedOuterRow cell3CachedSignedOuterRow
  simp only [cell3CachedTerm1Row, cell3CachedTerm2Row,
    cell3CachedTerm3Row, cell3CachedTerm4Row]
  rw [h0, h1, h2, h3]

@[simp] theorem cell3CachedQQRow_coeff_if (i l : Nat) :
    (cell3CachedQQRow i).coeff l =
      if i < 19 then (if l < 7 then cell3QQStageValue i l else 0) else 0 := by
  by_cases hi : i < 19 <;>
    simp [cell3CachedQQRow, cell3StageRow_coeff,
      cell3StageProductValue_zero, hi]

@[simp] theorem cell3CachedTwoPdQRow_coeff_if (i l : Nat) :
    (cell3CachedTwoPdQRow i).coeff l =
      if i < 17 then (if l < 7 then cell3TwoPdQStageValue i l else 0) else 0 := by
  by_cases hi : i < 17 <;>
    simp [cell3CachedTwoPdQRow, cell3StageRow_coeff,
      cell3StageProductValue_one, hi]

@[simp] theorem cell3CachedQdQdRow_coeff_if (i l : Nat) :
    (cell3CachedQdQdRow i).coeff l =
      if i < 17 then (if l < 7 then cell3QdQdStageValue i l else 0) else 0 := by
  by_cases hi : i < 17 <;>
    simp [cell3CachedQdQdRow, cell3StageRow_coeff,
      cell3StageProductValue_two, hi]

@[simp] theorem cell3CachedPQRow_coeff_if (i l : Nat) :
    (cell3CachedPQRow i).coeff l =
      if i < 18 then (if l < 7 then cell3PQStageValue i l else 0) else 0 := by
  by_cases hi : i < 18 <;>
    simp [cell3CachedPQRow, cell3StageRow_coeff,
      cell3StageProductValue_three, hi]

theorem cell3CachedSignedOuterRow_coeff (k l : Nat) :
    (cell3CachedSignedOuterRow k).coeff l =
      -(cell3ScalarConv (fun i j => (cell3PDeriv2Coeff i).coeff j)
          (fun i j => (cell3CachedQQRow i).coeff j) k l -
        cell3ScalarConv (fun i j => (cell3CachedTwoPdQRow i).coeff j)
          (fun i j => (cell3QDerivCoeff i).coeff j) k l +
        cell3ScalarConv (fun i j => (cell3TwoPCoeff i).coeff j)
          (fun i j => (cell3CachedQdQdRow i).coeff j) k l -
        cell3ScalarConv (fun i j => (cell3CachedPQRow i).coeff j)
          (fun i j => (cell3QDeriv2Coeff i).coeff j) k l) := by
  simp only [cell3CachedSignedOuterRow, cell3CachedTerm1Row,
    cell3CachedTerm2Row, cell3CachedTerm3Row, cell3CachedTerm4Row,
    Polynomial.coeff_neg,
    Polynomial.coeff_sub, Polynomial.coeff_add, cell3OuterConv_coeff]

end SectionSixFirstLowCentralLargeAboveCertificateCurvatureCell3

end

end PrimesRestrictedDigits
