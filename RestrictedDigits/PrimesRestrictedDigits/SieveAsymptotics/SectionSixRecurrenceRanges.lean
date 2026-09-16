import PrimesRestrictedDigits.SieveAsymptotics.SectionSixRecurrenceState
import Mathlib.Tactic.NormNum

/-!
# Exact range predicates for corrected Section 6 states

The strict states use their current complete modulus. A repeated state uses the exact natural
quotient by its duplicated terminal prime, which is the pre-repeat product in Maynard's
`RU`/`RV` definitions.
-/

namespace PrimesRestrictedDigits

noncomputable section

def sectionSixStateInnerRange
    (X delta theta : Real) (inner : List Nat) : Prop :=
  ∀ q ∈ inner,
    X ^ delta < (q : Real) ∧ (q : Real) ≤ X ^ theta

def sectionSixStateCutoffPredicate
    (kind : SectionSixStateKind) (R : Real) (n : Nat)
    (inner : List Nat) : Prop :=
  match kind with
  | SectionSixStateKind.T => (n : Real) ≤ R
  | SectionSixStateKind.U => (n : Real) ≤ R
  | SectionSixStateKind.V =>
      ∃ q : Nat, ∃ rest : List Nat,
        inner = q :: rest ∧ q ∣ n ∧
          R < (n : Real) ∧ (n : Real) ≤ R * (q : Real)
  | SectionSixStateKind.RU =>
      ∃ q : Nat, ∃ rest : List Nat,
        inner = q :: q :: rest ∧ q ∣ n ∧
          ((n / q : Nat) : Real) ≤ R
  | SectionSixStateKind.RV =>
      ∃ q : Nat, ∃ rest : List Nat,
        inner = q :: q :: rest ∧ q ∣ n ∧
          R < ((n / q : Nat) : Real) ∧
            ((n / q : Nat) : Real) ≤ R * (q : Real)

def sectionSixStateBandCutoff
    (band : SectionSixStateBand) (X thetaOne thetaTwo : Real) : Real :=
  match band with
  | SectionSixStateBand.low => X ^ thetaOne
  | SectionSixStateBand.high => X ^ (1 - thetaTwo)

def IsSectionSixRecurrenceState
    {band : SectionSixStateBand} {ell n : Nat}
    (X delta theta thetaOne thetaTwo : Real)
    (s : SectionSixRecurrenceState band ell n) : Prop :=
  sectionSixStateInnerRange X delta theta s.inner ∧
    sectionSixStateCutoffPredicate s.kind
      (sectionSixStateBandCutoff band X thetaOne thetaTwo)
      n s.inner

theorem sectionSixRepeatedPreProduct_mul_eq
    {n q : Nat} (hq : q ∣ n) :
    (n / q) * q = n := by
  exact Nat.div_mul_cancel hq

theorem sectionSixRepeatedPreProduct_cast_mul_eq
    {n q : Nat} (hq : q ∣ n) :
    ((n / q : Nat) : Real) * (q : Real) = (n : Real) := by
  exact_mod_cast sectionSixRepeatedPreProduct_mul_eq hq

theorem sectionSixStateCutoff_T_empty
    {R : Real} {n : Nat} (hn : (n : Real) ≤ R) :
    sectionSixStateCutoffPredicate SectionSixStateKind.T R n [] := by
  exact hn

theorem sectionSixStateCutoff_RU_repeated_two
    {R : Real} (hR : (2 : Real) ≤ R) :
    sectionSixStateCutoffPredicate SectionSixStateKind.RU R 4 [2, 2] := by
  refine ⟨2, [], by rfl, by norm_num, ?_⟩
  exact hR

theorem sectionSixStateCutoff_RV_repeated_two
    {R : Real} (hRlower : R < 2) (hRupper : (2 : Real) ≤ R * 2) :
    sectionSixStateCutoffPredicate SectionSixStateKind.RV R 4 [2, 2] := by
  refine ⟨2, [], by rfl, by norm_num, hRlower, hRupper⟩

end

end PrimesRestrictedDigits
