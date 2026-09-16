import PrimesRestrictedDigits.SieveAsymptotics.SectionSixStatePath
import PrimesRestrictedDigits.SieveDecomposition.SectionSixPrimeRecurrence
import Mathlib.Data.PNat.Basic
import Mathlib.Tactic.NormNum

/-!
# One-step occurrence of corrected Section 6 states

This file aligns one concrete weak Buchstab fiber with the indexed strict or repeated child
state. It is deliberately a local bridge: arbitrary paths are not declared to be summands of
the full recurrence.
-/

namespace PrimesRestrictedDigits

noncomputable section

theorem sectionSixRecurrenceState_modulus_pos
    {band : SectionSixStateBand} {ell n : Nat}
    (s : SectionSixRecurrenceState band ell n) : 0 < n := by
  rw [← s.product_eq]
  have houter : 0 < primeTupleProduct s.outer := by
    rw [primeTupleProduct]
    exact Finset.prod_pos (fun i hi => (s.outerPrime i).pos)
  have hinner : 0 < s.inner.prod := by
    apply List.prod_pos
    intro q hq
    exact (s.innerPrime q hq).pos
  exact Nat.mul_pos houter hinner

noncomputable def sectionSixStateModulusPNat
    {band : SectionSixStateBand} {ell n : Nat}
  (s : SectionSixRecurrenceState band ell n) : PNat :=
  ⟨n, sectionSixRecurrenceState_modulus_pos s⟩

@[simp] theorem sectionSixStateModulusPNat_coe
    {band : SectionSixStateBand} {ell n : Nat}
    (s : SectionSixRecurrenceState band ell n) :
    (sectionSixStateModulusPNat s : Nat) = n := rfl

def sectionSixStateStepChild
    {band : SectionSixStateBand} {ell : Nat}
    (s : SectionSixAnyState band ell) (step : SectionSixStateStep)
    (hq : step.q.Prime)
    (horder : ∀ r, r ∈ s.2.inner → step.q ≤ r) :
    SectionSixAnyState band ell :=
  match step.mode with
  | SectionSixStateStepMode.strict =>
      ⟨s.1 * step.q,
        sectionSixStrictChild s.2 step.kind step.q hq horder⟩
  | SectionSixStateStepMode.repeated =>
      ⟨s.1 * step.q * step.q,
        sectionSixRepeatedChild s.2 step.kind step.q hq horder⟩

def sectionSixStateStepAdmissible (step : SectionSixStateStep) : Prop :=
  match step.mode, step.kind with
  | SectionSixStateStepMode.strict, SectionSixStateKind.U => True
  | SectionSixStateStepMode.strict, SectionSixStateKind.V => True
  | SectionSixStateStepMode.repeated, SectionSixStateKind.RU => True
  | SectionSixStateStepMode.repeated, SectionSixStateKind.RV => True
  | _, _ => False

def sectionSixStateStepCutoffData
    (step : SectionSixStateStep) (n : Nat) (R : Real) : Prop :=
  match step.mode, step.kind with
  | SectionSixStateStepMode.strict, SectionSixStateKind.U =>
      ((n * step.q : Nat) : Real) ≤ R
  | SectionSixStateStepMode.strict, SectionSixStateKind.V =>
      R < ((n * step.q : Nat) : Real) ∧
        ((n * step.q : Nat) : Real) ≤ R * (step.q : Real)
  | SectionSixStateStepMode.repeated, SectionSixStateKind.RU =>
      ((n * step.q : Nat) : Real) ≤ R
  | SectionSixStateStepMode.repeated, SectionSixStateKind.RV =>
      R < ((n * step.q : Nat) : Real) ∧
        ((n * step.q : Nat) : Real) ≤ R * (step.q : Real)
  | _, _ => False

theorem sectionSixStateStep_singleton_path
    {band : SectionSixStateBand} {ell : Nat}
    (s : SectionSixAnyState band ell) (step : SectionSixStateStep)
    (hq : step.q.Prime)
    (horder : ∀ r, r ∈ s.2.inner → step.q ≤ r) :
    SectionSixStatePath s (sectionSixStateStepChild s step hq horder)
      [step] := by
  cases s with
  | mk n state =>
      cases step with
      | mk mode kind q =>
          cases mode with
          | strict =>
              exact SectionSixStatePath.strict ⟨.strict, kind, q⟩ rfl hq horder
                (SectionSixStatePath.nil _)
          | repeated =>
              exact SectionSixStatePath.repeated ⟨.repeated, kind, q⟩ rfl hq horder
                (SectionSixStatePath.nil _)

theorem sectionSixStateStepChild_inner_range
    {band : SectionSixStateBand} {ell : Nat}
    (s : SectionSixAnyState band ell) (step : SectionSixStateStep)
    (hq : step.q.Prime) (horder : ∀ r, r ∈ s.2.inner → step.q ≤ r)
    {X delta theta : Real}
    (hqRange : X ^ delta < (step.q : Real) ∧
      (step.q : Real) ≤ X ^ theta)
    (hstart : sectionSixStateInnerRange X delta theta s.2.inner) :
    sectionSixStateInnerRange X delta theta
      (sectionSixStateStepChild s step hq horder).2.inner := by
  cases step with
  | mk mode kind q =>
      cases mode with
      | strict =>
          exact sectionSixStrictChild_innerRange s.2 q hqRange hstart
      | repeated =>
          exact sectionSixRepeatedChild_innerRange s.2 q hqRange hstart

theorem sectionSixStateStepChild_cutoff
    {band : SectionSixStateBand} {ell : Nat}
    (s : SectionSixAnyState band ell) (step : SectionSixStateStep)
    (hq : step.q.Prime)
    (horder : ∀ r, r ∈ s.2.inner → step.q ≤ r)
    {R : Real} (hdata : sectionSixStateStepCutoffData step s.1 R) :
    sectionSixStateCutoffPredicate step.kind R
      (sectionSixStateStepChild s step hq horder).1
      (sectionSixStateStepChild s step hq horder).2.inner := by
  cases s with
  | mk n state =>
      cases step with
      | mk mode kind q =>
          simp only [sectionSixStateStepCutoffData] at hdata
          cases mode with
          | strict =>
              cases kind with
              | T => exact False.elim hdata
              | U =>
                  simpa [sectionSixStateStepCutoffData, sectionSixStateStepChild] using
                    sectionSixStrictChild_cutoff_U state q hq horder hdata
              | V =>
                  simpa [sectionSixStateStepCutoffData, sectionSixStateStepChild] using
                    sectionSixStrictChild_cutoff_V state q hq horder hdata.1 hdata.2
              | RU => exact False.elim hdata
              | RV => exact False.elim hdata
          | repeated =>
              cases kind with
              | T => exact False.elim hdata
              | U => exact False.elim hdata
              | V => exact False.elim hdata
              | RU =>
                  simpa [sectionSixStateStepCutoffData, sectionSixStateStepChild] using
                    sectionSixRepeatedChild_cutoff_RU state q hq horder hdata
              | RV =>
                  simpa [sectionSixStateStepCutoffData, sectionSixStateStepChild] using
                    sectionSixRepeatedChild_cutoff_RV state q hq horder hdata.1 hdata.2

def sectionSixStateStrictTerm
    (digit : Fin 10) (length : Nat)
    {band : SectionSixStateBand} {ell : Nat}
    {n : Nat} (s : SectionSixRecurrenceState band ell n) (z : Real) : Real :=
  sectionSixSiftedSum digit length (sectionSixStateModulusPNat s) z

def sectionSixStateWeakTerm
    (digit : Fin 10) (length : Nat)
    {band : SectionSixStateBand} {ell : Nat}
    {n : Nat} (s : SectionSixRecurrenceState band ell n) (z : Real) : Real :=
  sectionSixWeakSiftedSum digit length (sectionSixStateModulusPNat s) z

theorem sectionSixStrictPrimeTerm_eq_stateStrictTerm
    (digit : Fin 10) (length : Nat)
    {band : SectionSixStateBand} {ell n : Nat}
    (s : SectionSixRecurrenceState band ell n)
    (kind : SectionSixStateKind)
    {q : Nat} (hq : q.Prime)
    (horder : ∀ r, r ∈ s.inner → q ≤ r) :
    sectionSixStrictPrimeTerm digit length
        (sectionSixStateModulusPNat s) q =
      sectionSixStateStrictTerm digit length
        (sectionSixStrictChild s kind q hq horder) (q : Real) := by
  rw [sectionSixStrictPrimeTerm_eq_siftedSum digit length
    (sectionSixStateModulusPNat s) hq]
  unfold sectionSixStateStrictTerm sectionSixStateModulusPNat
  apply congrArg (fun d : PNat => sectionSixSiftedSum digit length d (q : Real))
  apply PNat.eq
  simp [Nat.toPNat'_coe, hq.pos]

theorem sectionSixRepeatedPrimeTerm_eq_stateWeakTerm
    (digit : Fin 10) (length : Nat)
    {band : SectionSixStateBand} {ell n : Nat}
    (s : SectionSixRecurrenceState band ell n)
    (kind : SectionSixStateKind)
    {q : Nat} (hq : q.Prime)
    (horder : ∀ r, r ∈ s.inner → q ≤ r) :
    sectionSixRepeatedPrimeTerm digit length
        (sectionSixStateModulusPNat s) q =
      sectionSixStateWeakTerm digit length
        (sectionSixRepeatedChild s kind q hq horder) (q : Real) := by
  rw [sectionSixRepeatedPrimeTerm_eq_weakSiftedSum digit length
    (sectionSixStateModulusPNat s) hq]
  unfold sectionSixStateWeakTerm sectionSixStateModulusPNat
  apply congrArg (fun d : PNat => sectionSixWeakSiftedSum digit length d (q : Real))
  apply PNat.eq
  simp [Nat.toPNat'_coe, hq.pos]

end

end PrimesRestrictedDigits
