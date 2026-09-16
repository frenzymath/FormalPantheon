import PrimesRestrictedDigits.SieveAsymptotics.SectionSixOneStepState

/-!
# Finite paths of corrected Section 6 states

The path relation is a structural enumeration interface for the strict and repeated child
constructors. It makes no claim that an arbitrary path occurs in the Buchstab expansion.
-/

namespace PrimesRestrictedDigits

noncomputable section

inductive SectionSixStateStepMode
  | strict
  | repeated
  deriving DecidableEq

structure SectionSixStateStep where
  mode : SectionSixStateStepMode
  kind : SectionSixStateKind
  q : Nat

/- A sigma package keeps the changing natural modulus and the dependent state
   together while a path is traversed. -/
def SectionSixAnyState (band : SectionSixStateBand) (ell : Nat) :=
  Sigma (fun n : Nat => SectionSixRecurrenceState band ell n)

inductive SectionSixStatePath {band : SectionSixStateBand} {ell : Nat} :
    SectionSixAnyState band ell -> SectionSixAnyState band ell ->
      List SectionSixStateStep -> Prop
  | nil (s : SectionSixAnyState band ell) :
      SectionSixStatePath s s []
  | strict {s target : SectionSixAnyState band ell} {rest : List SectionSixStateStep}
      (step : SectionSixStateStep) (hmode : step.mode = SectionSixStateStepMode.strict)
      (hq : step.q.Prime)
      (horder : ∀ r, r ∈ s.2.inner → step.q ≤ r)
      (tail : SectionSixStatePath
        ⟨s.1 * step.q,
          sectionSixStrictChild s.2 step.kind step.q hq horder⟩ target rest) :
      SectionSixStatePath s target (step :: rest)
  | repeated {s target : SectionSixAnyState band ell} {rest : List SectionSixStateStep}
      (step : SectionSixStateStep) (hmode : step.mode = SectionSixStateStepMode.repeated)
      (hq : step.q.Prime)
      (horder : ∀ r, r ∈ s.2.inner → step.q ≤ r)
      (tail : SectionSixStatePath
        ⟨s.1 * step.q * step.q,
          sectionSixRepeatedChild s.2 step.kind step.q hq horder⟩ target rest) :
      SectionSixStatePath s target (step :: rest)

def SectionSixStateStep.count : SectionSixStateStep → Nat
  | ⟨SectionSixStateStepMode.strict, _, _⟩ => 1
  | ⟨SectionSixStateStepMode.repeated, _, _⟩ => 2

def sectionSixStatePathCount : List SectionSixStateStep → Nat
  | [] => 0
  | s :: rest => SectionSixStateStep.count s + sectionSixStatePathCount rest

def SectionSixStateStep.multiplier : SectionSixStateStep → Nat
  | ⟨SectionSixStateStepMode.strict, _, q⟩ => q
  | ⟨SectionSixStateStepMode.repeated, _, q⟩ => q * q

def sectionSixStatePathMultiplier : List SectionSixStateStep → Nat
  | [] => 1
  | s :: rest =>
      SectionSixStateStep.multiplier s * sectionSixStatePathMultiplier rest

theorem sectionSixStatePath_inner_length
    {band : SectionSixStateBand} {ell : Nat}
    {start target : SectionSixAnyState band ell}
    {steps : List SectionSixStateStep}
    (hpath : SectionSixStatePath start target steps) :
    target.2.inner.length =
      start.2.inner.length + sectionSixStatePathCount steps := by
  induction hpath with
  | nil s => simp [sectionSixStatePathCount]
  | @strict s target rest step hmode hq horder tail ih =>
      simp only [sectionSixStatePathCount]
      cases step with
      | mk mode kind q =>
          simp_all [SectionSixStateStep.count, sectionSixStrictChild]
          omega
  | @repeated s target rest step hmode hq horder tail ih =>
      simp only [sectionSixStatePathCount]
      cases step with
      | mk mode kind q =>
          simp_all [SectionSixStateStep.count, sectionSixRepeatedChild]
          omega

theorem sectionSixStatePath_end_modulus
    {band : SectionSixStateBand} {ell : Nat}
    {start target : SectionSixAnyState band ell}
    {steps : List SectionSixStateStep}
    (hpath : SectionSixStatePath start target steps) :
    target.1 = start.1 * sectionSixStatePathMultiplier steps := by
  induction hpath with
  | nil s => simp [sectionSixStatePathMultiplier]
  | @strict s target rest step hmode hq horder tail ih =>
      cases step with
      | mk mode kind q =>
          simp_all [SectionSixStateStep.multiplier,
            sectionSixStatePathMultiplier]
          simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  | @repeated s target rest step hmode hq horder tail ih =>
      cases step with
      | mk mode kind q =>
          simp_all [SectionSixStateStep.multiplier,
            sectionSixStatePathMultiplier]
          simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

theorem sectionSixStatePath_inner_range
    {band : SectionSixStateBand} {ell : Nat}
    {start target : SectionSixAnyState band ell}
    {steps : List SectionSixStateStep} {X delta theta : Real}
    (hstart : sectionSixStateInnerRange X delta theta start.2.inner)
    (hstepRange : ∀ step ∈ steps,
      X ^ delta < (step.q : Real) ∧ (step.q : Real) ≤ X ^ theta)
    (hpath : SectionSixStatePath start target steps) :
    sectionSixStateInnerRange X delta theta target.2.inner := by
  induction hpath with
  | nil s => exact hstart
  | @strict s target rest step hmode hq horder tail ih =>
      have hqRange := hstepRange step (by simp)
      have hrest : ∀ u ∈ rest,
          X ^ delta < (u.q : Real) ∧ (u.q : Real) ≤ X ^ theta := by
        intro u hu
        exact hstepRange u (by simp [hu])
      have hchild := sectionSixStrictChild_innerRange
        s.2 step.q hqRange hstart
      exact ih hchild hrest
  | @repeated s target rest step hmode hq horder tail ih =>
      have hqRange := hstepRange step (by simp)
      have hrest : ∀ u ∈ rest,
          X ^ delta < (u.q : Real) ∧ (u.q : Real) ≤ X ^ theta := by
        intro u hu
        exact hstepRange u (by simp [hu])
      have hchild := sectionSixRepeatedChild_innerRange
        s.2 step.q hqRange hstart
      exact ih hchild hrest
end

end PrimesRestrictedDigits
