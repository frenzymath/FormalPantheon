import PrimesRestrictedDigits.SieveAsymptotics.SectionSixStateOccurrence
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Exact low/high partition of one corrected Section 6 recurrence

The concrete prime interval is split at the pre-child product. Both strict and repeated sums
use the same partition, yielding the exact four families `U/V/RU/RV` with their singleton
state occurrences.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

noncomputable def sectionSixStateLowPrimeInterval
    {band : SectionSixStateBand} {ell : Nat}
    (s : SectionSixAnyState band ell) (R y z : Real) : Finset Nat :=
  (sievePrimeInterval y z).filter fun q =>
    ((s.1 * q : Nat) : Real) ≤ R

noncomputable def sectionSixStateHighPrimeInterval
    {band : SectionSixStateBand} {ell : Nat}
    (s : SectionSixAnyState band ell) (R y z : Real) : Finset Nat :=
  (sievePrimeInterval y z).filter fun q =>
    R < ((s.1 * q : Nat) : Real)

@[simp] theorem mem_sectionSixStateLowPrimeInterval
    {band : SectionSixStateBand} {ell : Nat}
    {s : SectionSixAnyState band ell} {R y z : Real} {q : Nat} :
    q ∈ sectionSixStateLowPrimeInterval s R y z ↔
      q ∈ sievePrimeInterval y z ∧
        ((s.1 * q : Nat) : Real) ≤ R := by
  simp [sectionSixStateLowPrimeInterval]

@[simp] theorem mem_sectionSixStateHighPrimeInterval
    {band : SectionSixStateBand} {ell : Nat}
    {s : SectionSixAnyState band ell} {R y z : Real} {q : Nat} :
    q ∈ sectionSixStateHighPrimeInterval s R y z ↔
      q ∈ sievePrimeInterval y z ∧
        R < ((s.1 * q : Nat) : Real) := by
  simp [sectionSixStateHighPrimeInterval]

theorem sectionSixStateLowPrimeInterval_disjoint_high
    {band : SectionSixStateBand} {ell : Nat}
    (s : SectionSixAnyState band ell) (R y z : Real) :
    Disjoint (sectionSixStateLowPrimeInterval s R y z)
      (sectionSixStateHighPrimeInterval s R y z) := by
  rw [Finset.disjoint_left]
  intro q hqLow hqHigh
  have hlow := (mem_sectionSixStateLowPrimeInterval.mp hqLow).2
  have hhigh := (mem_sectionSixStateHighPrimeInterval.mp hqHigh).2
  exact (not_lt_of_ge hlow) hhigh

theorem sectionSixStateLowPrimeInterval_union_high
    {band : SectionSixStateBand} {ell : Nat}
    (s : SectionSixAnyState band ell) (R y z : Real) :
    sectionSixStateLowPrimeInterval s R y z ∪
        sectionSixStateHighPrimeInterval s R y z =
      sievePrimeInterval y z := by
  ext q
  constructor
  · intro hq
    rcases Finset.mem_union.mp hq with hqLow | hqHigh
    · exact (mem_sectionSixStateLowPrimeInterval.mp hqLow).1
    · exact (mem_sectionSixStateHighPrimeInterval.mp hqHigh).1
  · intro hq
    by_cases hlow : ((s.1 * q : Nat) : Real) ≤ R
    · exact Finset.mem_union_left _
        (mem_sectionSixStateLowPrimeInterval.mpr ⟨hq, hlow⟩)
    · exact Finset.mem_union_right _
        (mem_sectionSixStateHighPrimeInterval.mpr
          ⟨hq, lt_of_not_ge hlow⟩)

theorem sum_sectionSixStatePrimeInterval_eq_low_add_high
    {M : Type*} [AddCommMonoid M]
    {band : SectionSixStateBand} {ell : Nat}
    (s : SectionSixAnyState band ell) (R y z : Real) (f : Nat → M) :
    (∑ q ∈ sievePrimeInterval y z, f q) =
      (∑ q ∈ sectionSixStateLowPrimeInterval s R y z, f q) +
        ∑ q ∈ sectionSixStateHighPrimeInterval s R y z, f q := by
  rw [← sectionSixStateLowPrimeInterval_union_high s R y z]
  exact Finset.sum_union
    (sectionSixStateLowPrimeInterval_disjoint_high s R y z)

theorem sectionSixStateTerm_eq_four_branch_recurrence
    (digit : Fin 10) (length : Nat)
    {band : SectionSixStateBand} {ell : Nat}
    (s : SectionSixAnyState band ell) (R : Real)
    {y z : Real} (hyz : y ≤ z) :
    sectionSixStateStrictTerm digit length s.2 z =
      sectionSixStateStrictTerm digit length s.2 y -
          ((∑ q ∈ sectionSixStateLowPrimeInterval s R y z,
              sectionSixStrictPrimeTerm digit length
                (sectionSixStateModulusPNat s.2) q) +
            ∑ q ∈ sectionSixStateHighPrimeInterval s R y z,
              sectionSixStrictPrimeTerm digit length
                (sectionSixStateModulusPNat s.2) q) -
        ((∑ q ∈ sectionSixStateLowPrimeInterval s R y z,
              sectionSixRepeatedPrimeTerm digit length
                (sectionSixStateModulusPNat s.2) q) +
            ∑ q ∈ sectionSixStateHighPrimeInterval s R y z,
              sectionSixRepeatedPrimeTerm digit length
                (sectionSixStateModulusPNat s.2) q) := by
  unfold sectionSixStateStrictTerm
  rw [sectionSixSiftedSum_eq_sub_strict_sub_repeated digit length
    (sectionSixStateModulusPNat s.2) hyz]
  rw [sum_sectionSixStatePrimeInterval_eq_low_add_high s R y z
      (sectionSixStrictPrimeTerm digit length
        (sectionSixStateModulusPNat s.2)),
    sum_sectionSixStatePrimeInterval_eq_low_add_high s R y z
      (sectionSixRepeatedPrimeTerm digit length
        (sectionSixStateModulusPNat s.2))]

def sectionSixStatePrimeStepTerm
    (digit : Fin 10) (length : Nat)
    {band : SectionSixStateBand} {ell : Nat}
    (s : SectionSixAnyState band ell) (step : SectionSixStateStep) : Real :=
  match step.mode with
  | SectionSixStateStepMode.strict =>
      sectionSixStrictPrimeTerm digit length
        (sectionSixStateModulusPNat s.2) step.q
  | SectionSixStateStepMode.repeated =>
      sectionSixRepeatedPrimeTerm digit length
        (sectionSixStateModulusPNat s.2) step.q

def sectionSixStateChildStepTerm
    (digit : Fin 10) (length : Nat)
    {band : SectionSixStateBand} {ell : Nat}
    (s : SectionSixAnyState band ell) (step : SectionSixStateStep)
    (hq : step.q.Prime)
    (horder : ∀ r, r ∈ s.2.inner → step.q ≤ r) : Real :=
  let child := sectionSixStateStepChild s step hq horder
  match step.mode with
  | SectionSixStateStepMode.strict =>
      sectionSixStateStrictTerm digit length child.2 (step.q : Real)
  | SectionSixStateStepMode.repeated =>
      sectionSixStateWeakTerm digit length child.2 (step.q : Real)

structure SectionSixStatePrimeOccurrence
    (digit : Fin 10) (length : Nat)
    {band : SectionSixStateBand} {ell : Nat}
    (s : SectionSixAnyState band ell) (R y z : Real)
    (step : SectionSixStateStep) : Prop where
  primeMem : step.q ∈ sievePrimeInterval y z
  prime : step.q.Prime
  order : ∀ r, r ∈ s.2.inner → step.q ≤ r
  admissible : sectionSixStateStepAdmissible step
  path : SectionSixStatePath s
    (sectionSixStateStepChild s step prime order) [step]
  cutoff : sectionSixStateCutoffPredicate step.kind R
    (sectionSixStateStepChild s step prime order).1
    (sectionSixStateStepChild s step prime order).2.inner
  term_eq : sectionSixStatePrimeStepTerm digit length s step =
    sectionSixStateChildStepTerm digit length s step prime order

theorem sectionSixStatePrimeOccurrence_of_data
    (digit : Fin 10) (length : Nat)
    {band : SectionSixStateBand} {ell : Nat}
    (s : SectionSixAnyState band ell) (R y z : Real)
    (step : SectionSixStateStep)
    (hmem : step.q ∈ sievePrimeInterval y z)
    (horder : ∀ r, r ∈ s.2.inner → step.q ≤ r)
    (hadmissible : sectionSixStateStepAdmissible step)
    (hcutoff : sectionSixStateStepCutoffData step s.1 R) :
    SectionSixStatePrimeOccurrence digit length s R y z step := by
  have hq : step.q.Prime := (mem_sievePrimeInterval.mp hmem).1
  refine
    { primeMem := hmem
      prime := hq
      order := horder
      admissible := hadmissible
      path := sectionSixStateStep_singleton_path s step hq horder
      cutoff := sectionSixStateStepChild_cutoff s step hq horder hcutoff
      term_eq := ?_ }
  cases step with
  | mk mode kind q =>
      cases mode with
      | strict =>
          simpa [sectionSixStatePrimeStepTerm,
            sectionSixStateChildStepTerm, sectionSixStateStepChild] using
            sectionSixStrictPrimeTerm_eq_stateStrictTerm
              digit length s.2 kind hq horder
      | repeated =>
          simpa [sectionSixStatePrimeStepTerm,
            sectionSixStateChildStepTerm, sectionSixStateStepChild] using
            sectionSixRepeatedPrimeTerm_eq_stateWeakTerm
              digit length s.2 kind hq horder

def sectionSixStateUStep (q : Nat) : SectionSixStateStep :=
  ⟨SectionSixStateStepMode.strict, SectionSixStateKind.U, q⟩

def sectionSixStateVStep (q : Nat) : SectionSixStateStep :=
  ⟨SectionSixStateStepMode.strict, SectionSixStateKind.V, q⟩

def sectionSixStateRUStep (q : Nat) : SectionSixStateStep :=
  ⟨SectionSixStateStepMode.repeated, SectionSixStateKind.RU, q⟩

def sectionSixStateRVStep (q : Nat) : SectionSixStateStep :=
  ⟨SectionSixStateStepMode.repeated, SectionSixStateKind.RV, q⟩

theorem sectionSixStateNextPrime_order
    {band : SectionSixStateBand} {ell : Nat}
    {s : SectionSixAnyState band ell} {y z : Real} {q : Nat}
    (hq : q ∈ sievePrimeInterval y z)
    (hinner : ∀ r, r ∈ s.2.inner → z ≤ (r : Real)) :
    ∀ r, r ∈ s.2.inner → q ≤ r := by
  intro r hr
  have hqr : (q : Real) ≤ (r : Real) :=
    (mem_sievePrimeInterval.mp hq).2.2.trans (hinner r hr)
  exact_mod_cast hqr

theorem sectionSixStateLowPrime_U_occurrence
    (digit : Fin 10) (length : Nat)
    {band : SectionSixStateBand} {ell : Nat}
    (s : SectionSixAnyState band ell) {R y z : Real} {q : Nat}
    (hq : q ∈ sectionSixStateLowPrimeInterval s R y z)
    (hinner : ∀ r, r ∈ s.2.inner → z ≤ (r : Real)) :
    SectionSixStatePrimeOccurrence digit length s R y z
      (sectionSixStateUStep q) := by
  have hdata := mem_sectionSixStateLowPrimeInterval.mp hq
  exact sectionSixStatePrimeOccurrence_of_data digit length s R y z
    (sectionSixStateUStep q) hdata.1
      (sectionSixStateNextPrime_order hdata.1 hinner)
      (by simp [sectionSixStateUStep, sectionSixStateStepAdmissible])
      (by simpa [sectionSixStateUStep, sectionSixStateStepCutoffData] using hdata.2)

theorem sectionSixStateLowPrime_RU_occurrence
    (digit : Fin 10) (length : Nat)
    {band : SectionSixStateBand} {ell : Nat}
    (s : SectionSixAnyState band ell) {R y z : Real} {q : Nat}
    (hq : q ∈ sectionSixStateLowPrimeInterval s R y z)
    (hinner : ∀ r, r ∈ s.2.inner → z ≤ (r : Real)) :
    SectionSixStatePrimeOccurrence digit length s R y z
      (sectionSixStateRUStep q) := by
  have hdata := mem_sectionSixStateLowPrimeInterval.mp hq
  exact sectionSixStatePrimeOccurrence_of_data digit length s R y z
    (sectionSixStateRUStep q) hdata.1
      (sectionSixStateNextPrime_order hdata.1 hinner)
      (by simp [sectionSixStateRUStep, sectionSixStateStepAdmissible])
      (by simpa [sectionSixStateRUStep, sectionSixStateStepCutoffData] using hdata.2)

private theorem sectionSixStateHighPrime_upper
    {band : SectionSixStateBand} {ell : Nat}
    (s : SectionSixAnyState band ell) {R : Real} {q : Nat}
    (hsR : (s.1 : Real) ≤ R) :
    ((s.1 * q : Nat) : Real) ≤ R * (q : Real) := by
  rw [Nat.cast_mul]
  exact mul_le_mul_of_nonneg_right hsR (Nat.cast_nonneg q)

theorem sectionSixStateHighPrime_V_occurrence
    (digit : Fin 10) (length : Nat)
    {band : SectionSixStateBand} {ell : Nat}
    (s : SectionSixAnyState band ell) {R y z : Real} {q : Nat}
    (hq : q ∈ sectionSixStateHighPrimeInterval s R y z)
    (hsR : (s.1 : Real) ≤ R)
    (hinner : ∀ r, r ∈ s.2.inner → z ≤ (r : Real)) :
    SectionSixStatePrimeOccurrence digit length s R y z
      (sectionSixStateVStep q) := by
  have hdata := mem_sectionSixStateHighPrimeInterval.mp hq
  exact sectionSixStatePrimeOccurrence_of_data digit length s R y z
    (sectionSixStateVStep q) hdata.1
      (sectionSixStateNextPrime_order hdata.1 hinner)
      (by simp [sectionSixStateVStep, sectionSixStateStepAdmissible])
      (by
        simpa [sectionSixStateVStep, sectionSixStateStepCutoffData] using
          And.intro hdata.2 (sectionSixStateHighPrime_upper s hsR))

theorem sectionSixStateHighPrime_RV_occurrence
    (digit : Fin 10) (length : Nat)
    {band : SectionSixStateBand} {ell : Nat}
    (s : SectionSixAnyState band ell) {R y z : Real} {q : Nat}
    (hq : q ∈ sectionSixStateHighPrimeInterval s R y z)
    (hsR : (s.1 : Real) ≤ R)
    (hinner : ∀ r, r ∈ s.2.inner → z ≤ (r : Real)) :
    SectionSixStatePrimeOccurrence digit length s R y z
      (sectionSixStateRVStep q) := by
  have hdata := mem_sectionSixStateHighPrimeInterval.mp hq
  exact sectionSixStatePrimeOccurrence_of_data digit length s R y z
    (sectionSixStateRVStep q) hdata.1
      (sectionSixStateNextPrime_order hdata.1 hinner)
      (by simp [sectionSixStateRVStep, sectionSixStateStepAdmissible])
      (by
        simpa [sectionSixStateRVStep, sectionSixStateStepCutoffData] using
          And.intro hdata.2 (sectionSixStateHighPrime_upper s hsR))

end

end PrimesRestrictedDigits
