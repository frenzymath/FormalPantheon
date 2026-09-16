import PrimesRestrictedDigits.SieveAsymptotics.SectionSixStatePathFuel
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixStateRecurrencePartition

/-!
# Thresholded strict-low paths for the corrected Section 6 recurrence

An active node packages exactly the range and cutoff invariants needed to continue through a
strict low `U` child. Repeated and high children remain terminal leaves for this layer.
-/

namespace PrimesRestrictedDigits

noncomputable section

/- A general append lemma is useful when a structural path is followed by a
   final hypothetical child.  It makes no occurrence claim about source sums. -/
theorem sectionSixStatePath_append
    {band : SectionSixStateBand} {ell : Nat}
    {start middle target : SectionSixAnyState band ell}
    {steps₁ steps₂ : List SectionSixStateStep}
    (h₁ : SectionSixStatePath start middle steps₁)
    (h₂ : SectionSixStatePath middle target steps₂) :
    SectionSixStatePath start target (steps₁ ++ steps₂) := by
  induction h₁ with
  | nil s => simpa using h₂
  | @strict s middle rest step hmode hq horder tail ih =>
      simp only [List.cons_append]
      exact SectionSixStatePath.strict step hmode hq horder (ih h₂)
  | @repeated s middle rest step hmode hq horder tail ih =>
      simp only [List.cons_append]
      exact SectionSixStatePath.repeated step hmode hq horder (ih h₂)

structure SectionSixLowActiveNode
    (X delta theta R y : Real)
    (band : SectionSixStateBand) (ell : Nat) where
  upper : Real
  state : SectionSixAnyState band ell
  y_eq : y = X ^ delta
  R_le_X : R ≤ X
  lower_le_upper : y ≤ upper
  upper_le_range : upper ≤ X ^ theta
  modulus_le : (state.1 : Real) ≤ R
  ordered : ∀ r, r ∈ state.2.inner → upper ≤ (r : Real)
  innerRange : sectionSixStateInnerRange X delta theta state.2.inner
  outerLower : ∀ i, X ^ delta ≤ (state.2.outer i : Real)
  activeKind : state.2.kind = .T ∨ state.2.kind = .U

theorem sectionSixLowActivePrime
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    (node : SectionSixLowActiveNode X delta theta R y band ell)
    {q : Nat}
    (hq : q ∈ sectionSixStateLowPrimeInterval node.state R y node.upper) :
    q.Prime := by
  exact (mem_sievePrimeInterval.mp
    (mem_sectionSixStateLowPrimeInterval.mp hq).1).1

theorem sectionSixLowActiveOrder
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    (node : SectionSixLowActiveNode X delta theta R y band ell)
    {q : Nat}
    (hq : q ∈ sectionSixStateLowPrimeInterval node.state R y node.upper) :
    ∀ r, r ∈ node.state.2.inner → q ≤ r := by
  exact sectionSixStateNextPrime_order
    (mem_sectionSixStateLowPrimeInterval.mp hq).1 node.ordered

noncomputable def sectionSixLowActiveChild
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    (node : SectionSixLowActiveNode X delta theta R y band ell)
    (q : Nat)
    (hq : q ∈ sectionSixStateLowPrimeInterval node.state R y node.upper) :
    SectionSixLowActiveNode X delta theta R y band ell := by
  let hdata := mem_sectionSixStateLowPrimeInterval.mp hq
  let hinterval := mem_sievePrimeInterval.mp hdata.1
  let hprime := sectionSixLowActivePrime node hq
  let horder := sectionSixLowActiveOrder node hq
  have hqRange : X ^ delta < (q : Real) ∧ (q : Real) ≤ X ^ theta := by
    constructor
    · rw [← node.y_eq]
      exact hinterval.2.1
    · exact hinterval.2.2.trans node.upper_le_range
  have hchildInnerRange :
      sectionSixStateInnerRange X delta theta
        (sectionSixStrictChild node.state.2 SectionSixStateKind.U q
          hprime horder).inner :=
    sectionSixStrictChild_innerRange node.state.2 q hqRange
      node.innerRange
  have hchildOrdered :
      ∀ r, r ∈
        (sectionSixStrictChild node.state.2 SectionSixStateKind.U q
          hprime horder).inner → q ≤ r := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact le_rfl
    · exact horder r hr
  exact
    { upper := q
      state := ⟨node.state.1 * q,
        sectionSixStrictChild node.state.2 SectionSixStateKind.U q
          hprime horder⟩
      y_eq := node.y_eq
      R_le_X := node.R_le_X
      lower_le_upper := le_of_lt hinterval.2.1
      upper_le_range := hinterval.2.2.trans node.upper_le_range
      modulus_le := hdata.2
      ordered := by
        intro r hr
        exact_mod_cast hchildOrdered r hr
      innerRange := hchildInnerRange
      outerLower := node.outerLower
      activeKind := Or.inr rfl }

@[simp] theorem sectionSixLowActiveChild_state
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    (node : SectionSixLowActiveNode X delta theta R y band ell)
    (q : Nat)
    (hq : q ∈ sectionSixStateLowPrimeInterval node.state R y node.upper) :
    (sectionSixLowActiveChild node q hq).state =
      ⟨node.state.1 * q,
        sectionSixStrictChild node.state.2 SectionSixStateKind.U q
          (sectionSixLowActivePrime node hq)
          (sectionSixLowActiveOrder node hq)⟩ := rfl

inductive SectionSixLowStrictPath
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat} :
    SectionSixLowActiveNode X delta theta R y band ell →
      SectionSixLowActiveNode X delta theta R y band ell →
        List Nat → Prop
  | nil (node : SectionSixLowActiveNode X delta theta R y band ell) :
      SectionSixLowStrictPath node node []
  | cons {node target : SectionSixLowActiveNode X delta theta R y band ell}
      {rest : List Nat} {q : Nat}
      (hq : q ∈ sectionSixStateLowPrimeInterval node.state R y node.upper)
      (tail : SectionSixLowStrictPath
        (sectionSixLowActiveChild node q hq) target rest) :
      SectionSixLowStrictPath node target (q :: rest)

theorem sectionSixLowStrictPath_append
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {start middle target : SectionSixLowActiveNode X delta theta R y band ell}
    {steps₁ steps₂ : List Nat}
    (h₁ : SectionSixLowStrictPath start middle steps₁)
    (h₂ : SectionSixLowStrictPath middle target steps₂) :
    SectionSixLowStrictPath start target (steps₁ ++ steps₂) := by
  induction h₁ with
  | nil node => simpa using h₂
  | @cons node middle rest q hq tail ih =>
      simp only [List.cons_append]
      exact SectionSixLowStrictPath.cons hq (ih h₂)

theorem sectionSixLowStrictPath_to_statePath
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {start target : SectionSixLowActiveNode X delta theta R y band ell}
    {steps : List Nat}
    (hpath : SectionSixLowStrictPath start target steps) :
    SectionSixStatePath start.state target.state
      (steps.map sectionSixStateUStep) := by
  induction hpath with
  | nil node => exact SectionSixStatePath.nil _
  | @cons node target rest q hq tail ih =>
      simp only [List.map_cons]
      exact SectionSixStatePath.strict (sectionSixStateUStep q) rfl
        (sectionSixLowActivePrime node hq)
        (sectionSixLowActiveOrder node hq) (by
          simpa only [sectionSixLowActiveChild_state, sectionSixStateUStep] using ih)

theorem sectionSixLowStrictPath_length_le_ceil_inv_delta
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {start target : SectionSixLowActiveNode X delta theta R y band ell}
    {steps : List Nat}
    (hX : 1 < X) (hdelta : 0 < delta)
    (hpath : SectionSixLowStrictPath start target steps) :
    steps.length ≤ Nat.ceil (1 / delta) := by
  have h := sectionSixStatePath_length_le_ceil_inv_delta hX hdelta
    (sectionSixLowStrictPath_to_statePath hpath)
    (target.modulus_le.trans target.R_le_X)
    target.outerLower target.innerRange
  simpa only [List.length_map] using h

theorem sectionSixLowStrictPath_lowPrimeInterval_eq_empty_of_length_eq_ceil_inv_delta
    {X delta theta R y : Real}
    {band : SectionSixStateBand} {ell : Nat}
    {start target : SectionSixLowActiveNode X delta theta R y band ell}
    {steps : List Nat}
    (hX : 1 < X) (hdelta : 0 < delta)
    (hpath : SectionSixLowStrictPath start target steps)
    (hmax : steps.length = Nat.ceil (1 / delta)) :
    sectionSixStateLowPrimeInterval target.state R y target.upper = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hnonempty
  rcases hnonempty with ⟨q, hq⟩
  have hsingle :
      SectionSixLowStrictPath target
        (sectionSixLowActiveChild target q hq) [q] := by
    exact SectionSixLowStrictPath.cons hq
      (SectionSixLowStrictPath.nil _)
  have hext := sectionSixLowStrictPath_append hpath hsingle
  have hbound := sectionSixLowStrictPath_length_le_ceil_inv_delta
    hX hdelta hext
  simp only [List.length_append, List.length_singleton] at hbound
  omega

end

end PrimesRestrictedDigits
