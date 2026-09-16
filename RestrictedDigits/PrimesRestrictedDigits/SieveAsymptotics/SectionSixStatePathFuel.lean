import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFactorLengthBound
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixStatePath
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

/-!
# Exact fuel for corrected Section 6 paths

The complete modulus records every outer and inner prime, including both copies introduced by
a repeated correction. Fixed-delta factor length then gives a finite path fuel certificate.
-/

namespace PrimesRestrictedDigits

noncomputable section

theorem sectionSixRecurrenceState_primeFactorsList_length
    {band : SectionSixStateBand} {ell n : Nat}
    (s : SectionSixRecurrenceState band ell n) :
    n.primeFactorsList.length = ell + s.inner.length := by
  have hperm :
      (List.ofFn s.outer ++ s.inner).Perm n.primeFactorsList := by
    apply Nat.primeFactorsList_unique
    · rw [List.prod_append, List.prod_ofFn]
      simpa only [primeTupleProduct] using s.product_eq
    · exact List.forall_mem_append.2
        ⟨List.forall_mem_ofFn_iff.2 s.outerPrime, s.innerPrime⟩
  have hlength := hperm.length_eq
  simpa only [List.length_append, List.length_ofFn] using hlength.symm

theorem sectionSixStatePath_length_le_count
    (steps : List SectionSixStateStep) :
    steps.length ≤ sectionSixStatePathCount steps := by
  induction steps with
  | nil => simp [sectionSixStatePathCount]
  | cons step rest ih =>
      rcases step with ⟨mode, kind, q⟩
      cases mode <;>
        simp only [List.length_cons, sectionSixStatePathCount,
          SectionSixStateStep.count] <;>
        omega

theorem sectionSixStatePath_factorCount_le_ceil_inv_delta
    {band : SectionSixStateBand} {ell : Nat}
    {start target : SectionSixAnyState band ell}
    {steps : List SectionSixStateStep}
    {X delta theta : Real}
    (hX : 1 < X) (hdelta : 0 < delta)
    (hpath : SectionSixStatePath start target steps)
    (htargetX : (target.1 : Real) ≤ X)
    (houter : ∀ i, X ^ delta ≤ (target.2.outer i : Real))
    (hinner : sectionSixStateInnerRange X delta theta target.2.inner) :
    ell + start.2.inner.length + sectionSixStatePathCount steps ≤
      Nat.ceil (1 / delta) := by
  have hfactor :
      target.1.primeFactorsList.length ≤ Nat.ceil (1 / delta) :=
    sectionSixRecurrenceState_factorLength_le_ceil_inv_delta
      hX hdelta target.2 htargetX houter hinner
  rw [sectionSixRecurrenceState_primeFactorsList_length target.2,
    sectionSixStatePath_inner_length hpath] at hfactor
  simpa only [Nat.add_assoc] using hfactor

theorem sectionSixStatePath_length_le_ceil_inv_delta
    {band : SectionSixStateBand} {ell : Nat}
    {start target : SectionSixAnyState band ell}
    {steps : List SectionSixStateStep}
    {X delta theta : Real}
    (hX : 1 < X) (hdelta : 0 < delta)
    (hpath : SectionSixStatePath start target steps)
    (htargetX : (target.1 : Real) ≤ X)
    (houter : ∀ i, X ^ delta ≤ (target.2.outer i : Real))
    (hinner : sectionSixStateInnerRange X delta theta target.2.inner) :
    steps.length ≤ Nat.ceil (1 / delta) := by
  have hcount := sectionSixStatePath_length_le_count steps
  have hfuel := sectionSixStatePath_factorCount_le_ceil_inv_delta
    hX hdelta hpath htargetX houter hinner
  omega

end

end PrimesRestrictedDigits
