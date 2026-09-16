import PrimesRestrictedDigits.ExceptionalMinorArcs.LocalizedPrimeCellScales

/-!
# Rational scale data from a nonempty canonical frequency cell

A nonempty disjoint Dirichlet fiber transfers the canonical approximation bounds to its finite
key. Empty fibers are handled separately downstream.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- Every nonempty canonical rational cell satisfies the exact scale
hypotheses of repaired Lemma 13.1. -/
theorem exceptionalDirichletBandFiber_scale_bounds
    {length : Nat} (hlength : 0 < length)
    {S : Finset (Fin (10 ^ length))} {key : Nat × Nat}
    (hnonempty : (exceptionalDirichletBandFiber S key).Nonempty) :
    let X : Real := ((10 ^ length : Nat) : Real)
    let Q := exceptionalDirichletDenominatorScaleAt (10 ^ length) key.1
    let E := exceptionalDirichletErrorScaleAt (10 ^ length) key.2
    1 ≤ Q ∧ Q ≤ Real.sqrt X ∧ 0 ≤ E ∧
      E ≤ 100 * Real.sqrt X / Q ∧
        (E = 0 ∨ 1 / X ≤ E) := by
  rcases hnonempty with ⟨h, hh⟩
  have hkey := (mem_exceptionalDirichletBandFiber_iff.mp hh).2
  have hden : exceptionalDirichletDenominatorIndex (10 ^ length) h =
      key.1 := by
    simpa only [exceptionalDirichletBandKey] using congrArg Prod.fst hkey
  have herror : exceptionalDirichletErrorIndex (10 ^ length) h =
      key.2 := by
    simpa only [exceptionalDirichletBandKey] using congrArg Prod.snd hkey
  have hX : 4 ≤ 10 ^ length := by
    have hten : 10 ≤ 10 ^ length := by
      simpa only [pow_one] using
        (pow_le_pow_right₀ (by norm_num : (1 : Nat) ≤ 10)
          (by omega : 1 ≤ length))
    omega
  have hbounds := exceptionalDirichletScales_bounds hX h
  have hQ : exceptionalDirichletDenominatorScaleAt
      (10 ^ length) key.1 =
      exceptionalDirichletDenominatorScale (10 ^ length) h := by
    rw [← hden, exceptionalDirichletDenominatorScaleAt_index]
  have hE : exceptionalDirichletErrorScaleAt (10 ^ length) key.2 =
      exceptionalDirichletErrorScale (10 ^ length) h := by
    rw [← herror, exceptionalDirichletErrorScaleAt_index]
  dsimp only
  rw [hQ, hE]
  exact ⟨hbounds.1, hbounds.2.1, hbounds.2.2.1,
    hbounds.2.2.2.1.le, hbounds.2.2.2.2.imp_right LT.lt.le⟩

end

end PrimesRestrictedDigits
