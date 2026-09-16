import PrimesRestrictedDigits.SieveAsymptotics.TypeIIStableLabeledFactorization

/-!
# Positions in the stable labelled factor tuple

The stable sort keeps the source labels of the outer tuple and of the residual prime-factor
list. This file exposes the residual half of that partition and the finite label facts used by
the strict near adapters. The labels are retained deliberately: equal factor values are still
distinct coordinates, while no order between an arbitrary outer and residual value is claimed.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- The sorted position occupied by a residual prime-factor-list label. -/
def typeIIStableResidualPositionEmbedding {ell : Nat}
    (outer : Fin ell → Nat) (m : Nat) :
    Fin m.primeFactorsList.length ↪
      Fin (ell + m.primeFactorsList.length) :=
  { toFun := fun j =>
      (typeIIStableFactorPermutation outer m).symm (Fin.natAdd ell j)
    inj' := by
      intro i j hij
      apply Fin.ext
      have h := congrArg (typeIIStableFactorPermutation outer m) hij
      exact congrArg Fin.val (by simpa using h) }

/-- Recovery of an outer value through its public stable position embedding. -/
theorem typeIIStableFactorTuple_at_outerPositionEmbedding {ell : Nat}
    (outer : Fin ell → Nat) (m : Nat) (i : Fin ell) :
    typeIIStableFactorTuple outer m
        (typeIIStableOuterPositionEmbedding outer m i) = outer i := by
  simpa [typeIIStableOuterPositionEmbedding] using
    typeIIStableFactorTuple_at_outerPosition outer m i

/-- Recovery of a residual value through its stable position embedding. -/
theorem typeIIStableFactorTuple_at_residualPosition {ell : Nat}
    (outer : Fin ell → Nat) (m : Nat)
    (j : Fin m.primeFactorsList.length) :
    typeIIStableFactorTuple outer m
        (typeIIStableResidualPositionEmbedding outer m j) =
      m.primeFactorsList.get j := by
  simp [typeIIStableResidualPositionEmbedding, typeIIStableFactorTuple,
    typeIICombinedLabeledFactors, Function.comp_apply]

/-- An outer label and a residual label occupy different sorted positions. -/
theorem typeIIStableOuterPosition_ne_residualPosition {ell : Nat}
    (outer : Fin ell → Nat) (m : Nat) (i : Fin ell)
    (j : Fin m.primeFactorsList.length) :
    typeIIStableOuterPositionEmbedding outer m i ≠
      typeIIStableResidualPositionEmbedding outer m j := by
  intro h
  have hlabels :
      (Fin.castAdd m.primeFactorsList.length i :
          Fin (ell + m.primeFactorsList.length)) =
        Fin.natAdd ell j := by
    apply (typeIIStableFactorPermutation outer m).symm.injective
    exact h
  have hvals := congrArg Fin.val hlabels
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hvals
  omega

/-- Every sorted position comes from exactly one side of the labelled input. -/
theorem typeIIStablePosition_cases {ell : Nat}
    (outer : Fin ell → Nat) (m : Nat)
    (k : Fin (ell + m.primeFactorsList.length)) :
    (∃ i, typeIIStableOuterPositionEmbedding outer m i = k) ∨
      (∃ j, typeIIStableResidualPositionEmbedding outer m j = k) := by
  let σ := typeIIStableFactorPermutation outer m
  let source := σ k
  by_cases houter : source.val < ell
  · left
    let i : Fin ell := ⟨source.val, houter⟩
    refine ⟨i, ?_⟩
    have hsource :
        (Fin.castAdd m.primeFactorsList.length i :
            Fin (ell + m.primeFactorsList.length)) = source := by
      apply Fin.ext
      simp [source, i]
    change σ.symm (Fin.castAdd m.primeFactorsList.length i) = k
    rw [hsource]
    simp [source]
  · right
    have houterLe : ell ≤ source.val := Nat.le_of_not_gt houter
    have hsourceLt : source.val < ell + m.primeFactorsList.length := source.isLt
    have hresidual : source.val - ell < m.primeFactorsList.length := by
      omega
    let j : Fin m.primeFactorsList.length := ⟨source.val - ell, hresidual⟩
    refine ⟨j, ?_⟩
    have hsource :
        (Fin.natAdd ell j : Fin (ell + m.primeFactorsList.length)) = source := by
      apply Fin.ext
      simp [source, j]
      omega
    change σ.symm (Fin.natAdd ell j) = k
    rw [hsource]
    simp [source]

/-- The ranges of outer and residual stable positions are disjoint. -/
theorem typeIIStableOuterPositionEmbedding_range_disjoint {ell : Nat}
    (outer : Fin ell → Nat) (m : Nat) :
    Disjoint (Set.range (typeIIStableOuterPositionEmbedding outer m))
      (Set.range (typeIIStableResidualPositionEmbedding outer m)) := by
  refine Set.disjoint_left.2 ?_
  intro k houter hresidual
  rcases houter with ⟨i, hi⟩
  rcases hresidual with ⟨j, hj⟩
  apply typeIIStableOuterPosition_ne_residualPosition outer m i j
  exact hi.trans hj.symm

/-- An outer position precedes a residual position when its value is no larger.

There is intentionally no unconditional ordering assertion: a smaller
residual factor can occur before a larger outer factor.
-/
theorem typeIIStableOuterPosition_lt_residualPosition_of_le {ell : Nat}
    (outer : Fin ell → Nat) (m : Nat) {i : Fin ell}
    {j : Fin m.primeFactorsList.length}
    (hle : outer i ≤ m.primeFactorsList.get j) :
    typeIIStableOuterPositionEmbedding outer m i <
      typeIIStableResidualPositionEmbedding outer m j := by
  let a := typeIIStableOuterPositionEmbedding outer m i
  let b := typeIIStableResidualPositionEmbedding outer m j
  have hab : a ≠ b := by
    exact typeIIStableOuterPosition_ne_residualPosition outer m i j
  rcases lt_or_eq_of_le hle with hlt | heq
  · apply lt_of_not_ge
    intro hba
    have hmono := monotone_typeIIStableFactorTuple outer m hba
    have hvalue : m.primeFactorsList.get j ≤ outer i := by
      simpa [a, b, typeIIStableFactorTuple_at_outerPositionEmbedding,
        typeIIStableFactorTuple_at_residualPosition] using hmono
    exact (Nat.not_lt_of_ge hvalue) hlt
  · rcases lt_or_gt_of_ne hab with hablt | hblt
    · exact hablt
    · have htuple :
          typeIIStableFactorTuple outer m a =
            typeIIStableFactorTuple outer m b := by
        calc
          typeIIStableFactorTuple outer m a = outer i := by
            simpa [a] using
              typeIIStableFactorTuple_at_outerPositionEmbedding outer m i
          _ = m.primeFactorsList.get j := heq
          _ = typeIIStableFactorTuple outer m b := by
            symm
            simpa [b] using
              typeIIStableFactorTuple_at_residualPosition outer m j
      have hordered := typeIIStableOuterPosition_lt_residualPosition_of_eq
        outer m htuple
      exact (Nat.lt_asymm hordered hblt).elim

end

end PrimesRestrictedDigits
