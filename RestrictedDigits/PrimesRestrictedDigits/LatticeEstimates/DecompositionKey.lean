import PrimesRestrictedDigits.LatticeEstimates.DecompositionScales

/-!
# Five-factor decimal scale keys

This is the finite scale carrier in the repaired proof of `MAYNARD-PRD-PUBLISHED`, Lemma 14.3.
Its five coordinates record the factor-ten exponents of `q'`, `g'_1`, `g_2`, `d_0`, and `d_1`;
the error scale is then a deterministic function of this key.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- The five decimal exponents used to localize one oriented denominator
factorization. -/
@[ext]
structure LatticeDecompositionScaleKey (length : Nat) where
  qPrimeIndex : Fin (length + 7)
  g1PrimeIndex : Fin (length + 7)
  g2Index : Fin (length + 7)
  d0Index : Fin (length + 7)
  d1Index : Fin (length + 7)
deriving DecidableEq, Fintype

namespace LatticeDecompositionScaleKey

/-- The scale attached to `q'`. -/
def qPrimeScale {length : Nat} (key : LatticeDecompositionScaleKey length) : Nat :=
  10 ^ key.qPrimeIndex.val

/-- The scale attached to `g'_1`. -/
def g1PrimeScale {length : Nat} (key : LatticeDecompositionScaleKey length) : Nat :=
  10 ^ key.g1PrimeIndex.val

/-- The scale attached to `g_2`. -/
def g2Scale {length : Nat} (key : LatticeDecompositionScaleKey length) : Nat :=
  10 ^ key.g2Index.val

/-- The scale attached to the common decimal-smooth factor `d_0`. -/
def d0Scale {length : Nat} (key : LatticeDecompositionScaleKey length) : Nat :=
  10 ^ key.d0Index.val

/-- The scale attached to the first-coordinate decimal-smooth factor `d_1`. -/
def d1Scale {length : Nat} (key : LatticeDecompositionScaleKey length) : Nat :=
  10 ^ key.d1Index.val

/-- The product `Q_0` of the five upper factor-ten scales. -/
def denominatorScale {length : Nat}
    (key : LatticeDecompositionScaleKey length) : Nat :=
  key.qPrimeScale * key.g1PrimeScale * key.g2Scale * key.d0Scale * key.d1Scale

/-- The real target `10^11 X / (P Q_0)` which determines the error scale. -/
def errorTarget {length : Nat}
    (key : LatticeDecompositionScaleKey length) (P : Real) : Real :=
  (((10 ^ 11 : Nat) : Real) * ((10 ^ length : Nat) : Real)) /
    (P * (key.denominatorScale : Real))

/-- The deterministic exponent attached to the error target. -/
noncomputable def errorScaleIndex {length : Nat}
    (key : LatticeDecompositionScaleKey length) (P : Real) : Nat :=
  latticePositiveRealFactorTenExponent (key.errorTarget P)

/-- The deterministic power-of-ten error scale attached to a five-scale key. -/
noncomputable def errorScale {length : Nat}
    (key : LatticeDecompositionScaleKey length) (P : Real) : Nat :=
  10 ^ key.errorScaleIndex P

/-- The two scale inequalities required by the downstream Lemma 14.4 bound.
The exact power-of-ten shape of every scale is already built into the key. -/
def IsAdmissible {length : Nat}
    (key : LatticeDecompositionScaleKey length) (P : Real) : Prop :=
  ((((key.errorScale P * key.denominatorScale : Nat) : Real) <=
      ((10 ^ 12 : Nat) : Real) * ((10 ^ length : Nat) : Real) / P) ∧
    ((key.g1PrimeScale : Real) <=
      ((10 ^ 12 : Nat) : Real) * (key.g2Scale : Real)))

/-- A tuple presentation used only to calculate the carrier cardinality. -/
private def tupleEquiv (length : Nat) :
    LatticeDecompositionScaleKey length ≃
      Fin (length + 7) ×
        (Fin (length + 7) ×
          (Fin (length + 7) × (Fin (length + 7) × Fin (length + 7)))) where
  toFun key :=
    (key.qPrimeIndex,
      (key.g1PrimeIndex, (key.g2Index, (key.d0Index, key.d1Index))))
  invFun data :=
    { qPrimeIndex := data.1
      g1PrimeIndex := data.2.1
      g2Index := data.2.2.1
      d0Index := data.2.2.2.1
      d1Index := data.2.2.2.2 }
  left_inv _ := rfl
  right_inv _ := rfl

/-- There are exactly `(length+7)^5` five-factor scale keys. -/
theorem card (length : Nat) :
    Fintype.card (LatticeDecompositionScaleKey length) = (length + 7) ^ 5 := by
  rw [Fintype.card_congr (tupleEquiv length)]
  simp only [Fintype.card_prod, Fintype.card_fin]
  ring

/-- The finite carrier of scale keys satisfying the downstream inequalities. -/
noncomputable def admissibleCarrier (length : Nat) (P : Real) :
    Finset (LatticeDecompositionScaleKey length) := by
  classical
  exact Finset.univ.filter fun key => key.IsAdmissible P

theorem mem_admissibleCarrier_iff
    {length : Nat} {P : Real} {key : LatticeDecompositionScaleKey length} :
    key ∈ admissibleCarrier length P ↔ key.IsAdmissible P := by
  classical
  simp [admissibleCarrier]

/-- Filtering by admissibility cannot increase the five-dimensional cover. -/
theorem card_admissibleCarrier_le (length : Nat) (P : Real) :
    (admissibleCarrier length P).card <= (length + 7) ^ 5 := by
  classical
  calc
    (admissibleCarrier length P).card <=
        (Finset.univ : Finset (LatticeDecompositionScaleKey length)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = (length + 7) ^ 5 := by
      rw [Finset.card_univ, card]

end LatticeDecompositionScaleKey

end

end PrimesRestrictedDigits
