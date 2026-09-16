import PrimesRestrictedDigits.LatticeEstimates.BranchAggregation

/-!
# Repaired Lemma 14.3

This assembles the two orientation branches, the five-dimensional scale cover, and the
corrected common-`S1` smooth-pair bound. The source typo in equation (14.2) is repaired by
using the exceptional frequency carrier. and `MAYNARD-PRD-PUBLISHED`, Lemma 14.3.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- The smooth-factor sum attached to one admissible five-scale key. -/
noncomputable def latticeLemma14ThreeScaleCell
    (digit : Fin 10) (length : Nat) (P : Real)
    (key : LatticeDecompositionScaleKey length) : Real :=
  latticeExceptionalSmoothPairSum digit length key.qPrimeScale
    key.g1PrimeScale key.g2Scale key.d0Scale key.d1Scale (key.errorScale P)

/-- The finite image of all admissible five-scale cell values. -/
noncomputable def latticeLemma14ThreeScaleCarrier
    (digit : Fin 10) (length : Nat) (P : Real) : Finset Real := by
  classical
  exact (LatticeDecompositionScaleKey.admissibleCarrier length P).image
    (latticeLemma14ThreeScaleCell digit length P)

/-- The zero-adjoined finite maximum of all admissible cell values. -/
noncomputable def latticeLemma14ThreeScaleMaximum
    (digit : Fin 10) (length : Nat) (P : Real) : Real :=
  let values := insert 0 (latticeLemma14ThreeScaleCarrier digit length P)
  values.sup' (Finset.insert_nonempty 0 _) id

theorem latticeLemma14ThreeScaleMaximum_nonneg
    (digit : Fin 10) (length : Nat) (P : Real) :
    0 <= latticeLemma14ThreeScaleMaximum digit length P := by
  unfold latticeLemma14ThreeScaleMaximum
  exact Finset.le_sup' id (Finset.mem_insert_self 0 _)

theorem latticeLemma14ThreeScaleCell_le_maximum
    (digit : Fin 10) (length : Nat) (P : Real)
    (key : LatticeDecompositionScaleKey length)
    (hkey : key ∈ LatticeDecompositionScaleKey.admissibleCarrier length P) :
    latticeLemma14ThreeScaleCell digit length P key <=
      latticeLemma14ThreeScaleMaximum digit length P := by
  unfold latticeLemma14ThreeScaleMaximum
  apply Finset.le_sup' id
  apply Finset.mem_insert_of_mem
  apply Finset.mem_image.mpr
  exact ⟨key, hkey, rfl⟩

/-- Uniform-majorant form of repaired Lemma 14.3.  The factor two is the
explicit orientation loss, and the fifth power is the exact scale-carrier
dimension. -/
theorem latticeGeneratingExceptionalMass_le_of_scale_majorant
    (digit : Fin 10) {length : Nat} (N K delta B : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta)
    (hB : 0 <= B)
    (hmajorant : ∀ key,
      key ∈ LatticeDecompositionScaleKey.admissibleCarrier length (N * K) ->
      latticeLemma14ThreeScaleCell digit length (N * K) key <= B) :
    latticeGeneratingExceptionalMass digit length N K delta <=
      ((2 * (length + 7) ^ 5 : Nat) : Real) * B := by
  have horientation := latticeGeneratingExceptionalMass_le_orientations
    digit N K delta hN hK hdelta hdeltaLower
  have hfirst := latticeFirstOrientedExceptionalMass_le
    digit N K delta B hN hK hdelta hdeltaLower hB hmajorant
  have hsecond := latticeSecondOrientedExceptionalMass_le
    digit N K delta B hN hK hdelta hdeltaLower hB hmajorant
  calc
    latticeGeneratingExceptionalMass digit length N K delta <=
        latticeFirstOrientedExceptionalMass digit N K delta hN hK hdelta
            hdeltaLower +
          latticeSecondOrientedExceptionalMass digit N K delta hN hK hdelta
            hdeltaLower := horientation
    _ <= (((length + 7) ^ 5 : Nat) : Real) * B +
        (((length + 7) ^ 5 : Nat) : Real) * B := add_le_add hfirst hsecond
    _ = ((2 * (length + 7) ^ 5 : Nat) : Real) * B := by
      push_cast
      ring

/-- Total zero-adjoined maximum form of repaired Lemma 14.3, valid for every
natural `length`, including `length=0`. -/
theorem latticeGeneratingExceptionalMass_le_scaleMaximum
    (digit : Fin 10) {length : Nat} (N K delta : Real)
    (hN : 1 <= N) (hK : 1 <= K) (hdelta : 0 < delta)
    (hdeltaLower : N / ((10 ^ length : Nat) : Real) <= delta) :
    latticeGeneratingExceptionalMass digit length N K delta <=
      ((2 * (length + 7) ^ 5 : Nat) : Real) *
        latticeLemma14ThreeScaleMaximum digit length (N * K) := by
  apply latticeGeneratingExceptionalMass_le_of_scale_majorant digit N K delta
    (latticeLemma14ThreeScaleMaximum digit length (N * K)) hN hK hdelta
    hdeltaLower
  · exact latticeLemma14ThreeScaleMaximum_nonneg digit length (N * K)
  · intro key hkey
    exact latticeLemma14ThreeScaleCell_le_maximum digit length (N * K) key hkey

end

end PrimesRestrictedDigits
