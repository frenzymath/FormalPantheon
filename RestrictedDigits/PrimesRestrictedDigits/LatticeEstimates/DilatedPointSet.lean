import PrimesRestrictedDigits.LatticeEstimates.DilatedLattice

/-!
# Transporting finite integer point sets through dilation

The construction preserves the exact cardinality needed in the repaired
proof of `MAYNARD-PRD-PUBLISHED`, Lemma 14.1.
-/

noncomputable section

namespace PrimesRestrictedDigits

private abbrev E := EuclideanSpace Real (Fin 3)

/-- Inject the attached integer points into the dilated image lattice. -/
def dilatedPointEmbedding (Lambda : RankTwoIntegralLattice)
    (S : Finset (Fin 3 -> Int))
    (hS : forall z, z ∈ S -> intVectorToEuclidean z ∈ Lambda.carrier)
    (u : E) (t : Real) (hu : u ≠ 0) (ht : t ≠ 0) :
    {z // z ∈ S} ↪ directionallyDilatedLattice Lambda u t hu ht where
  toFun z := directionallyDilatedLatticeEquiv Lambda u t hu ht
    ⟨intVectorToEuclidean z, hS z z.property⟩
  inj' := by
    intro z w hzw
    apply Subtype.ext
    apply intVectorToEuclidean_injective
    have hsource := (directionallyDilatedLatticeEquiv Lambda u t hu ht).injective hzw
    exact congrArg Subtype.val hsource

/-- The finite image of `S` in the dilated lattice. -/
def dilatedPointSet (Lambda : RankTwoIntegralLattice)
    (S : Finset (Fin 3 -> Int))
    (hS : forall z, z ∈ S -> intVectorToEuclidean z ∈ Lambda.carrier)
    (u : E) (t : Real) (hu : u ≠ 0) (ht : t ≠ 0) :
    Finset (directionallyDilatedLattice Lambda u t hu ht) :=
  S.attach.map (dilatedPointEmbedding Lambda S hS u t hu ht)

@[simp] theorem card_dilatedPointSet
    (Lambda : RankTwoIntegralLattice)
    (S : Finset (Fin 3 -> Int))
    (hS : forall z, z ∈ S -> intVectorToEuclidean z ∈ Lambda.carrier)
    (u : E) (t : Real) (hu : u ≠ 0) (ht : t ≠ 0) :
    (dilatedPointSet Lambda S hS u t hu ht).card = S.card := by
  simp [dilatedPointSet]

/-- Recover the original integer triple from membership in the dilated set. -/
theorem exists_of_mem_dilatedPointSet
    (Lambda : RankTwoIntegralLattice)
    (S : Finset (Fin 3 -> Int))
    (hS : forall z, z ∈ S -> intVectorToEuclidean z ∈ Lambda.carrier)
    (u : E) (t : Real) (hu : u ≠ 0) (ht : t ≠ 0)
    {x : directionallyDilatedLattice Lambda u t hu ht}
    (hx : x ∈ dilatedPointSet Lambda S hS u t hu ht) :
    exists z, exists hz : z ∈ S,
      x = directionallyDilatedLatticeEquiv Lambda u t hu ht
        ⟨intVectorToEuclidean z, hS z hz⟩ := by
  rw [dilatedPointSet, Finset.mem_map] at hx
  obtain ⟨z, _hz, rfl⟩ := hx
  exact ⟨z, z.property, rfl⟩

/-- Every original point maps into the finite dilated set. -/
theorem dilatedPoint_mem_dilatedPointSet
    (Lambda : RankTwoIntegralLattice)
    (S : Finset (Fin 3 -> Int))
    (hS : forall z, z ∈ S -> intVectorToEuclidean z ∈ Lambda.carrier)
    (u : E) (t : Real) (hu : u ≠ 0) (ht : t ≠ 0)
    {z : Fin 3 -> Int} (hz : z ∈ S) :
    directionallyDilatedLatticeEquiv Lambda u t hu ht
        ⟨intVectorToEuclidean z, hS z hz⟩ ∈
      dilatedPointSet Lambda S hS u t hu ht := by
  rw [dilatedPointSet, Finset.mem_map]
  exact ⟨⟨z, hz⟩, Finset.mem_attach _ _, rfl⟩

end PrimesRestrictedDigits
