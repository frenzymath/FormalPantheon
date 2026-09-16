import PrimesRestrictedDigits.ExceptionalMinorArcs.SplitPrimeCoordinates

/-!
# Prime-tuple carriers for an arbitrary coordinate split

The second carrier combines the complementary prefix coordinates with the distinguished last
prime before any scale localization. Its last-prime condition is the original one from the
full region.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- Selected prefix coordinates in their canonical increasing order. -/
noncomputable def selectedProjectedPrimeTuples
    (X : Nat) {k : Nat} (a : Fin k -> Real) (delta : Real)
    (I : Finset (Fin k)) : Finset (Fin I.card -> Nat) :=
  projectedPrimeBoxTuples X (selectedPrimeAnchor a I) delta

/-- Complementary prefix coordinates in their canonical increasing order. -/
noncomputable def complementaryProjectedPrimeTuples
    (X : Nat) {k : Nat} (a : Fin k -> Real) (delta : Real)
    (I : Finset (Fin k)) : Finset (Fin Iᶜ.card -> Nat) :=
  projectedPrimeBoxTuples X (complementaryPrimeAnchor a I) delta

/-- The complementary prefix tuple with the original distinguished last
prime appended. -/
noncomputable def complementaryLastPrimeTuples
    (X : Nat) {k : Nat} (a : Fin k -> Real) (delta eta : Real)
    (I : Finset (Fin k)) : Finset (Fin (Iᶜ.card + 1) -> Nat) :=
  (majorArcLastPrimes X a delta eta ×ˢ
      complementaryProjectedPrimeTuples X a delta I).map
    (Fin.snocEquiv (fun _ : Fin (Iᶜ.card + 1) => Nat)).toEmbedding

/-- Product-fiber weight of the selected coordinates. -/
noncomputable def selectedProjectedPrimeWeightAtProduct
    (X : Nat) {k : Nat} (a : Fin k -> Real) (delta : Real)
    (I : Finset (Fin k)) (n : Nat) : Real :=
  primeTupleWeightAtProduct (selectedProjectedPrimeTuples X a delta I) n

/-- Product-fiber weight of the complementary coordinates together with the
last prime. -/
noncomputable def complementaryLastPrimeWeightAtProduct
    (X : Nat) {k : Nat} (a : Fin k -> Real) (delta eta : Real)
    (I : Finset (Fin k)) (m : Nat) : Real :=
  primeTupleWeightAtProduct
    (complementaryLastPrimeTuples X a delta eta I) m

/-- Full tuples obtained by merging the selected and complementary-last
carriers. -/
noncomputable def splitMajorArcPrimeTuples
    (X : Nat) {k : Nat} (a : Fin k -> Real) (delta eta : Real)
    (I : Finset (Fin k)) : Finset (Fin (k + 1) -> Nat) :=
  (selectedProjectedPrimeTuples X a delta I ×ˢ
      complementaryLastPrimeTuples X a delta eta I).map
    (fullTupleSplitEquiv I).toEmbedding

@[simp]
theorem mem_selectedProjectedPrimeTuples_iff
    {X k : Nat} {a : Fin k -> Real} {delta : Real}
    {I : Finset (Fin k)} {u : Fin I.card -> Nat} :
    u ∈ selectedProjectedPrimeTuples X a delta I ↔
      (∀ j, u j ∈ Nat.primesLE X) ∧
        ∀ j, normalizedPrimeLog X (u j) ∈
          Set.Ioc (a (selectedPrimeCoordinate I j))
            (a (selectedPrimeCoordinate I j) + delta) := by
  simpa only [selectedProjectedPrimeTuples, selectedPrimeAnchor] using
    (mem_projectedPrimeBoxTuples_iff
      (X := X) (a := selectedPrimeAnchor a I) (δ := delta) (p := u))

@[simp]
theorem mem_complementaryProjectedPrimeTuples_iff
    {X k : Nat} {a : Fin k -> Real} {delta : Real}
    {I : Finset (Fin k)} {v : Fin Iᶜ.card -> Nat} :
    v ∈ complementaryProjectedPrimeTuples X a delta I ↔
      (∀ j, v j ∈ Nat.primesLE X) ∧
        ∀ j, normalizedPrimeLog X (v j) ∈
          Set.Ioc (a (complementaryPrimeCoordinate I j))
            (a (complementaryPrimeCoordinate I j) + delta) := by
  simpa only [complementaryProjectedPrimeTuples,
    complementaryPrimeAnchor] using
      (mem_projectedPrimeBoxTuples_iff
        (X := X) (a := complementaryPrimeAnchor a I)
          (δ := delta) (p := v))

@[simp]
theorem mem_complementaryLastPrimeTuples_iff
    {X k : Nat} {a : Fin k -> Real} {delta eta : Real}
    {I : Finset (Fin k)} {v : Fin (Iᶜ.card + 1) -> Nat} :
    v ∈ complementaryLastPrimeTuples X a delta eta I ↔
      Fin.init v ∈ complementaryProjectedPrimeTuples X a delta I ∧
        v (Fin.last Iᶜ.card) ∈ majorArcLastPrimes X a delta eta := by
  classical
  simp [complementaryLastPrimeTuples, and_comm]

@[simp]
theorem fullTupleSplitEquiv_mem_splitMajorArcPrimeTuples_iff
    {X k : Nat} {a : Fin k -> Real} {delta eta : Real}
    {I : Finset (Fin k)}
    {u : Fin I.card -> Nat} {v : Fin (Iᶜ.card + 1) -> Nat} :
    fullTupleSplitEquiv I (u, v) ∈
        splitMajorArcPrimeTuples X a delta eta I ↔
      u ∈ selectedProjectedPrimeTuples X a delta I ∧
        v ∈ complementaryLastPrimeTuples X a delta eta I := by
  classical
  simp [splitMajorArcPrimeTuples]

/-- Merging selected and complementary prefixes recovers exactly the original
projected coordinate box. -/
theorem prefixTupleSplitEquiv_mem_projectedPrimeBoxTuples_iff
    {X k : Nat} {a : Fin k -> Real} {delta : Real}
    {I : Finset (Fin k)}
    {u : Fin I.card -> Nat} {v : Fin Iᶜ.card -> Nat} :
    prefixTupleSplitEquiv I (u, v) ∈ projectedPrimeBoxTuples X a delta ↔
      u ∈ selectedProjectedPrimeTuples X a delta I ∧
        v ∈ complementaryProjectedPrimeTuples X a delta I := by
  rw [mem_projectedPrimeBoxTuples_iff,
    mem_selectedProjectedPrimeTuples_iff,
    mem_complementaryProjectedPrimeTuples_iff]
  constructor
  · rintro ⟨hprime, hbox⟩
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro j
      simpa using hprime (selectedPrimeCoordinate I j)
    · intro j
      simpa using hbox (selectedPrimeCoordinate I j)
    · intro j
      simpa using hprime (complementaryPrimeCoordinate I j)
    · intro j
      simpa using hbox (complementaryPrimeCoordinate I j)
  · rintro ⟨⟨huPrime, huBox⟩, ⟨hvPrime, hvBox⟩⟩
    constructor
    · intro i
      by_cases hi : i ∈ I
      · let j := (I.orderIsoOfFin rfl).symm ⟨i, hi⟩
        have hcoord : selectedPrimeCoordinate I j = i := by
          exact congrArg Subtype.val
            ((I.orderIsoOfFin rfl).apply_symm_apply ⟨i, hi⟩)
        rw [← hcoord, prefixTupleSplitEquiv_apply_selected]
        exact huPrime j
      · let j := (Iᶜ.orderIsoOfFin rfl).symm
          ⟨i, by simpa using hi⟩
        have hcoord : complementaryPrimeCoordinate I j = i := by
          exact congrArg Subtype.val
            ((Iᶜ.orderIsoOfFin rfl).apply_symm_apply
              ⟨i, by simpa using hi⟩)
        rw [← hcoord, prefixTupleSplitEquiv_apply_complementary]
        exact hvPrime j
    · intro i
      by_cases hi : i ∈ I
      · let j := (I.orderIsoOfFin rfl).symm ⟨i, hi⟩
        have hcoord : selectedPrimeCoordinate I j = i := by
          exact congrArg Subtype.val
            ((I.orderIsoOfFin rfl).apply_symm_apply ⟨i, hi⟩)
        rw [← hcoord, prefixTupleSplitEquiv_apply_selected]
        exact huBox j
      · let j := (Iᶜ.orderIsoOfFin rfl).symm
          ⟨i, by simpa using hi⟩
        have hcoord : complementaryPrimeCoordinate I j = i := by
          exact congrArg Subtype.val
            ((Iᶜ.orderIsoOfFin rfl).apply_symm_apply
              ⟨i, by simpa using hi⟩)
        rw [← hcoord, prefixTupleSplitEquiv_apply_complementary]
        exact hvBox j

/-- Below the ambient cutoff, a merged tuple belongs to the full region
exactly when its two factors belong to the selected and complementary-last
carriers. -/
theorem fullTupleSplitEquiv_mem_majorArcPrimeTuples_iff
    {X k : Nat} {a : Fin k -> Real} {delta eta : Real}
    {I : Finset (Fin k)}
    {u : Fin I.card -> Nat} {v : Fin (Iᶜ.card + 1) -> Nat}
    (hX : 1 < X)
    (hproduct : primeTupleProduct (fullTupleSplitEquiv I (u, v)) < X) :
    fullTupleSplitEquiv I (u, v) ∈ majorArcPrimeTuples X a delta eta ↔
      u ∈ selectedProjectedPrimeTuples X a delta I ∧
        v ∈ complementaryLastPrimeTuples X a delta eta I := by
  let q := fullTupleSplitEquiv I (u, v)
  have hfiber := mem_majorArcRegion_productFiber_iff
    (X := X) (k := k) (a := a) (delta := delta) (eta := eta)
    (q := q) (n := primeTupleProduct q) hX hproduct
  have hbase : q ∈ majorArcPrimeTuples X a delta eta ↔
      Fin.init q ∈ projectedPrimeBoxTuples X a delta ∧
        q (Fin.last k) ∈ majorArcLastPrimes X a delta eta := by
    simpa only [Finset.mem_filter, eq_self, and_true, true_and,
      primeTupleProduct_eq_init_mul_last] using hfiber
  simpa only [q, fullTupleSplitEquiv_init, fullTupleSplitEquiv_last,
    prefixTupleSplitEquiv_mem_projectedPrimeBoxTuples_iff,
    mem_complementaryLastPrimeTuples_iff, and_assoc] using hbase

/-- On every product fiber below `X`, the split carrier is exactly the full
source region carrier. -/
theorem majorArcPrimeTuples_productFiber_eq_split
    {X k n : Nat} {a : Fin k -> Real} {delta eta : Real}
    (I : Finset (Fin k)) (hX : 1 < X) (hn : n < X) :
    (majorArcPrimeTuples X a delta eta).filter
        (fun q => primeTupleProduct q = n) =
      (splitMajorArcPrimeTuples X a delta eta I).filter
        (fun q => primeTupleProduct q = n) := by
  classical
  ext q
  rw [Finset.mem_filter, Finset.mem_filter]
  let uv := (fullTupleSplitEquiv I).symm q
  have hq : fullTupleSplitEquiv I uv = q :=
    (fullTupleSplitEquiv I).apply_symm_apply q
  have hproduct (hqn : primeTupleProduct q = n) :
      primeTupleProduct (fullTupleSplitEquiv I uv) < X := by
    rw [hq, hqn]
    exact hn
  constructor
  · rintro ⟨hqRegion, hqn⟩
    have huv := (fullTupleSplitEquiv_mem_majorArcPrimeTuples_iff
      (X := X) (a := a) (delta := delta) (eta := eta)
      (I := I) (u := uv.1) (v := uv.2)
      hX (hproduct hqn)).mp (by simpa only [hq] using hqRegion)
    refine ⟨?_, hqn⟩
    rw [← hq]
    exact fullTupleSplitEquiv_mem_splitMajorArcPrimeTuples_iff.mpr huv
  · rintro ⟨hqSplit, hqn⟩
    have huv : uv.1 ∈ selectedProjectedPrimeTuples X a delta I ∧
        uv.2 ∈ complementaryLastPrimeTuples X a delta eta I := by
      apply fullTupleSplitEquiv_mem_splitMajorArcPrimeTuples_iff.mp
      simpa only [hq] using hqSplit
    refine ⟨?_, hqn⟩
    rw [← hq]
    exact (fullTupleSplitEquiv_mem_majorArcPrimeTuples_iff
      (X := X) (a := a) (delta := delta) (eta := eta)
      (I := I) (u := uv.1) (v := uv.2)
      hX (hproduct hqn)).mpr huv

end

end PrimesRestrictedDigits
