import PrimesRestrictedDigits.MajorArcs.Factorization
import Mathlib.Data.Finset.Sort

/-!
# Canonical coordinate splits for prime tuples

This replaces the implicit coordinate permutation in the proof of published Proposition 9.3 by
increasing order equivalences for an arbitrary selected subset and its finite complement.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The `j`th selected prefix coordinate in increasing order. -/
noncomputable def selectedPrimeCoordinate
    {k : Nat} (I : Finset (Fin k)) (j : Fin I.card) : Fin k :=
  (I.orderIsoOfFin rfl j).val

/-- The `j`th complementary prefix coordinate in increasing order. -/
noncomputable def complementaryPrimeCoordinate
    {k : Nat} (I : Finset (Fin k)) (j : Fin Iᶜ.card) : Fin k :=
  (Iᶜ.orderIsoOfFin rfl j).val

/-- Anchors restricted to the selected coordinates in canonical order. -/
noncomputable def selectedPrimeAnchor
    {k : Nat} (a : Fin k -> Real) (I : Finset (Fin k)) :
    Fin I.card -> Real :=
  fun j => a (selectedPrimeCoordinate I j)

/-- Anchors restricted to the complementary coordinates in canonical order. -/
noncomputable def complementaryPrimeAnchor
    {k : Nat} (a : Fin k -> Real) (I : Finset (Fin k)) :
    Fin Iᶜ.card -> Real :=
  fun j => a (complementaryPrimeCoordinate I j)

@[simp]
theorem selectedPrimeCoordinate_mem
    {k : Nat} (I : Finset (Fin k)) (j : Fin I.card) :
    selectedPrimeCoordinate I j ∈ I := by
  exact (I.orderIsoOfFin rfl j).property

@[simp]
theorem complementaryPrimeCoordinate_not_mem
    {k : Nat} (I : Finset (Fin k)) (j : Fin Iᶜ.card) :
    complementaryPrimeCoordinate I j ∉ I := by
  have hmem := (Iᶜ.orderIsoOfFin rfl j).property
  change (Iᶜ.orderIsoOfFin rfl j).val ∉ I
  simpa only [Finset.mem_compl] using hmem

/-- Merge two canonically ordered restrictions into one prefix tuple. -/
noncomputable def mergePrefixTuples
    {k : Nat} (I : Finset (Fin k))
    (u : Fin I.card -> Nat) (v : Fin Iᶜ.card -> Nat) : Fin k -> Nat :=
  fun i =>
    if hi : i ∈ I then
      u ((I.orderIsoOfFin rfl).symm ⟨i, hi⟩)
    else
      v ((Iᶜ.orderIsoOfFin rfl).symm ⟨i, by simpa using hi⟩)

@[simp]
theorem mergePrefixTuples_selected
    {k : Nat} (I : Finset (Fin k))
    (u : Fin I.card -> Nat) (v : Fin Iᶜ.card -> Nat)
    (j : Fin I.card) :
    mergePrefixTuples I u v (selectedPrimeCoordinate I j) = u j := by
  rw [mergePrefixTuples, dif_pos (selectedPrimeCoordinate_mem I j)]
  change u ((I.orderIsoOfFin rfl).symm (I.orderIsoOfFin rfl j)) = u j
  rw [OrderIso.symm_apply_apply]

@[simp]
theorem mergePrefixTuples_complementary
    {k : Nat} (I : Finset (Fin k))
    (u : Fin I.card -> Nat) (v : Fin Iᶜ.card -> Nat)
    (j : Fin Iᶜ.card) :
    mergePrefixTuples I u v (complementaryPrimeCoordinate I j) = v j := by
  rw [mergePrefixTuples,
    dif_neg (complementaryPrimeCoordinate_not_mem I j)]
  change v ((Iᶜ.orderIsoOfFin rfl).symm (Iᶜ.orderIsoOfFin rfl j)) = v j
  rw [OrderIso.symm_apply_apply]

/-- Merge selected and complementary prefix tuples, with an explicit inverse
given by restriction to the two increasing coordinate lists. -/
noncomputable def prefixTupleSplitEquiv
    {k : Nat} (I : Finset (Fin k)) :
    ((Fin I.card -> Nat) × (Fin Iᶜ.card -> Nat)) ≃ (Fin k -> Nat) where
  toFun uv := mergePrefixTuples I uv.1 uv.2
  invFun p :=
    (fun j => p (selectedPrimeCoordinate I j),
      fun j => p (complementaryPrimeCoordinate I j))
  left_inv uv := by
    apply Prod.ext
    · funext j
      exact mergePrefixTuples_selected I uv.1 uv.2 j
    · funext j
      exact mergePrefixTuples_complementary I uv.1 uv.2 j
  right_inv p := by
    funext i
    change mergePrefixTuples I
      (fun j => p (selectedPrimeCoordinate I j))
      (fun j => p (complementaryPrimeCoordinate I j)) i = p i
    by_cases hi : i ∈ I
    · rw [mergePrefixTuples, dif_pos hi]
      congr 1
      exact congrArg Subtype.val
        ((I.orderIsoOfFin rfl).apply_symm_apply ⟨i, hi⟩)
    · rw [mergePrefixTuples, dif_neg hi]
      congr 1
      exact congrArg Subtype.val
        ((Iᶜ.orderIsoOfFin rfl).apply_symm_apply
          ⟨i, by simpa using hi⟩)

@[simp]
theorem prefixTupleSplitEquiv_apply_selected
    {k : Nat} (I : Finset (Fin k))
    (u : Fin I.card -> Nat) (v : Fin Iᶜ.card -> Nat)
    (j : Fin I.card) :
    prefixTupleSplitEquiv I (u, v) (selectedPrimeCoordinate I j) = u j := by
  exact mergePrefixTuples_selected I u v j

@[simp]
theorem prefixTupleSplitEquiv_apply_complementary
    {k : Nat} (I : Finset (Fin k))
    (u : Fin I.card -> Nat) (v : Fin Iᶜ.card -> Nat)
    (j : Fin Iᶜ.card) :
    prefixTupleSplitEquiv I (u, v) (complementaryPrimeCoordinate I j) = v j := by
  exact mergePrefixTuples_complementary I u v j

/-- Split a full `(k+1)`-tuple into the selected prefix and the
complementary-prefix-plus-last tuple. -/
noncomputable def fullTupleSplitEquiv
    {k : Nat} (I : Finset (Fin k)) :
    ((Fin I.card -> Nat) × (Fin (Iᶜ.card + 1) -> Nat)) ≃
      (Fin (k + 1) -> Nat) where
  toFun uv :=
    Fin.snoc
      (prefixTupleSplitEquiv I (uv.1, Fin.init uv.2))
      (uv.2 (Fin.last Iᶜ.card))
  invFun p :=
    let split := (prefixTupleSplitEquiv I).symm (Fin.init p)
    (split.1, Fin.snoc split.2 (p (Fin.last k)))
  left_inv uv := by
    simp only [Fin.init_snoc, Fin.snoc_last]
    let split := (prefixTupleSplitEquiv I).symm
      (prefixTupleSplitEquiv I (uv.1, Fin.init uv.2))
    have hsplit : split = (uv.1, Fin.init uv.2) := by
      exact (prefixTupleSplitEquiv I).symm_apply_apply _
    change (split.1,
      Fin.snoc split.2 (uv.2 (Fin.last Iᶜ.card))) = uv
    rw [hsplit]
    simp
  right_inv p := by
    simp only [Fin.init_snoc, Fin.snoc_last]
    let split := (prefixTupleSplitEquiv I).symm (Fin.init p)
    have hsplit : prefixTupleSplitEquiv I split = Fin.init p := by
      exact (prefixTupleSplitEquiv I).apply_symm_apply _
    change Fin.snoc (prefixTupleSplitEquiv I split)
      (p (Fin.last k)) = p
    rw [hsplit, Fin.snoc_init_self]

@[simp]
theorem fullTupleSplitEquiv_init
    {k : Nat} (I : Finset (Fin k))
    (u : Fin I.card -> Nat) (v : Fin (Iᶜ.card + 1) -> Nat) :
    Fin.init (fullTupleSplitEquiv I (u, v)) =
      prefixTupleSplitEquiv I (u, Fin.init v) := by
  simp [fullTupleSplitEquiv]

@[simp]
theorem fullTupleSplitEquiv_last
    {k : Nat} (I : Finset (Fin k))
    (u : Fin I.card -> Nat) (v : Fin (Iᶜ.card + 1) -> Nat) :
    fullTupleSplitEquiv I (u, v) (Fin.last k) =
      v (Fin.last Iᶜ.card) := by
  simp [fullTupleSplitEquiv]

/-- The natural product is preserved and split by the prefix equivalence. -/
theorem primeTupleProduct_prefixTupleSplitEquiv
    {k : Nat} (I : Finset (Fin k))
    (u : Fin I.card -> Nat) (v : Fin Iᶜ.card -> Nat) :
    primeTupleProduct (prefixTupleSplitEquiv I (u, v)) =
      primeTupleProduct u * primeTupleProduct v := by
  have hselected :
      (∏ j, u j) =
        ∏ i ∈ I, mergePrefixTuples I u v i := by
    calc
      (∏ j, u j) =
          ∏ i : I, mergePrefixTuples I u v i.val := by
        apply Fintype.prod_equiv (I.orderIsoOfFin rfl).toEquiv
        intro j
        exact (mergePrefixTuples_selected I u v j).symm
      _ = ∏ i ∈ I, mergePrefixTuples I u v i :=
        Finset.prod_coe_sort I (mergePrefixTuples I u v)
  have hcomplementary :
      (∏ j, v j) =
        ∏ i ∈ Iᶜ, mergePrefixTuples I u v i := by
    calc
      (∏ j, v j) =
          ∏ i : (Iᶜ : Finset (Fin k)),
            mergePrefixTuples I u v i.val := by
        apply Fintype.prod_equiv (Iᶜ.orderIsoOfFin rfl).toEquiv
        intro j
        exact (mergePrefixTuples_complementary I u v j).symm
      _ = ∏ i ∈ Iᶜ, mergePrefixTuples I u v i :=
        Finset.prod_coe_sort Iᶜ (mergePrefixTuples I u v)
  have hsplit := Finset.prod_mul_prod_compl I (mergePrefixTuples I u v)
  unfold primeTupleProduct
  change (∏ i, mergePrefixTuples I u v i) = (∏ j, u j) * ∏ j, v j
  calc
    (∏ i, mergePrefixTuples I u v i) =
        (∏ i ∈ I, mergePrefixTuples I u v i) *
          ∏ i ∈ Iᶜ, mergePrefixTuples I u v i := hsplit.symm
    _ = (∏ j, u j) * ∏ j, v j := by
      rw [hselected, hcomplementary]

/-- The product of logarithmic weights is preserved and split by the prefix
equivalence. -/
theorem primeTupleLogWeight_prefixTupleSplitEquiv
    {k : Nat} (I : Finset (Fin k))
    (u : Fin I.card -> Nat) (v : Fin Iᶜ.card -> Nat) :
    primeTupleLogWeight (prefixTupleSplitEquiv I (u, v)) =
      primeTupleLogWeight u * primeTupleLogWeight v := by
  have hselected :
      (∏ j, Real.log (u j : Real)) =
        ∏ i ∈ I, Real.log (mergePrefixTuples I u v i : Real) := by
    calc
      (∏ j, Real.log (u j : Real)) =
          ∏ i : I, Real.log (mergePrefixTuples I u v i.val : Real) := by
        apply Fintype.prod_equiv (I.orderIsoOfFin rfl).toEquiv
        intro j
        change Real.log (u j : Real) =
          Real.log (mergePrefixTuples I u v
            (selectedPrimeCoordinate I j) : Real)
        rw [mergePrefixTuples_selected]
      _ = ∏ i ∈ I, Real.log (mergePrefixTuples I u v i : Real) :=
        Finset.prod_coe_sort I
          (fun i => Real.log (mergePrefixTuples I u v i : Real))
  have hcomplementary :
      (∏ j, Real.log (v j : Real)) =
        ∏ i ∈ Iᶜ, Real.log (mergePrefixTuples I u v i : Real) := by
    calc
      (∏ j, Real.log (v j : Real)) =
          ∏ i : (Iᶜ : Finset (Fin k)),
            Real.log (mergePrefixTuples I u v i.val : Real) := by
        apply Fintype.prod_equiv (Iᶜ.orderIsoOfFin rfl).toEquiv
        intro j
        change Real.log (v j : Real) =
          Real.log (mergePrefixTuples I u v
            (complementaryPrimeCoordinate I j) : Real)
        rw [mergePrefixTuples_complementary]
      _ = ∏ i ∈ Iᶜ, Real.log (mergePrefixTuples I u v i : Real) :=
        Finset.prod_coe_sort Iᶜ
          (fun i => Real.log (mergePrefixTuples I u v i : Real))
  have hsplit := Finset.prod_mul_prod_compl I
    (fun i => Real.log (mergePrefixTuples I u v i : Real))
  unfold primeTupleLogWeight
  change (∏ i, Real.log (mergePrefixTuples I u v i : Real)) =
    (∏ j, Real.log (u j : Real)) * ∏ j, Real.log (v j : Real)
  calc
    (∏ i, Real.log (mergePrefixTuples I u v i : Real)) =
        (∏ i ∈ I, Real.log (mergePrefixTuples I u v i : Real)) *
          ∏ i ∈ Iᶜ, Real.log (mergePrefixTuples I u v i : Real) :=
      hsplit.symm
    _ = (∏ j, Real.log (u j : Real)) *
        ∏ j, Real.log (v j : Real) := by rw [hselected, hcomplementary]

/-- The full tuple product factors into the selected product and the single
complement-plus-last product. -/
theorem primeTupleProduct_fullTupleSplitEquiv
    {k : Nat} (I : Finset (Fin k))
    (u : Fin I.card -> Nat) (v : Fin (Iᶜ.card + 1) -> Nat) :
    primeTupleProduct (fullTupleSplitEquiv I (u, v)) =
      primeTupleProduct u * primeTupleProduct v := by
  change primeTupleProduct
      (Fin.snoc (prefixTupleSplitEquiv I (u, Fin.init v))
        (v (Fin.last Iᶜ.card))) = _
  rw [primeTupleProduct_snoc,
    primeTupleProduct_prefixTupleSplitEquiv,
    primeTupleProduct_eq_init_mul_last]
  ring

/-- The full tuple logarithmic weight factors across the same split. -/
theorem primeTupleLogWeight_fullTupleSplitEquiv
    {k : Nat} (I : Finset (Fin k))
    (u : Fin I.card -> Nat) (v : Fin (Iᶜ.card + 1) -> Nat) :
    primeTupleLogWeight (fullTupleSplitEquiv I (u, v)) =
      primeTupleLogWeight u * primeTupleLogWeight v := by
  change primeTupleLogWeight
      (Fin.snoc (prefixTupleSplitEquiv I (u, Fin.init v))
        (v (Fin.last Iᶜ.card))) = _
  rw [primeTupleLogWeight_snoc,
    primeTupleLogWeight_prefixTupleSplitEquiv]
  have hv : primeTupleLogWeight v =
      primeTupleLogWeight (Fin.init v) *
        Real.log (v (Fin.last Iᶜ.card) : Real) := by
    rw [← primeTupleLogWeight_snoc, Fin.snoc_init_self]
  rw [hv]
  ring

end

end PrimesRestrictedDigits
