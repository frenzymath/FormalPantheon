import PrimesRestrictedDigits.SieveAsymptotics.TypeIIRegionSandwich

/-!
# Finite Type II region-cardinality assembly

This file converts the corrected near-scale support sandwich into the finite cardinality
inequality used in Proposition 7.2. The two full supports share one outside-near carrier tail.
Interior cell supports are disjoint; remainder cell supports need not be.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private theorem card_filter_gap_bounds_of_near_sandwich
    (C near interior original remainder : Finset Nat)
    (hlower : interior ∩ near ⊆ original ∩ near)
    (hupper : original ∩ near ⊆ (interior ∪ remainder) ∩ near) :
    (((original.filter fun n => n ∈ C).card : Real) -
        ((interior.filter fun n => n ∈ C).card : Real) ≤
      ((remainder.filter fun n => n ∈ C).card : Real) +
        ((C \ near).card : Real)) ∧
    (((interior.filter fun n => n ∈ C).card : Real) -
        ((original.filter fun n => n ∈ C).card : Real) ≤
      ((C \ near).card : Real)) := by
  let originalC := original.filter fun n => n ∈ C
  let interiorC := interior.filter fun n => n ∈ C
  let remainderC := remainder.filter fun n => n ∈ C
  let tailC := C \ near
  have horiginalSubset :
      originalC ⊆ (interiorC ∪ remainderC) ∪ tailC := by
    intro n hn
    have hnOriginal : n ∈ original := (Finset.mem_filter.mp hn).1
    have hnC : n ∈ C := (Finset.mem_filter.mp hn).2
    by_cases hnNear : n ∈ near
    · have hnUpper := hupper (Finset.mem_inter.mpr ⟨hnOriginal, hnNear⟩)
      rcases Finset.mem_union.mp (Finset.mem_inter.mp hnUpper).1 with
        hnInterior | hnRemainder
      · exact Finset.mem_union.mpr <| Or.inl <|
          Finset.mem_union.mpr <| Or.inl <|
            Finset.mem_filter.mpr ⟨hnInterior, hnC⟩
      · exact Finset.mem_union.mpr <| Or.inl <|
          Finset.mem_union.mpr <| Or.inr <|
            Finset.mem_filter.mpr ⟨hnRemainder, hnC⟩
    · exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_sdiff.mpr ⟨hnC, hnNear⟩
  have hinteriorSubset : interiorC ⊆ originalC ∪ tailC := by
    intro n hn
    have hnInterior : n ∈ interior := (Finset.mem_filter.mp hn).1
    have hnC : n ∈ C := (Finset.mem_filter.mp hn).2
    by_cases hnNear : n ∈ near
    · have hnLower := hlower (Finset.mem_inter.mpr ⟨hnInterior, hnNear⟩)
      exact Finset.mem_union.mpr <| Or.inl <|
        Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp hnLower).1, hnC⟩
    · exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_sdiff.mpr ⟨hnC, hnNear⟩
  have horiginalCard := Finset.card_le_card horiginalSubset
  have hinteriorCard := Finset.card_le_card hinteriorSubset
  have hfirstUnion := Finset.card_union_le interiorC remainderC
  have hsecondUnion := Finset.card_union_le (interiorC ∪ remainderC) tailC
  have hinteriorUnion := Finset.card_union_le originalC tailC
  have horiginalNat :
      originalC.card ≤ interiorC.card + remainderC.card + tailC.card := by
    omega
  have hinteriorNat : interiorC.card ≤ originalC.card + tailC.card := by
    omega
  have horiginalReal :
      (originalC.card : Real) ≤
        (interiorC.card : Real) + (remainderC.card : Real) +
          (tailC.card : Real) := by
    exact_mod_cast horiginalNat
  have hinteriorReal :
      (interiorC.card : Real) ≤
        (originalC.card : Real) + (tailC.card : Real) := by
    exact_mod_cast hinteriorNat
  change
    ((originalC.card : Real) - (interiorC.card : Real) ≤
        (remainderC.card : Real) + (tailC.card : Real)) ∧
      ((interiorC.card : Real) - (originalC.card : Real) ≤
        (tailC.card : Real))
  constructor <;> linarith

/-- A near support sandwich controls a density-weighted discrepancy by the
interior discrepancy, the positive remainder mass, and one joint carrier
tail. -/
theorem abs_weighted_card_filter_sub_le_of_near_sandwich
    (A B near interior original remainder : Finset Nat)
    (lambda : Real) (hlambda : 0 ≤ lambda)
    (hlower : interior ∩ near ⊆ original ∩ near)
    (hupper : original ∩ near ⊆ (interior ∪ remainder) ∩ near) :
    |((original.filter fun n => n ∈ A).card : Real) -
        lambda * ((original.filter fun n => n ∈ B).card : Real)| ≤
      |((interior.filter fun n => n ∈ A).card : Real) -
        lambda * ((interior.filter fun n => n ∈ B).card : Real)| +
      (((remainder.filter fun n => n ∈ A).card : Real) +
        lambda * ((remainder.filter fun n => n ∈ B).card : Real)) +
      (((A \ near).card : Real) +
        lambda * ((B \ near).card : Real)) := by
  obtain ⟨hAUpper, hALower⟩ :=
    card_filter_gap_bounds_of_near_sandwich A near interior original
      remainder hlower hupper
  obtain ⟨hBUpper, hBLower⟩ :=
    card_filter_gap_bounds_of_near_sandwich B near interior original
      remainder hlower hupper
  let sA : Real := ((original.filter fun n => n ∈ A).card : Real)
  let iA : Real := ((interior.filter fun n => n ∈ A).card : Real)
  let rA : Real := ((remainder.filter fun n => n ∈ A).card : Real)
  let tA : Real := ((A \ near).card : Real)
  let sB : Real := ((original.filter fun n => n ∈ B).card : Real)
  let iB : Real := ((interior.filter fun n => n ∈ B).card : Real)
  let rB : Real := ((remainder.filter fun n => n ∈ B).card : Real)
  let tB : Real := ((B \ near).card : Real)
  have hrA : 0 ≤ rA := by positivity
  have hrB : 0 ≤ rB := by positivity
  have hAabs : |sA - iA| ≤ rA + tA := by
    rw [abs_sub_le_iff]
    constructor
    · simpa only [sA, iA, rA, tA] using hAUpper
    · have htail : tA ≤ rA + tA := le_add_of_nonneg_left hrA
      have hlower : iA - sA ≤ tA := by
        simpa only [sA, iA, tA] using hALower
      exact hlower.trans htail
  have hBabs : |sB - iB| ≤ rB + tB := by
    rw [abs_sub_le_iff]
    constructor
    · simpa only [sB, iB, rB, tB] using hBUpper
    · have htail : tB ≤ rB + tB := le_add_of_nonneg_left hrB
      have hlower : iB - sB ≤ tB := by
        simpa only [sB, iB, tB] using hBLower
      exact hlower.trans htail
  have hweighted :
      |(sA - iA) - lambda * (sB - iB)| ≤
        (rA + tA) + lambda * (rB + tB) := by
    calc
      |(sA - iA) - lambda * (sB - iB)| ≤
          |sA - iA| + |lambda * (sB - iB)| := abs_sub _ _
      _ = |sA - iA| + lambda * |sB - iB| := by
        rw [abs_mul, abs_of_nonneg hlambda]
      _ ≤ (rA + tA) + lambda * (rB + tB) :=
        add_le_add hAabs (mul_le_mul_of_nonneg_left hBabs hlambda)
  have hdecompose :
      sA - lambda * sB =
        (iA - lambda * iB) +
          ((sA - iA) - lambda * (sB - iB)) := by
    ring
  rw [show
    ((original.filter fun n => n ∈ A).card : Real) = sA by rfl,
    show ((original.filter fun n => n ∈ B).card : Real) = sB by rfl,
    show ((interior.filter fun n => n ∈ A).card : Real) = iA by rfl,
    show ((interior.filter fun n => n ∈ B).card : Real) = iB by rfl,
    show ((remainder.filter fun n => n ∈ A).card : Real) = rA by rfl,
    show ((remainder.filter fun n => n ∈ B).card : Real) = rB by rfl,
    show ((A \ near).card : Real) = tA by rfl,
    show ((B \ near).card : Real) = tB by rfl,
    hdecompose]
  apply (abs_add_le _ _).trans
  calc
    |iA - lambda * iB| +
        |(sA - iA) - lambda * (sB - iB)| ≤
      |iA - lambda * iB| +
        ((rA + tA) + lambda * (rB + tB)) :=
      add_le_add le_rfl hweighted
    _ = |iA - lambda * iB| + (rA + lambda * rB) +
        (tA + lambda * tB) := by ring

private theorem card_filter_typeIICubeProductSupportUnion_interior
    (XNat k : Nat) (eta delta : Real)
    (region : Set (Fin (k + 1) -> Real))
    (C : Finset Nat) (hX : 1 < XNat) (hdelta : 0 < delta)
    (hregion : IsTypeIISourceRegion eta region) :
    (((typeIICubeProductSupportUnion XNat delta eta
        (typeIIInteriorCubeAnchors delta region)).filter
          (fun n => n ∈ C)).card : Real) =
      ∑ anchor ∈ typeIIInteriorCubeAnchors delta region,
        (((primeTupleProductSupport
          (majorArcPrimeTuples XNat
            (scaledNaturalCubeAnchor delta anchor) delta eta)).filter
              (fun n => n ∈ C)).card : Real) := by
  have hdisjoint := pairwiseDisjoint_typeIIInteriorCubeProductSupports
    XNat k hX hdelta hregion
  unfold typeIICubeProductSupportUnion
  rw [Finset.filter_biUnion]
  rw [Finset.card_biUnion
    (Finset.pairwiseDisjoint_filter hdisjoint fun n => n ∈ C)]
  exact Nat.cast_sum _ _

private theorem card_filter_typeIICubeProductSupportUnion_remainder_le
    (XNat : Nat) {k : Nat} (eta delta : Real)
    (region : Set (Fin (k + 1) -> Real)) (C : Finset Nat) :
    (((typeIICubeProductSupportUnion XNat delta eta
        (typeIIRemainderCubeAnchors delta region)).filter
          (fun n => n ∈ C)).card : Real) ≤
      ∑ anchor ∈ typeIIRemainderCubeAnchors delta region,
        (((primeTupleProductSupport
          (majorArcPrimeTuples XNat
            (scaledNaturalCubeAnchor delta anchor) delta eta)).filter
              (fun n => n ∈ C)).card : Real) := by
  have hcard :
      ((typeIIRemainderCubeAnchors delta region).biUnion fun anchor =>
          (primeTupleProductSupport
            (majorArcPrimeTuples XNat
              (scaledNaturalCubeAnchor delta anchor) delta eta)).filter
                (fun n => n ∈ C)).card ≤
        ∑ anchor ∈ typeIIRemainderCubeAnchors delta region,
          ((primeTupleProductSupport
            (majorArcPrimeTuples XNat
              (scaledNaturalCubeAnchor delta anchor) delta eta)).filter
                (fun n => n ∈ C)).card :=
    Finset.card_biUnion_le
  unfold typeIICubeProductSupportUnion
  rw [Finset.filter_biUnion]
  exact_mod_cast hcard

/-- The original Type II region discrepancy is bounded by the interior
cell discrepancies, positive remainder-cell mass, and the one weak carrier
tail. -/
theorem typeIIOriginalRegionDiscrepancy_le
    {XNat k : Nat} {eta delta lambda : Real}
    {region : Set (Fin (k + 1) -> Real)}
    (A B : Finset Nat)
    (hX : 1 < XNat) (heta : 0 < eta)
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ 1 / 2)
    (hlambda : 0 ≤ lambda)
    (hregion : IsTypeIISourceRegion eta region) :
    let source : Finset Nat := typeIIOriginalRegionSupport XNat region
    let interior : Finset (Fin k -> Nat) :=
      typeIIInteriorCubeAnchors delta region
    let remainder : Finset (Fin k -> Nat) :=
      typeIIRemainderCubeAnchors delta region
    let supportCount : (Fin k -> Nat) -> Finset Nat -> Real :=
      fun anchor C =>
        (((primeTupleProductSupport
          (majorArcPrimeTuples XNat
            (scaledNaturalCubeAnchor delta anchor) delta eta)).filter
              (fun n => n ∈ C)).card : Real)
    |((source.filter fun n => n ∈ A).card : Real) -
        lambda * ((source.filter fun n => n ∈ B).card : Real)| ≤
      (∑ anchor ∈ interior,
        |supportCount anchor A - lambda * supportCount anchor B|) +
      remainder.sum (fun anchor =>
        supportCount anchor A + lambda * supportCount anchor B) +
      (((A \ typeIINearXCarrier XNat delta).card : Real) +
        lambda * ((B \ typeIINearXCarrier XNat delta).card : Real)) := by
  dsimp only
  let near : Finset Nat := typeIINearXCarrier XNat delta
  let source : Finset Nat := typeIIOriginalRegionSupport XNat region
  let interiorAnchors : Finset (Fin k -> Nat) :=
    typeIIInteriorCubeAnchors delta region
  let remainderAnchors : Finset (Fin k -> Nat) :=
    typeIIRemainderCubeAnchors delta region
  let interiorSupport : Finset Nat :=
    typeIICubeProductSupportUnion XNat delta eta interiorAnchors
  let remainderSupport : Finset Nat :=
    typeIICubeProductSupportUnion XNat delta eta remainderAnchors
  let supportCount : (Fin k -> Nat) -> Finset Nat -> Real :=
    fun anchor C =>
      (((primeTupleProductSupport
        (majorArcPrimeTuples XNat
          (scaledNaturalCubeAnchor delta anchor) delta eta)).filter
            (fun n => n ∈ C)).card : Real)
  have hsandwich := typeIIRegionSupport_near_sandwich hX heta hdelta
    hdeltaHalf hregion
  have hfinite := abs_weighted_card_filter_sub_le_of_near_sandwich
    A B near interiorSupport source remainderSupport lambda hlambda
    (by simpa only [near, interiorSupport, source, interiorAnchors] using
      hsandwich.1)
    (by simpa only [near, interiorSupport, remainderSupport, source,
      interiorAnchors, remainderAnchors] using hsandwich.2)
  have hinteriorCount (C : Finset Nat) :
      (((interiorSupport.filter fun n => n ∈ C).card : Real)) =
        ∑ anchor ∈ interiorAnchors, supportCount anchor C := by
    simpa only [interiorSupport, interiorAnchors, supportCount] using
      card_filter_typeIICubeProductSupportUnion_interior
        XNat k eta delta region C hX hdelta hregion
  have hremainderCount (C : Finset Nat) :
      (((remainderSupport.filter fun n => n ∈ C).card : Real)) ≤
        ∑ anchor ∈ remainderAnchors, supportCount anchor C := by
    simpa only [remainderSupport, remainderAnchors, supportCount] using
      card_filter_typeIICubeProductSupportUnion_remainder_le
        XNat eta delta region C
  have hinterior :
      |((interiorSupport.filter fun n => n ∈ A).card : Real) -
          lambda *
            ((interiorSupport.filter fun n => n ∈ B).card : Real)| ≤
        ∑ anchor ∈ interiorAnchors,
          |supportCount anchor A - lambda * supportCount anchor B| := by
    rw [hinteriorCount A, hinteriorCount B, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  have hremainder :
      ((remainderSupport.filter fun n => n ∈ A).card : Real) +
          lambda *
            ((remainderSupport.filter fun n => n ∈ B).card : Real) ≤
        remainderAnchors.sum (fun anchor =>
          supportCount anchor A + lambda * supportCount anchor B) := by
    calc
      ((remainderSupport.filter fun n => n ∈ A).card : Real) +
          lambda *
            ((remainderSupport.filter fun n => n ∈ B).card : Real) ≤
        (∑ anchor ∈ remainderAnchors, supportCount anchor A) +
          lambda * (∑ anchor ∈ remainderAnchors,
            supportCount anchor B) :=
        add_le_add (hremainderCount A)
          (mul_le_mul_of_nonneg_left (hremainderCount B) hlambda)
      _ = remainderAnchors.sum (fun anchor =>
          supportCount anchor A + lambda * supportCount anchor B) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
  apply hfinite.trans
  exact add_le_add (add_le_add hinterior hremainder) le_rfl

end

end PrimesRestrictedDigits
