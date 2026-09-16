import PrimesRestrictedDigits.SieveAsymptotics.TypeIIAffineSlabCount

/-!
# Finite Type II thick affine-slab counts

This file extends the affine grid count by a fixed nonnegative half-width. The resulting
pivot-fiber bound keeps the exact `gamma / delta` term needed by the strict Type II transfer.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- Natural grid anchors whose scaled bases lie in a fixed affine slab,
widened by the doubled-cell crossing margin.  Zero normals are excluded. -/
noncomputable def typeIIAffineThickSlabAnchors {k : Nat}
    (delta gamma : Real) (normal : Fin k -> Real) (bound : Real) :
    Finset (Fin k -> Nat) := by
  classical
  exact (typeIINaturalCubeGrid k delta).filter fun anchor =>
    normal ≠ 0 ∧
      |typeIIAffineValue normal
          (scaledNaturalCubeAnchor delta anchor) - bound| <=
        gamma + 2 * delta * typeIIAffineNormalMass normal

@[simp] theorem mem_typeIIAffineThickSlabAnchors
    {k : Nat} {delta gamma bound : Real} {normal : Fin k -> Real}
    {anchor : Fin k -> Nat} :
    anchor ∈ typeIIAffineThickSlabAnchors delta gamma normal bound <->
      anchor ∈ typeIINaturalCubeGrid k delta ∧ normal ≠ 0 ∧
        |typeIIAffineValue normal
            (scaledNaturalCubeAnchor delta anchor) - bound| <=
          gamma + 2 * delta * typeIIAffineNormalMass normal := by
  classical
  simp [typeIIAffineThickSlabAnchors]

/-- Two anchors in one maximal-coordinate fiber of the thick slab have
pivot values differing by at most the rounded fixed width plus the exact
doubled-cell margin. -/
theorem typeIIAffineThickSlabAnchor_sub_le
    {n : Nat} {delta gamma bound : Real}
    {normal : Fin (n + 1) -> Real}
    {u v : Fin (n + 1) -> Nat}
    (hdelta : 0 < delta) (hgamma : 0 <= gamma)
    (hu : u ∈ typeIIAffineThickSlabAnchors
      delta gamma normal bound)
    (hv : v ∈ typeIIAffineThickSlabAnchors
      delta gamma normal bound)
    (hremove :
      (typeIIAffineMaxAbsCoordinate normal).removeNth u =
        (typeIIAffineMaxAbsCoordinate normal).removeNth v)
    (huv : u (typeIIAffineMaxAbsCoordinate normal) <=
      v (typeIIAffineMaxAbsCoordinate normal)) :
    v (typeIIAffineMaxAbsCoordinate normal) -
        u (typeIIAffineMaxAbsCoordinate normal) <=
      Nat.ceil (2 * gamma /
        (delta * |normal (typeIIAffineMaxAbsCoordinate normal)|)) +
          4 * (n + 1) := by
  let pivot := typeIIAffineMaxAbsCoordinate normal
  have hnormal : normal ≠ 0 :=
    (mem_typeIIAffineThickSlabAnchors.mp hu).2.1
  have hpivot : 0 < |normal pivot| :=
    abs_typeIIAffineMaxAbsCoordinate_pos hnormal
  have huSlab := (mem_typeIIAffineThickSlabAnchors.mp hu).2.2
  have hvSlab := (mem_typeIIAffineThickSlabAnchors.mp hv).2.2
  have hdiff :
      |typeIIAffineValue normal (scaledNaturalCubeAnchor delta u) -
          typeIIAffineValue normal (scaledNaturalCubeAnchor delta v)| <=
        2 * gamma + 4 * delta * typeIIAffineNormalMass normal := by
    calc
      |typeIIAffineValue normal (scaledNaturalCubeAnchor delta u) -
          typeIIAffineValue normal (scaledNaturalCubeAnchor delta v)| <=
          |typeIIAffineValue normal (scaledNaturalCubeAnchor delta u) - bound| +
            |bound - typeIIAffineValue normal
              (scaledNaturalCubeAnchor delta v)| := abs_sub_le _ _ _
      _ = |typeIIAffineValue normal
              (scaledNaturalCubeAnchor delta u) - bound| +
            |typeIIAffineValue normal
              (scaledNaturalCubeAnchor delta v) - bound| := by
          rw [abs_sub_comm bound]
      _ <= (gamma + 2 * delta * typeIIAffineNormalMass normal) +
            (gamma + 2 * delta * typeIIAffineNormalMass normal) :=
          add_le_add huSlab hvSlab
      _ = 2 * gamma + 4 * delta * typeIIAffineNormalMass normal := by ring
  have hvalue := typeIIAffineValue_scaled_sub_eq_of_removeNth_eq
    normal delta pivot u v hremove
  rw [hvalue, abs_mul, abs_mul, abs_of_pos hdelta] at hdiff
  have hscale : 0 < |normal pivot| * delta := mul_pos hpivot hdelta
  have hmass := typeIIAffineNormalMass_le_card_mul_max normal
  have hnumerator :
      2 * gamma + 4 * delta * typeIIAffineNormalMass normal <=
        2 * gamma +
          4 * delta * (((n + 1 : Nat) : Real) * |normal pivot|) := by
    gcongr
  have hgap :
      |((u pivot : Nat) : Real) - (v pivot : Nat)| <=
        2 * gamma / (delta * |normal pivot|) +
          4 * ((n + 1 : Nat) : Real) := by
    calc
      |((u pivot : Nat) : Real) - (v pivot : Nat)| <=
          (2 * gamma + 4 * delta * typeIIAffineNormalMass normal) /
            (|normal pivot| * delta) := by
        apply (le_div_iff₀ hscale).2
        calc
          |((u pivot : Nat) : Real) - (v pivot : Nat)| *
                (|normal pivot| * delta) =
              |normal pivot| *
                |((u pivot : Nat) : Real) - (v pivot : Nat)| * delta := by
            ring
          _ <= 2 * gamma +
              4 * delta * typeIIAffineNormalMass normal := hdiff
      _ <= (2 * gamma +
            4 * delta * (((n + 1 : Nat) : Real) * |normal pivot|)) /
          (|normal pivot| * delta) :=
        (div_le_div_iff_of_pos_right hscale).2 hnumerator
      _ = 2 * gamma / (delta * |normal pivot|) +
          4 * ((n + 1 : Nat) : Real) := by
        field_simp [hdelta.ne', hpivot.ne']
  have hceil :
      2 * gamma / (delta * |normal pivot|) <=
        (Nat.ceil (2 * gamma / (delta * |normal pivot|)) : Real) :=
    Nat.le_ceil _
  have hgapCast :
      (((v pivot - u pivot : Nat) : Nat) : Real) <=
        ((Nat.ceil (2 * gamma / (delta * |normal pivot|)) +
          4 * (n + 1) : Nat) : Real) := by
    rw [Nat.cast_sub huv]
    have hnonneg :
        0 <= ((v pivot : Nat) : Real) - (u pivot : Nat) := by
      apply sub_nonneg.mpr
      exact_mod_cast huv
    rw [abs_sub_comm, abs_of_nonneg hnonneg] at hgap
    calc
      ((v pivot : Nat) : Real) - (u pivot : Nat) <=
          2 * gamma / (delta * |normal pivot|) +
            4 * ((n + 1 : Nat) : Real) := hgap
      _ <= (Nat.ceil (2 * gamma / (delta * |normal pivot|)) : Real) +
          4 * ((n + 1 : Nat) : Real) :=
        add_le_add hceil (le_refl _)
      _ = ((Nat.ceil (2 * gamma / (delta * |normal pivot|)) +
          4 * (n + 1) : Nat) : Real) := by norm_num
  exact_mod_cast hgapCast

/-- A fixed-width nonzero affine slab meets only codimension-one many
bounded natural-grid anchors, with the exact rounded pivot width. -/
theorem card_typeIIAffineThickSlabAnchors_le
    {n : Nat} {delta gamma : Real}
    (hdelta : 0 < delta) (hgamma : 0 <= gamma)
    (normal : Fin (n + 1) -> Real) (bound : Real) :
    (typeIIAffineThickSlabAnchors delta gamma normal bound).card <=
      (Nat.ceil (2 * gamma /
          (delta * |normal (typeIIAffineMaxAbsCoordinate normal)|)) +
        4 * (n + 1) + 1) *
          typeIINaturalCubeGridSide delta ^ n := by
  classical
  by_cases hnormal : normal = 0
  · simp [typeIIAffineThickSlabAnchors, hnormal]
  let pivot := typeIIAffineMaxAbsCoordinate normal
  let slab := typeIIAffineThickSlabAnchors delta gamma normal bound
  let tailGrid := typeIINaturalCubeGrid n delta
  let width := Nat.ceil (2 * gamma / (delta * |normal pivot|)) +
    4 * (n + 1)
  change slab.card <= (width + 1) *
    typeIINaturalCubeGridSide delta ^ n
  rw [← card_typeIINaturalCubeGrid n delta]
  change slab.card <= (width + 1) * tailGrid.card
  refine Finset.card_le_mul_card_image_of_maps_to
    (f := fun anchor => pivot.removeNth anchor)
    (s := slab) (t := tailGrid) ?_ (width + 1) ?_
  · intro anchor hanchor
    rw [mem_typeIINaturalCubeGrid]
    intro i
    have hgrid := (mem_typeIIAffineThickSlabAnchors.mp hanchor).1
    exact (mem_typeIINaturalCubeGrid.mp hgrid) (pivot.succAbove i)
  · intro tail htail
    let fiber := {anchor ∈ slab | pivot.removeNth anchor = tail}
    let values := fiber.image fun anchor => anchor pivot
    have hinjective : Set.InjOn
        (fun anchor : Fin (n + 1) -> Nat => anchor pivot)
        (↑fiber : Set (Fin (n + 1) -> Nat)) := by
      intro u hu v hv huv
      have huremove : pivot.removeNth u = tail :=
        (Finset.mem_filter.mp hu).2
      have hvremove : pivot.removeNth v = tail :=
        (Finset.mem_filter.mp hv).2
      apply (Fin.insertNthEquiv (fun _ : Fin (n + 1) => Nat) pivot).symm.injective
      rw [Fin.insertNthEquiv_symm_apply, Fin.insertNthEquiv_symm_apply]
      exact Prod.ext huv (huremove.trans hvremove.symm)
    have hcard : fiber.card = values.card := by
      exact (Finset.card_image_iff.mpr hinjective).symm
    have hdiameter :
        ∀ a ∈ values, ∀ b ∈ values, a <= b -> b - a <= width := by
      intro a ha b hb hab
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
      have huSlab : u ∈ slab := (Finset.mem_filter.mp hu).1
      have hvSlab : v ∈ slab := (Finset.mem_filter.mp hv).1
      have hremove : pivot.removeNth u = pivot.removeNth v :=
        (Finset.mem_filter.mp hu).2.trans
          (Finset.mem_filter.mp hv).2.symm
      exact typeIIAffineThickSlabAnchor_sub_le hdelta hgamma
        huSlab hvSlab hremove hab
    calc
      {anchor ∈ slab | pivot.removeNth anchor = tail}.card =
          fiber.card := rfl
      _ = values.card := hcard
      _ <= width + 1 :=
        card_nat_finset_le_add_one_of_sub_le values width hdiameter

end

end PrimesRestrictedDigits
