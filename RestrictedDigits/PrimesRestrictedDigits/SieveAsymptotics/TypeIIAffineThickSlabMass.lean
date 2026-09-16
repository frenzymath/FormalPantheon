import PrimesRestrictedDigits.SieveAsymptotics.TypeIIAffineThickSlabCount
import PrimesRestrictedDigits.SieveAsymptotics.TypeIICellSupportMass
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIWeakSmallProductTailScalars

/-!
# Positive Type II support mass in one thick affine slab

This combines the finite thick-slab count with the established positive one-cell support
estimate. It is the fixed-width boundary-mass calculation in the proof of Lemma 7.3 of
`MAYNARD-PRD-PUBLISHED`, pp. 150--152.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- Multiplication by the full projected cell volume cancels the thick-slab
grid count down to an explicit fixed-width plus cell-width expression. -/
theorem card_typeIIAffineThickSlabAnchors_mul_delta_pow_le
    {n : Nat} {delta gamma : Real}
    (hdelta : 0 < delta) (hdeltaOne : delta <= 1)
    (hgamma : 0 <= gamma) (normal : Fin (n + 1) -> Real)
    (hnormal : normal ≠ 0) (bound : Real) :
    ((typeIIAffineThickSlabAnchors delta gamma normal bound).card : Real) *
        delta ^ (n + 1) <=
      (2 : Real) ^ n *
        (2 * gamma /
            |normal (typeIIAffineMaxAbsCoordinate normal)| +
          ((4 * (n + 1) + 2 : Nat) : Real) * delta) := by
  let pivot := typeIIAffineMaxAbsCoordinate normal
  let maxAbs : Real := |normal pivot|
  let quotient : Real := 2 * gamma / (delta * maxAbs)
  let width : Nat := Nat.ceil quotient + 4 * (n + 1) + 1
  let side : Nat := typeIINaturalCubeGridSide delta
  let slab := typeIIAffineThickSlabAnchors delta gamma normal bound
  have hmaxAbs : 0 < maxAbs := by
    simpa only [maxAbs, pivot] using
      abs_typeIIAffineMaxAbsCoordinate_pos hnormal
  have hquotient : 0 <= quotient := by
    dsimp only [quotient]
    positivity
  have hcardNat : slab.card <= width * side ^ n := by
    simpa only [slab, width, side, quotient, maxAbs, pivot] using
      card_typeIIAffineThickSlabAnchors_le hdelta hgamma normal bound
  have hcard : (slab.card : Real) <=
      (width : Real) * (side : Real) ^ n := by
    exact_mod_cast hcardNat
  have hside : (side : Real) <= 2 / delta := by
    simpa only [side] using
      typeIINaturalCubeGridSide_cast_le_two_div hdelta hdeltaOne
  have hsidePow : (side : Real) ^ n <= (2 / delta) ^ n :=
    pow_le_pow_left₀ (by positivity) hside n
  have hscale : 0 <= delta ^ (n + 1) := by positivity
  have hwidthDelta : (width : Real) * delta <=
      2 * gamma / maxAbs +
        ((4 * (n + 1) + 2 : Nat) : Real) * delta := by
    have hceil : (Nat.ceil quotient : Real) <= quotient + 1 :=
      (Nat.ceil_lt_add_one hquotient).le
    have hcast : ((4 * (n + 1) + 2 : Nat) : Real) =
        4 * ((n + 1 : Nat) : Real) + 2 := by
      norm_num
    calc
      (width : Real) * delta =
          ((Nat.ceil quotient : Real) +
              4 * ((n + 1 : Nat) : Real) + 1) * delta := by
        dsimp only [width]
        push_cast
        ring
      _ <= (quotient + 1 + 4 * ((n + 1 : Nat) : Real) + 1) *
          delta := mul_le_mul_of_nonneg_right (by linarith) hdelta.le
      _ = 2 * gamma / maxAbs +
          ((4 * (n + 1) + 2 : Nat) : Real) * delta := by
        rw [hcast]
        dsimp only [quotient]
        field_simp [hdelta.ne', hmaxAbs.ne']
        ring
  calc
    (slab.card : Real) * delta ^ (n + 1) <=
        ((width : Real) * (side : Real) ^ n) * delta ^ (n + 1) :=
      mul_le_mul_of_nonneg_right hcard hscale
    _ <= ((width : Real) * (2 / delta) ^ n) * delta ^ (n + 1) := by
      gcongr
    _ = (2 : Real) ^ n * ((width : Real) * delta) := by
      rw [div_pow, pow_succ]
      field_simp [hdelta.ne']
    _ <= (2 : Real) ^ n *
        (2 * gamma / maxAbs +
          ((4 * (n + 1) + 2 : Nat) : Real) * delta) :=
      mul_le_mul_of_nonneg_left hwidthDelta (by positivity)
    _ = (2 : Real) ^ n *
        (2 * gamma /
            |normal (typeIIAffineMaxAbsCoordinate normal)| +
          ((4 * (n + 1) + 2 : Nat) : Real) * delta) := by
      rfl

set_option maxHeartbeats 2400000 in
/-- The eta-uniform positive support mass of any locally admissible subfamily
of one nonzero thick affine slab. -/
theorem exists_typeIIAffineThickSlabSupportMass_eta_upper
    (eta : Real) (heta : 0 < eta) :
    ∃ Ceta : Real, 0 < Ceta ∧
      ∀ mu : Real, 0 < mu ->
        ∃ length0 : Nat, 1 <= length0 ∧
          ∀ length : Nat, length0 <= length ->
          ∀ (digit : Fin 10) (n : Nat)
            (normal : Fin (n + 1) -> Real) (bound gamma : Real)
            (anchors : Finset (Fin (n + 1) -> Nat)),
            let XNat : Nat := 10 ^ length
            let X : Real := (XNat : Real)
            let delta : Real := majorArcM2LogLogDelta XNat
            let A : Finset Nat := paddedRestrictedNumbers digit length
            let B : Finset Nat := maynardAmbientCarrier X
            let supportCount : (Fin (n + 1) -> Nat) -> Finset Nat -> Real :=
              fun anchor C => typeIICellSupportCount XNat
                (scaledNaturalCubeAnchor delta anchor) delta eta C
            normal ≠ 0 ->
            0 <= gamma ->
            (((n + 2 : Nat) : Real) <= 2 / eta) ->
            anchors ⊆
              typeIIAffineThickSlabAnchors delta gamma normal bound ->
            (∀ anchor ∈ anchors, ∀ i,
              eta / 2 <= scaledNaturalCubeAnchor delta anchor i) ->
            (∀ anchor ∈ anchors,
              (∑ i, scaledNaturalCubeAnchor delta anchor i) <
                1 - eta / 2) ->
            (∀ anchor ∈ anchors, ∃ I : Finset (Fin (n + 1)),
              (∑ i ∈ I, scaledNaturalCubeAnchor delta anchor i) ∈
                    Set.Icc (9 / 25 + mu) (17 / 40 - mu) ∨
                (∑ i ∈ I, scaledNaturalCubeAnchor delta anchor i) ∈
                    Set.Icc (23 / 40 + mu) (16 / 25 - mu)) ->
            anchors.sum (fun anchor =>
                supportCount anchor A +
                  (restrictedDigitDensity digit : Real) *
                    (A.card : Real) / X * supportCount anchor B) <=
              Ceta *
                ((delta + (2 : Real) ^ n *
                    (2 * gamma /
                        |normal (typeIIAffineMaxAbsCoordinate normal)| +
                      ((4 * (n + 1) + 2 : Nat) : Real) * delta)) *
                  (A.card : Real) / Real.log X) := by
  obtain ⟨Ccell, hCcell, hcell⟩ :=
    exists_typeIIOneCellSupportMass_eta_upper eta heta
  obtain ⟨scaleLength, hscaleLength, hscale⟩ :=
    exists_typeIIWeakSmallProductScaleThreshold
  refine ⟨Ccell, hCcell, ?_⟩
  intro mu hmu
  obtain ⟨cellLength, hcellLength, hcellAt⟩ := hcell mu hmu
  let length0 := max cellLength scaleLength
  refine ⟨length0, hcellLength.trans (Nat.le_max_left _ _), ?_⟩
  intro length hlength digit n normal bound gamma anchors
  have hcellLengthAt : cellLength <= length :=
    (Nat.le_max_left _ _).trans hlength
  have hscaleLengthAt : scaleLength <= length :=
    (Nat.le_max_right _ _).trans hlength
  have hlengthOne : 1 <= length := hcellLength.trans hcellLengthAt
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let delta : Real := majorArcM2LogLogDelta XNat
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let supportCount : (Fin (n + 1) -> Nat) -> Finset Nat -> Real :=
    fun anchor C => typeIICellSupportCount XNat
      (scaledNaturalCubeAnchor delta anchor) delta eta C
  dsimp only
  intro hnormal hgamma hell hanchors hmargin hroom hconvenient
  let lambda : Real :=
    (restrictedDigitDensity digit : Real) * (A.card : Real) / X
  let mass : (Fin (n + 1) -> Nat) -> Real := fun anchor =>
    supportCount anchor A + lambda * supportCount anchor B
  let card : Real := (A.card : Real)
  let L : Real := Real.log X
  let slabFactor : Real := (2 : Real) ^ n *
    (2 * gamma / |normal (typeIIAffineMaxAbsCoordinate normal)| +
      ((4 * (n + 1) + 2 : Nat) : Real) * delta)
  let first : Real := (anchors.card : Real) * card / L ^ (n + 3)
  let second : Real :=
    (anchors.card : Real) * delta ^ (n + 1) * card / L
  have hscaleAt := hscale length hscaleLengthAt
  dsimp only at hscaleAt
  have hdelta : 0 < delta := by
    simpa only [delta, XNat] using hscaleAt.2.1
  have hdeltaOne : delta <= 1 := by
    have hdeltaHalf := hscaleAt.2.2.1
    dsimp only [delta, XNat]
    linarith
  have hlocal (anchor : Fin (n + 1) -> Nat) (hanchor : anchor ∈ anchors) :
      mass anchor <= Ccell *
        (card / L ^ (n + 3) + delta ^ (n + 1) * card / L) := by
    obtain ⟨I, hI⟩ := hconvenient anchor hanchor
    have hbound := hcellAt length hcellLengthAt digit (n + 1)
      (scaledNaturalCubeAnchor delta anchor) I
      (hmargin anchor hanchor) (hroom anchor hanchor) (by
        simpa only [Nat.add_assoc] using hell) hI
    simpa only [mass, supportCount, lambda, card, L, A, B, X, XNat,
      delta, show n + 1 + 2 = n + 3 by omega] using hbound
  have hsumLocal : anchors.sum mass <= Ccell * (first + second) := by
    calc
      anchors.sum mass <= anchors.sum (fun _anchor => Ccell *
          (card / L ^ (n + 3) + delta ^ (n + 1) * card / L)) :=
        Finset.sum_le_sum hlocal
      _ = Ccell * (first + second) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        dsimp only [first, second]
        ring
  have hgrid : anchors ⊆ typeIINaturalCubeGrid (n + 1) delta := by
    intro anchor hanchor
    exact (mem_typeIIAffineThickSlabAnchors.mp (hanchors hanchor)).1
  have hcardNonneg : 0 <= card := by
    dsimp only [card]
    positivity
  have hfirst : first <= delta * card / L := by
    have hbound := typeIIAnchorFamily_logError_le_delta_logError
      hlengthOne anchors (by
        simpa only [delta, XNat] using hgrid) card hcardNonneg
    simpa only [first, card, L, X, XNat, delta,
      show n + 1 + 2 = n + 3 by omega] using hbound
  have hslabCard :
      (anchors.card : Real) <=
        ((typeIIAffineThickSlabAnchors delta gamma normal bound).card : Real) := by
    exact_mod_cast Finset.card_le_card hanchors
  have hcardDelta : (anchors.card : Real) * delta ^ (n + 1) <=
      slabFactor := by
    calc
      (anchors.card : Real) * delta ^ (n + 1) <=
          ((typeIIAffineThickSlabAnchors delta gamma normal bound).card : Real) *
            delta ^ (n + 1) :=
        mul_le_mul_of_nonneg_right hslabCard (by positivity)
      _ <= slabFactor := by
        simpa only [slabFactor] using
          card_typeIIAffineThickSlabAnchors_mul_delta_pow_le hdelta hdeltaOne
            hgamma normal hnormal bound
  have hsecond : second <= slabFactor * card / L := by
    have hcardOverLog : 0 <= card / L := by
      have hXOne : (1 : Real) < X := by
        dsimp only [X, XNat]
        linarith [hscaleAt.1]
      positivity
    have hmul := mul_le_mul_of_nonneg_right hcardDelta hcardOverLog
    dsimp only [second]
    calc
      (anchors.card : Real) * delta ^ (n + 1) * card / L =
          ((anchors.card : Real) * delta ^ (n + 1)) * (card / L) := by ring
      _ <= slabFactor * (card / L) := hmul
      _ = slabFactor * card / L := by ring
  apply hsumLocal.trans
  calc
    Ccell * (first + second) <=
        Ccell * (delta * card / L + slabFactor * card / L) :=
      mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hCcell.le
    _ = Ccell * ((delta + slabFactor) * card / L) := by ring
    _ = Ccell *
        ((delta + (2 : Real) ^ n *
            (2 * gamma /
                |normal (typeIIAffineMaxAbsCoordinate normal)| +
              ((4 * (n + 1) + 2 : Nat) : Real) * delta)) *
          (A.card : Real) / Real.log X) := by
      rfl

end

end PrimesRestrictedDigits
