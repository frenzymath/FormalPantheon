import PrimesRestrictedDigits.SieveAsymptotics.TypeIIInteriorNormalization
import PrimesRestrictedDigits.SieveAsymptotics.TypeIICubeInternalError
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIWeightedOneCell

/-!
# Interior Type II cube-family discrepancy

This combines the additive Boolean/Lambda normalization with the two terminal inputs already
proved for the interior family: controls the positive support-mass error and controls every
weighted cell. It is the interior contribution in Eqs. (9.10)--(9.11) of
`MAYNARD-PRD-PUBLISHED`.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private theorem norm_typeIIWeightedCellDiscrepancy_eq_abs
    (digit : Fin 10) (length k : Nat) (a : Fin k -> Real)
    (delta eta : Real) :
    let XNat : Nat := 10 ^ length
    let X : Real := (XNat : Real)
    let A : Finset Nat := paddedRestrictedNumbers digit length
    let B : Finset Nat := maynardAmbientCarrier X
    let w : Nat -> Real := majorArcRegionWeightAtProduct XNat a delta eta
    let lambda : Real :=
      (restrictedDigitDensity digit : Real) * (A.card : Real) / X
    ‖(∑ m ∈ A, (w m : Complex)) -
        (restrictedDigitDensity digit : Complex) * (A.card : Complex) *
          majorArcRegionTotalWeight XNat a delta eta /
            (XNat : Complex)‖ =
      |(∑ m ∈ A, w m) - lambda * (∑ n ∈ B, w n)| := by
  dsimp only
  rw [maynardAmbientCarrier_natCast]
  unfold majorArcRegionTotalWeight
  rw [← Complex.ofReal_sum, ← Complex.ofReal_sum]
  have hcast :
      (↑(∑ i ∈ paddedRestrictedNumbers digit length,
          majorArcRegionWeightAtProduct (10 ^ length) a delta eta i) -
        (restrictedDigitDensity digit : Complex) *
          ((paddedRestrictedNumbers digit length).card : Complex) *
          ↑(∑ i ∈ Finset.range (10 ^ length),
            majorArcRegionWeightAtProduct (10 ^ length) a delta eta i) /
          ((10 ^ length : Nat) : Complex)) =
        (((∑ i ∈ paddedRestrictedNumbers digit length,
            majorArcRegionWeightAtProduct (10 ^ length) a delta eta i) -
          (restrictedDigitDensity digit : Real) *
            ((paddedRestrictedNumbers digit length).card : Real) /
              ((10 ^ length : Nat) : Real) *
            (∑ i ∈ Finset.range (10 ^ length),
              majorArcRegionWeightAtProduct (10 ^ length) a delta eta i) : Real) :
          Complex) := by
    push_cast
    ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs]

private theorem typeIIInteriorFamily_scalar
    (eta floor logX Crough delta card anchorCard total : Real)
    (ell : Nat) (heta : 0 < eta) (hfloor : 0 < floor)
    (hlog : 0 < logX) (hCrough : 0 <= Crough)
    (hdelta : 0 <= delta) (hcard : 0 <= card)
    (hanchorCard : 0 <= anchorCard)
    (hbound : floor * logX ^ ell * total <=
      229 * anchorCard * card / logX +
        (4 / eta) * logX ^ ell * (delta * Crough * card / logX)) :
    total <= (229 / floor + 4 * Crough / (eta * floor)) *
      (anchorCard * card / logX ^ (ell + 1) + delta * card / logX) := by
  have hdenom : 0 < floor * logX ^ ell :=
    mul_pos hfloor (pow_pos hlog ell)
  have hdivide : total <=
      (229 * anchorCard * card / logX +
        (4 / eta) * logX ^ ell * (delta * Crough * card / logX)) /
          (floor * logX ^ ell) := by
    apply (le_div_iff₀ hdenom).2
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hbound
  have heq :
      (229 * anchorCard * card / logX +
        (4 / eta) * logX ^ ell * (delta * Crough * card / logX)) /
          (floor * logX ^ ell) =
        (229 / floor) * (anchorCard * card / logX ^ (ell + 1)) +
          (4 * Crough / (eta * floor)) * (delta * card / logX) := by
    field_simp [heta.ne', hfloor.ne', hlog.ne']
    ring
  rw [heq] at hdivide
  let t1 : Real := anchorCard * card / logX ^ (ell + 1)
  let t2 : Real := delta * card / logX
  let c1 : Real := 229 / floor
  let c2 : Real := 4 * Crough / (eta * floor)
  have ht1 : 0 <= t1 := by dsimp [t1]; positivity
  have ht2 : 0 <= t2 := by dsimp [t2]; positivity
  have hc1 : c1 <= c1 + c2 := by
    apply le_add_of_nonneg_right
    dsimp [c2]
    positivity
  have hc2 : c2 <= c1 + c2 := by
    apply le_add_of_nonneg_left
    dsimp [c1]
    positivity
  apply hdivide.trans
  change c1 * t1 + c2 * t2 <= (c1 + c2) * (t1 + t2)
  calc
    c1 * t1 + c2 * t2 <= (c1 + c2) * t1 + (c1 + c2) * t2 :=
      add_le_add (mul_le_mul_of_nonneg_right hc1 ht1)
        (mul_le_mul_of_nonneg_right hc2 ht2)
    _ = (c1 + c2) * (t1 + t2) := by ring

set_option maxHeartbeats 1200000 in
/--
The eta-uniform interior-family Boolean discrepancy bound.
-/
theorem exists_typeIIInteriorCubeFamilyError_eta_upper
    (eta : Real) (heta : 0 < eta) :
    ∃ Ceta : Real, 0 < Ceta ∧
      ∀ mu : Real, 0 < mu ->
        ∃ length0 : Nat, 1 <= length0 ∧
          ∀ length : Nat, length0 <= length ->
          ∀ (digit : Fin 10) (k : Nat)
            (anchors : Finset (Fin k -> Nat)),
            let XNat : Nat := 10 ^ length
            let X : Real := (XNat : Real)
            let delta : Real := majorArcM2LogLogDelta XNat
            let A : Finset Nat := paddedRestrictedNumbers digit length
            let B : Finset Nat := maynardAmbientCarrier X
            let tupleFamily : (Fin k -> Nat) ->
                Finset (Fin (k + 1) -> Nat) := fun anchor =>
              majorArcPrimeTuples XNat
                (scaledNaturalCubeAnchor delta anchor) delta eta
            let supportCount : (Fin k -> Nat) -> Finset Nat -> Real :=
              fun anchor C =>
                (((primeTupleProductSupport (tupleFamily anchor)).filter
                  (fun n => n ∈ C)).card : Real)
            1 <= k ->
            (((k + 1 : Nat) : Real) <= 2 / eta) ->
            (∀ anchor ∈ anchors, ∀ i,
              eta / 2 <= scaledNaturalCubeAnchor delta anchor i) ->
            (∀ anchor ∈ anchors,
              (∑ i, scaledNaturalCubeAnchor delta anchor i) <
                1 - eta / 2) ->
            (∀ anchor ∈ anchors,
              typeIIInteriorCellSeparated
                (scaledNaturalCubeAnchor delta anchor) delta) ->
            (∀ anchor ∈ anchors, ∃ I : Finset (Fin k),
              (∑ i ∈ I, scaledNaturalCubeAnchor delta anchor i) ∈
                    Set.Icc (9 / 25 + mu) (17 / 40 - mu) ∨
                (∑ i ∈ I, scaledNaturalCubeAnchor delta anchor i) ∈
                    Set.Icc (23 / 40 + mu) (16 / 25 - mu)) ->
            (∑ anchor ∈ anchors,
              |supportCount anchor A -
                (restrictedDigitDensity digit : Real) *
                    (A.card : Real) / X * supportCount anchor B|) <=
              Ceta *
                (((anchors.card : Real) * (A.card : Real) /
                    Real.log X ^ (k + 2)) +
                  delta * (A.card : Real) / Real.log X) := by
  obtain ⟨Crough, hCrough, roughLength, hroughLength, hrough⟩ :=
    exists_majorArcCubeInternalError_eta_upper eta heta
  have hweighted := exists_typeIIWeightedOneCellLogError eta heta
  let floor : Real := typeIIEtaCellFloor eta
  let Ceta : Real :=
    229 / floor + 4 * Crough / (eta * floor)
  have hfloorPos : 0 < floor := by
    simpa only [floor] using typeIIEtaCellFloor_pos heta
  have hCeta : 0 < Ceta := by
    dsimp only [Ceta]
    positivity
  refine ⟨Ceta, hCeta, ?_⟩
  intro mu hmu
  obtain ⟨weightedLength, hweightedLength, hweightedAt⟩ :=
    hweighted mu hmu
  let length0 := max roughLength weightedLength
  refine ⟨length0, hroughLength.trans (le_max_left _ _), ?_⟩
  intro length hlength digit k anchors
  have hlengths : roughLength <= length ∧ weightedLength <= length := by
    simpa only [length0, max_le_iff] using hlength
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let delta : Real := majorArcM2LogLogDelta XNat
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let tupleFamily : (Fin k -> Nat) ->
      Finset (Fin (k + 1) -> Nat) := fun anchor =>
    majorArcPrimeTuples XNat
      (scaledNaturalCubeAnchor delta anchor) delta eta
  let supportCount : (Fin k -> Nat) -> Finset Nat -> Real :=
    fun anchor C =>
      (((primeTupleProductSupport (tupleFamily anchor)).filter
        (fun n => n ∈ C)).card : Real)
  dsimp only
  intro _hk hell hmargin hroom hseparated hconvenient
  let L : Real := Real.log X
  let card : Real := (A.card : Real)
  let lambda : Real :=
    (restrictedDigitDensity digit : Real) * card / X
  let weightSum : (Fin k -> Nat) -> Finset Nat -> Real :=
    fun anchor C =>
      ∑ n ∈ C, majorArcRegionWeightAtProduct XNat
        (scaledNaturalCubeAnchor delta anchor) delta eta n
  let discrepancy : (Fin k -> Nat) -> Real := fun anchor =>
    |supportCount anchor A - lambda * supportCount anchor B|
  let mass : (Fin k -> Nat) -> Real := fun anchor =>
    supportCount anchor A + lambda * supportCount anchor B
  have hlengthOne : 1 <= length := hroughLength.trans hlengths.1
  have hXNat : 1 < XNat := by
    dsimp only [XNat]
    exact Nat.one_lt_pow (by omega : length ≠ 0)
      (by norm_num : 1 < (10 : Nat))
  have hX : 1 < X := by
    dsimp only [X]
    exact_mod_cast hXNat
  have hL : 1 < L := by
    dsimp only [L, X]
    have htenLe : 10 <= XNat := by
      dsimp only [XNat]
      simpa using
        (Nat.pow_le_pow_right (by norm_num : 0 < (10 : Nat)) hlengthOne)
    exact (Real.lt_log_iff_exp_lt (by positivity)).mpr <|
      Real.exp_one_lt_three.trans_le
        (by exact_mod_cast ((by omega : 3 <= XNat)))
  have hdelta : 0 < delta := by
    dsimp only [delta, majorArcM2LogLogDelta]
    exact inv_pos.mpr (Real.log_pos hL)
  have hlambda : 0 <= lambda := by
    have hrho : 0 <= (restrictedDigitDensity digit : Real) := by
      rw [restrictedDigitDensity_eq]
      split_ifs <;> norm_num
    dsimp only [lambda, card]
    positivity
  have hweightedReal (anchor : Fin k -> Nat) (hanchor : anchor ∈ anchors) :
      |weightSum anchor A - lambda * weightSum anchor B| <=
        229 * card / L := by
    obtain ⟨I, hI⟩ := hconvenient anchor hanchor
    have hbound := hweightedAt length hlengths.2 digit k
      (scaledNaturalCubeAnchor delta anchor) I
      (hmargin anchor hanchor) (hroom anchor hanchor) hell hI
    rw [norm_typeIIWeightedCellDiscrepancy_eq_abs digit length k
      (scaledNaturalCubeAnchor delta anchor) delta eta] at hbound
    simpa only [weightSum, lambda, card, L, A, B, X, XNat, delta] using hbound
  have hlocal (anchor : Fin k -> Nat) (hanchor : anchor ∈ anchors) :
      floor * L ^ (k + 1) * discrepancy anchor <=
        229 * card / L +
          (4 / eta) * delta * L ^ (k + 1) * mass anchor := by
    have hnormalization :=
      typeIICellScale_mul_abs_supportCount_sub_mul_supportCount_le
        A B hXNat heta hdelta.le hlambda (hmargin anchor hanchor)
          (hroom anchor hanchor) (hseparated anchor hanchor)
    have hcoefficient :
        floor <= typeIICellCoefficient
          (scaledNaturalCubeAnchor delta anchor) := by
      simpa only [floor] using
        typeIIEtaCellFloor_le_typeIICellCoefficient heta
          (hmargin anchor hanchor) (hroom anchor hanchor) hell
    have hscale :
        floor * L ^ (k + 1) <=
          typeIICellCoefficient (scaledNaturalCubeAnchor delta anchor) *
            L ^ (k + 1) :=
      mul_le_mul_of_nonneg_right hcoefficient (by positivity)
    have hfirst :
        floor * L ^ (k + 1) * discrepancy anchor <=
          |weightSum anchor A - lambda * weightSum anchor B| +
            (2 * ((k + 1 : Nat) : Real) * delta * L ^ (k + 1)) *
              mass anchor := by
      apply (mul_le_mul_of_nonneg_right hscale
        (abs_nonneg _)).trans
      simpa only [discrepancy, mass, weightSum, supportCount, tupleFamily,
        lambda, XNat, delta] using hnormalization
    have harity : 2 * ((k + 1 : Nat) : Real) <= 4 / eta := by
      calc
        2 * ((k + 1 : Nat) : Real) <= 2 * (2 / eta) :=
          mul_le_mul_of_nonneg_left hell (by norm_num)
        _ = 4 / eta := by ring
    have herrorScale :
        2 * ((k + 1 : Nat) : Real) * delta * L ^ (k + 1) <=
          (4 / eta) * delta * L ^ (k + 1) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right harity hdelta.le) (by positivity)
    have hmass : 0 <= mass anchor := by
      dsimp only [mass, supportCount]
      positivity
    exact hfirst.trans <| add_le_add (hweightedReal anchor hanchor)
      (mul_le_mul_of_nonneg_right herrorScale hmass)
  have hsumLocal :
      floor * L ^ (k + 1) *
          (∑ anchor ∈ anchors, discrepancy anchor) <=
        229 * (anchors.card : Real) * card / L +
          (4 / eta) * L ^ (k + 1) *
            (delta * ∑ anchor ∈ anchors, mass anchor) := by
    calc
      floor * L ^ (k + 1) *
          (∑ anchor ∈ anchors, discrepancy anchor) =
          ∑ anchor ∈ anchors,
            floor * L ^ (k + 1) * discrepancy anchor := by
        rw [Finset.mul_sum]
      _ <= ∑ anchor ∈ anchors,
          (229 * card / L +
            (4 / eta) * delta * L ^ (k + 1) * mass anchor) := by
        exact Finset.sum_le_sum fun anchor hanchor => hlocal anchor hanchor
      _ = 229 * (anchors.card : Real) * card / L +
          (4 / eta) * L ^ (k + 1) *
            (delta * ∑ anchor ∈ anchors, mass anchor) := by
        rw [Finset.sum_add_distrib, Finset.sum_const]
        rw [← Finset.mul_sum]
        ring
  have hroughAt := hrough length hlengths.1 digit k delta hdelta.le hell
    anchors hmargin
  have hmassSum :
      (∑ anchor ∈ anchors, mass anchor) =
        (∑ anchor ∈ anchors, supportCount anchor A) +
          lambda * (∑ anchor ∈ anchors, supportCount anchor B) := by
    dsimp only [mass]
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hroughMass :
      delta * (∑ anchor ∈ anchors, mass anchor) <=
        delta * (Crough * card / L) := by
    rw [hmassSum]
    simpa only [supportCount, tupleFamily, lambda, card, L, A, B, X,
      XNat, delta] using hroughAt
  have hcombined :
      floor * L ^ (k + 1) *
          (∑ anchor ∈ anchors, discrepancy anchor) <=
        229 * (anchors.card : Real) * card / L +
          (4 / eta) * L ^ (k + 1) *
            (delta * Crough * card / L) := by
    apply hsumLocal.trans
    have hfactor : 0 <= (4 / eta) * L ^ (k + 1) := by positivity
    have hroughMass' :
        delta * (∑ anchor ∈ anchors, mass anchor) <=
          delta * Crough * card / L := by
      calc
        delta * (∑ anchor ∈ anchors, mass anchor) <=
            delta * (Crough * card / L) := hroughMass
        _ = delta * Crough * card / L := by ring
    exact add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hroughMass' hfactor)
  have hscalar := typeIIInteriorFamily_scalar eta floor L Crough delta card
    (anchors.card : Real) (∑ anchor ∈ anchors, discrepancy anchor) (k + 1)
    heta hfloorPos (zero_lt_one.trans hL) hCrough.le hdelta.le
    (by positivity) (by positivity) hcombined
  have hexponent : k + 1 + 1 = k + 2 := by omega
  simpa only [Ceta, discrepancy, lambda, card, L, A, B, X, delta,
    supportCount, tupleFamily, hexponent] using hscalar

end

end PrimesRestrictedDigits
