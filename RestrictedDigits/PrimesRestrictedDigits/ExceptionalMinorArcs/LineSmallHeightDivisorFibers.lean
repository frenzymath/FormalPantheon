import PrimesRestrictedDigits.ExceptionalMinorArcs.LineSmallHeightPrefixes
import PrimesRestrictedDigits.ExceptionalMinorArcs.LineZeroCoefficientFiberCount
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombination

/-!
# Initial divisor fibers in the small-height normalized count

This counts the outer key, the determined `(b1,a2)` factor pair, and the two primitive
coefficient factor pairs in the proof of equation `(15.4)` of `MAYNARD-PRD-PUBLISHED`.
-/

namespace PrimesRestrictedDigits

/-- The target whose factor pairs determine `b1` and `a2`. -/
def lineSmallHeightCrossFactorTarget {X : Nat}
    (key : LineSmallHeightKey X) : Int :=
  -(key.b2 * (key.a2Prime.val : Int) + key.b3 * (X : Int) + key.b4)

/-- Ambient box for the outer prefix `(a2',b2,b3,b4)`. -/
noncomputable def lineSmallHeightOuterKeyBox
    {X : Nat} (D : Finset (Fin X)) (W : Real) :
    Finset (LineSmallHeightKey X) :=
  (D.product ((lineCoefficientBox W).product
      ((lineCoefficientBox W).product (lineCoefficientBox W)))).image
    fun key =>
      { a2Prime := key.1
        b2 := key.2.1
        b3 := key.2.2.1
        b4 := key.2.2.2 }

private theorem lineSmallHeight_crossCoefficient_natAbs_le_envelope
    {length : Nat} {V U : Real} {z : Int}
    (hU : 0 ≤ U) (hUX : U ≤ ((10 ^ length : Nat) : Real))
    (hV : 0 ≤ V) (hVX : V ≤ ((10 ^ length : Nat) : Real))
    (hz : z ∈ lineCoefficientBox (2 * U * V)) :
    (z.natAbs : Real) ≤
      6 * (((10 ^ length : Nat) : Real) ^ 3) := by
  let X : Real := ((10 ^ length : Nat) : Real)
  have hX : 1 ≤ X := by
    dsimp only [X]
    rw [Nat.cast_pow]
    exact one_le_pow₀ (by norm_num)
  have hzAbs : abs (z : Real) ≤ 2 * U * V :=
    (mem_lineCoefficientBox_iff (by positivity)).mp hz
  have htwoSq : 2 * U * V ≤ 2 * X ^ 2 := by
    dsimp only [X] at hUX hVX ⊢
    calc
      2 * U * V ≤ 2 * X * X := by gcongr
      _ = 2 * X ^ 2 := by ring
  have hsqCube : 2 * X ^ 2 ≤ 6 * X ^ 3 := by
    have hlinear : 0 ≤ 3 * X - 1 := by linarith
    have haux : 0 ≤ X ^ 2 * (3 * X - 1) :=
      mul_nonneg (sq_nonneg X) hlinear
    nlinarith
  calc
    (z.natAbs : Real) = abs (z : Real) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    _ ≤ 2 * U * V := hzAbs
    _ ≤ 2 * X ^ 2 := htwoSq
    _ ≤ 6 * X ^ 3 := hsqCube

private theorem lineSmallHeight_crossCoefficient_mul_fin_natAbs_le_envelope
    {length : Nat} {V U : Real} {z : Int}
    {a : Fin (10 ^ length)}
    (hU : 0 ≤ U) (hUX : U ≤ ((10 ^ length : Nat) : Real))
    (hV : 0 ≤ V) (hVX : V ≤ ((10 ^ length : Nat) : Real))
    (hz : z ∈ lineCoefficientBox (2 * U * V)) :
    ((z * (a.val : Int)).natAbs : Real) ≤
      6 * (((10 ^ length : Nat) : Real) ^ 3) := by
  let X : Real := ((10 ^ length : Nat) : Real)
  have ha : (a.val : Real) ≤ X := by
    dsimp only [X]
    exact_mod_cast a.isLt.le
  have hzAbs : abs (z : Real) ≤ 2 * U * V :=
    (mem_lineCoefficientBox_iff (by positivity)).mp hz
  calc
    ((z * (a.val : Int)).natAbs : Real) =
        abs (z : Real) * (a.val : Real) := by
      rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_mul, abs_mul]
      simp
    _ ≤ (2 * U * V) * X := by gcongr
    _ ≤ (2 * X * X) * X := by
      dsimp only [X] at hUX hVX ⊢
      gcongr
    _ ≤ 6 * X ^ 3 := by
      have hXNonneg : 0 ≤ X := by positivity
      nlinarith [mul_nonneg (sq_nonneg X) hXNonneg]

/-- The outer key image has at most `#D` times three coefficient boxes. -/
theorem lineSmallHeightKeyClass_card_real_le
    {length : Nat} (C D : Finset (Fin (10 ^ length))) (V : Real)
    (j : Fin (length + 1)) (hV : 1 ≤ V) :
    ((lineSmallHeightKeyClass length C D V j).card : Real) ≤
      (D.card : Real) *
        ((lineCoefficientBox
          (2 * ((10 ^ j.val : Nat) : Real) * V)).card : Real) ^ 3 := by
  classical
  let U : Real := ((10 ^ j.val : Nat) : Real)
  let W : Real := 2 * U * V
  let outer := lineSmallHeightOuterKeyBox D W
  have hsubset : lineSmallHeightKeyClass length C D V j ⊆ outer := by
    intro key hkey
    obtain ⟨data, hdata, rfl⟩ := Finset.mem_image.mp hkey
    have hfull := (mem_orientedLineNormalizedSecondMomentClass.mp hdata).1
    have hvalid := mem_lineNormalizedSecondMomentClass_isValid hfull
    have hboxes :=
      mem_orientedLineNormalizedSecondMomentClass_cross_mem_boxes hdata hV
    apply Finset.mem_image.mpr
    refine ⟨(data.a2Prime,
      ((lineNormalizedCrossData data).b2,
        ((lineNormalizedCrossData data).b3,
          (lineNormalizedCrossData data).b4))), ?_, rfl⟩
    exact Finset.mem_product.mpr
      ⟨hvalid.a2Prime_mem, Finset.mem_product.mpr
        ⟨hboxes.2.1, Finset.mem_product.mpr ⟨hboxes.2.2.1, hboxes.2.2.2⟩⟩⟩
  have houter :
      (outer.card : Real) ≤
        (D.card : Real) * ((lineCoefficientBox W).card : Real) ^ 3 := by
    have hcardImage : outer.card ≤
        (D.product ((lineCoefficientBox W).product
          ((lineCoefficientBox W).product
            (lineCoefficientBox W)))).card := Finset.card_image_le
    have hcast : (outer.card : Real) ≤
        (D.product ((lineCoefficientBox W).product
          ((lineCoefficientBox W).product
            (lineCoefficientBox W)))).card := by exact_mod_cast hcardImage
    rw [Finset.product_eq_sprod, Finset.card_product,
      Finset.product_eq_sprod, Finset.card_product,
      Finset.product_eq_sprod, Finset.card_product] at hcast
    push_cast at hcast
    calc
      (outer.card : Real) ≤ (D.card : Real) *
          (((lineCoefficientBox W).card : Real) *
            (((lineCoefficientBox W).card : Real) *
              ((lineCoefficientBox W).card : Real))) := hcast
      _ = (D.card : Real) * ((lineCoefficientBox W).card : Real) ^ 3 := by
        ring
  calc
    ((lineSmallHeightKeyClass length C D V j).card : Real) ≤
        (outer.card : Real) := by
      exact_mod_cast Finset.card_le_card hsubset
    _ ≤ (D.card : Real) * ((lineCoefficientBox W).card : Real) ^ 3 := houter
    _ = (D.card : Real) *
        ((lineCoefficientBox
          (2 * ((10 ^ j.val : Nat) : Real) * V)).card : Real) ^ 3 := rfl

/-- The cross-relation fiber contributes one signed divisor factor. -/
theorem lineSmallHeightCrossFactorClass_card_real_le
    {length : Nat} (C D : Finset (Fin (10 ^ length))) (V Q : Real)
    (j : Fin (length + 1)) (hV : 1 ≤ V)
    (hVX : V < ((10 ^ length : Nat) : Real)) (hQ : 0 ≤ Q)
    (hfactor : forall z : Int,
      (z.natAbs : Real) ≤ 6 * (((10 ^ length : Nat) : Real) ^ 3) ->
      (z.divisorsAntidiag.card : Real) ≤ Q) :
    ((lineSmallHeightCrossFactorClass length C D V j).card : Real) ≤
      ((lineSmallHeightKeyClass length C D V j).card : Real) * Q := by
  classical
  let S := lineSmallHeightCrossFactorClass length C D V j
  let outer := lineSmallHeightKeyClass length C D V j
  let key : LineSmallHeightCrossFactor (10 ^ length) ->
      LineSmallHeightKey (10 ^ length) := fun item => item.toLineSmallHeightKey
  let target := lineSmallHeightCrossFactorTarget (X := 10 ^ length)
  let embedding : LineSmallHeightCrossFactor (10 ^ length) -> Prod Int Int :=
    fun item => (item.b1, (item.a2.val : Int))
  apply lineZeroCoefficient_card_nonzero_target_real_le
    S outer key target embedding
    (6 * (((10 ^ length : Nat) : Real) ^ 3)) Q
  · intro item hitem
    obtain ⟨data, hdata, rfl⟩ := Finset.mem_image.mp hitem
    exact Finset.mem_image.mpr ⟨data, hdata, rfl⟩
  · intro item hitem
    obtain ⟨data, hdata, hpref⟩ := Finset.mem_image.mp hitem
    subst item
    have hfull := (mem_orientedLineNormalizedSecondMomentClass.mp hdata).1
    have hvalid := mem_lineNormalizedSecondMomentClass_isValid hfull
    have hproduct :
        lineSmallHeightCrossFactorTarget
            (lineSmallHeightKeyOfData data) =
          (lineNormalizedCrossData data).b1 * (data.a2.val : Int) := by
      have hcross := hvalid.cross_relation
      dsimp only [lineSmallHeightCrossFactorTarget,
        lineSmallHeightKeyOfData, lineNormalizedCrossData] at hcross ⊢
      linear_combination -hcross
    change lineSmallHeightCrossFactorTarget
      (lineSmallHeightKeyOfData data) ≠ 0
    rw [hproduct]
    exact mul_ne_zero hvalid.cross_b1_ne (by exact_mod_cast hvalid.a2_pos.ne')
  · intro item hitem
    obtain ⟨data, hdata, hpref⟩ := Finset.mem_image.mp hitem
    subst item
    have hfull := (mem_orientedLineNormalizedSecondMomentClass.mp hdata).1
    have hvalid := mem_lineNormalizedSecondMomentClass_isValid hfull
    have hcross := hvalid.cross_relation
    dsimp only [embedding, target, key, lineSmallHeightCrossFactorTarget,
      lineSmallHeightCrossFactorOfData, lineSmallHeightKeyOfData,
      lineNormalizedCrossData] at hcross ⊢
    linear_combination hcross
  · intro fixed item hp item' hp' heq
    have hpKey := (Finset.mem_filter.mp hp).2
    have hp'Key := (Finset.mem_filter.mp hp').2
    have hkey : item.toLineSmallHeightKey =
        item'.toLineSmallHeightKey := hpKey.trans hp'Key.symm
    have hb1 := congrArg Prod.fst heq
    have ha2Val : (item.a2.val : Int) = (item'.a2.val : Int) := by
      simpa only [embedding] using congrArg Prod.snd heq
    apply LineSmallHeightCrossFactor.ext
    · exact congrArg LineSmallHeightKey.a2Prime hkey
    · exact congrArg LineSmallHeightKey.b2 hkey
    · exact congrArg LineSmallHeightKey.b3 hkey
    · exact congrArg LineSmallHeightKey.b4 hkey
    · exact hb1
    · apply Fin.ext
      exact_mod_cast ha2Val
  · intro item hitem
    obtain ⟨data, hdata, hpref⟩ := Finset.mem_image.mp hitem
    subst item
    have hboxes :=
      mem_orientedLineNormalizedSecondMomentClass_cross_mem_boxes hdata hV
    have hband := mem_lineNormalizedSecondMomentClass_band
      (mem_orientedLineNormalizedSecondMomentClass.mp hdata).1
    have htarget :
        lineSmallHeightCrossFactorTarget
            (lineSmallHeightKeyOfData data) =
          (lineNormalizedCrossData data).b1 * (data.a2.val : Int) := by
      have hvalid := mem_lineNormalizedSecondMomentClass_isValid
        (mem_orientedLineNormalizedSecondMomentClass.mp hdata).1
      have hcross := hvalid.cross_relation
      dsimp only [lineSmallHeightCrossFactorTarget,
        lineSmallHeightKeyOfData, lineNormalizedCrossData] at hcross ⊢
      linear_combination -hcross
    change ((lineSmallHeightCrossFactorTarget
      (lineSmallHeightKeyOfData data)).natAbs : Real) ≤
        6 * (((10 ^ length : Nat) : Real) ^ 3)
    rw [htarget]
    exact lineSmallHeight_crossCoefficient_mul_fin_natAbs_le_envelope
      (by positivity) (by exact_mod_cast hband.2.2)
      (zero_le_one.trans hV) hVX.le hboxes.1
  · exact hQ
  · exact hfactor

/-- Factoring `b1=u'*v2` contributes the second signed divisor factor. -/
theorem lineSmallHeightFirstPrimitiveFactorClass_card_real_le
    {length : Nat} (C D : Finset (Fin (10 ^ length))) (V Q : Real)
    (j : Fin (length + 1)) (hV : 1 ≤ V)
    (hVX : V < ((10 ^ length : Nat) : Real)) (hQ : 0 ≤ Q)
    (hfactor : forall z : Int,
      (z.natAbs : Real) ≤ 6 * (((10 ^ length : Nat) : Real) ^ 3) ->
      (z.divisorsAntidiag.card : Real) ≤ Q) :
    ((lineSmallHeightFirstPrimitiveFactorClass length C D V j).card : Real) ≤
      ((lineSmallHeightCrossFactorClass length C D V j).card : Real) * Q := by
  classical
  let S := lineSmallHeightFirstPrimitiveFactorClass length C D V j
  let outer := lineSmallHeightCrossFactorClass length C D V j
  let key : LineSmallHeightFirstPrimitiveFactor (10 ^ length) ->
      LineSmallHeightCrossFactor (10 ^ length) :=
    fun item => item.toLineSmallHeightCrossFactor
  let target : LineSmallHeightCrossFactor (10 ^ length) -> Int :=
    fun item => item.b1
  let embedding : LineSmallHeightFirstPrimitiveFactor (10 ^ length) ->
      Prod Int Int := fun item => (item.uPrime, item.v2)
  apply lineZeroCoefficient_card_nonzero_target_real_le
    S outer key target embedding
    (6 * (((10 ^ length : Nat) : Real) ^ 3)) Q
  · intro item hitem
    obtain ⟨data, hdata, rfl⟩ := Finset.mem_image.mp hitem
    exact Finset.mem_image.mpr ⟨data, hdata, rfl⟩
  · intro item hitem
    obtain ⟨data, hdata, rfl⟩ := Finset.mem_image.mp hitem
    exact (mem_lineNormalizedSecondMomentClass_isValid
      (mem_orientedLineNormalizedSecondMomentClass.mp hdata).1).cross_b1_ne
  · intro item hitem
    obtain ⟨data, hdata, rfl⟩ := Finset.mem_image.mp hitem
    rfl
  · intro fixed item hp item' hp' heq
    have hkey := (Finset.mem_filter.mp hp).2.trans
      (Finset.mem_filter.mp hp').2.symm
    have huPrime := congrArg Prod.fst heq
    have hv2 := congrArg Prod.snd heq
    apply LineSmallHeightFirstPrimitiveFactor.ext
    · exact congrArg (fun x => x.a2Prime) hkey
    · exact congrArg (fun x => x.b2) hkey
    · exact congrArg (fun x => x.b3) hkey
    · exact congrArg (fun x => x.b4) hkey
    · exact congrArg (fun x => x.b1) hkey
    · exact congrArg (fun x => x.a2) hkey
    · exact huPrime
    · exact hv2
  · intro item hitem
    obtain ⟨data, hdata, rfl⟩ := Finset.mem_image.mp hitem
    have hboxes :=
      mem_orientedLineNormalizedSecondMomentClass_cross_mem_boxes hdata hV
    have hband := mem_lineNormalizedSecondMomentClass_band
      (mem_orientedLineNormalizedSecondMomentClass.mp hdata).1
    exact lineSmallHeight_crossCoefficient_natAbs_le_envelope
      (by positivity) (by exact_mod_cast hband.2.2)
      (zero_le_one.trans hV) hVX.le hboxes.1
  · exact hQ
  · exact hfactor

/-- Factoring `-b2=u*v2'` contributes the third signed divisor factor. -/
theorem lineSmallHeightSecondPrimitiveFactorClass_card_real_le
    {length : Nat} (C D : Finset (Fin (10 ^ length))) (V Q : Real)
    (j : Fin (length + 1)) (hV : 1 ≤ V)
    (hVX : V < ((10 ^ length : Nat) : Real)) (hQ : 0 ≤ Q)
    (hfactor : forall z : Int,
      (z.natAbs : Real) ≤ 6 * (((10 ^ length : Nat) : Real) ^ 3) ->
      (z.divisorsAntidiag.card : Real) ≤ Q) :
    ((lineSmallHeightSecondPrimitiveFactorClass length C D V j).card : Real) ≤
      ((lineSmallHeightFirstPrimitiveFactorClass length C D V j).card : Real) *
        Q := by
  classical
  let S := lineSmallHeightSecondPrimitiveFactorClass length C D V j
  let outer := lineSmallHeightFirstPrimitiveFactorClass length C D V j
  let key : LineSmallHeightSecondPrimitiveFactor (10 ^ length) ->
      LineSmallHeightFirstPrimitiveFactor (10 ^ length) :=
    fun item => item.toLineSmallHeightFirstPrimitiveFactor
  let target : LineSmallHeightFirstPrimitiveFactor (10 ^ length) -> Int :=
    fun item => -item.b2
  let embedding : LineSmallHeightSecondPrimitiveFactor (10 ^ length) ->
      Prod Int Int := fun item => (item.u, item.v2Prime)
  apply lineZeroCoefficient_card_nonzero_target_real_le
    S outer key target embedding
    (6 * (((10 ^ length : Nat) : Real) ^ 3)) Q
  · intro item hitem
    obtain ⟨data, hdata, rfl⟩ := Finset.mem_image.mp hitem
    exact Finset.mem_image.mpr ⟨data, hdata, rfl⟩
  · intro item hitem
    obtain ⟨data, hdata, rfl⟩ := Finset.mem_image.mp hitem
    exact neg_ne_zero.mpr
      (mem_lineNormalizedSecondMomentClass_isValid
        (mem_orientedLineNormalizedSecondMomentClass.mp hdata).1).cross_b2_ne
  · intro item hitem
    obtain ⟨data, hdata, rfl⟩ := Finset.mem_image.mp hitem
    dsimp only [embedding, target, key]
    simp [lineSmallHeightSecondPrimitiveFactorOfData,
      lineSmallHeightFirstPrimitiveFactorOfData,
      lineSmallHeightCrossFactorOfData, lineSmallHeightKeyOfData,
      lineNormalizedCrossData]
  · intro fixed item hp item' hp' heq
    have hkey := (Finset.mem_filter.mp hp).2.trans
      (Finset.mem_filter.mp hp').2.symm
    have hu := congrArg Prod.fst heq
    have hv2Prime := congrArg Prod.snd heq
    apply LineSmallHeightSecondPrimitiveFactor.ext
    · exact congrArg (fun x => x.a2Prime) hkey
    · exact congrArg (fun x => x.b2) hkey
    · exact congrArg (fun x => x.b3) hkey
    · exact congrArg (fun x => x.b4) hkey
    · exact congrArg (fun x => x.b1) hkey
    · exact congrArg (fun x => x.a2) hkey
    · exact congrArg (fun x => x.uPrime) hkey
    · exact congrArg (fun x => x.v2) hkey
    · exact hu
    · exact hv2Prime
  · intro item hitem
    obtain ⟨data, hdata, rfl⟩ := Finset.mem_image.mp hitem
    have hboxes :=
      mem_orientedLineNormalizedSecondMomentClass_cross_mem_boxes hdata hV
    have hband := mem_lineNormalizedSecondMomentClass_band
      (mem_orientedLineNormalizedSecondMomentClass.mp hdata).1
    rw [Int.natAbs_neg]
    exact lineSmallHeight_crossCoefficient_natAbs_le_envelope
      (by positivity) (by exact_mod_cast hband.2.2)
      (zero_le_one.trans hV) hVX.le hboxes.2.1
  · exact hQ
  · exact hfactor

end PrimesRestrictedDigits
