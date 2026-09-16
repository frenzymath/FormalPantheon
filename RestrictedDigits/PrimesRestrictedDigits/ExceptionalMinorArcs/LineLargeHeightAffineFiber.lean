import PrimesRestrictedDigits.ExceptionalMinorArcs.LineLargeHeightPrefixes
import PrimesRestrictedDigits.ExceptionalMinorArcs.LineCongruenceScaleBridge
import PrimesRestrictedDigits.ExceptionalMinorArcs.LineCongruenceHeightClasses
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombination

/-!
# Affine cross fiber in the large primitive-height count

This counts the actual bounded `(b3,b4)` image in the large-height argument before equation
`(15.5)` of `MAYNARD-PRD-PUBLISHED`, Lemma 15.2, pp. 212--213. The congruence residue and
recovery equality have the corrected negative sign.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

private theorem card_real_le_card_mul_of_large_height_fiber_bound
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (S : Finset A) (outer : Finset B) (key : A -> B) (R : Real)
    (hmaps : Set.MapsTo key (S : Set A) (outer : Set B))
    (hfiber : forall fixed, fixed ∈ outer ->
      ((S.filter fun item => key item = fixed).card : Real) ≤ R) :
    (S.card : Real) ≤ (outer.card : Real) * R := by
  have hdecomp := Finset.card_eq_sum_card_fiberwise hmaps
  calc
    (S.card : Real) =
        ∑ fixed ∈ outer,
          ((S.filter fun item => key item = fixed).card : Real) := by
      simpa only [Nat.cast_sum] using
        congrArg (fun n : Nat => (n : Real)) hdecomp
    _ ≤ ∑ _fixed ∈ outer, R :=
      Finset.sum_le_sum fun fixed hfixed => hfiber fixed hfixed
    _ = (outer.card : Real) * R := by simp

/-- A cross-prefix image member satisfies the exact corrected cross relation. -/
theorem mem_lineSmallHeightCrossFactorClass_cross_relation
    {length : Nat} {C D : Finset (Fin (10 ^ length))} {V : Real}
    {j : Fin (length + 1)}
    {item : LineSmallHeightCrossFactor (10 ^ length)}
    (hitem : item ∈ lineSmallHeightCrossFactorClass length C D V j) :
    item.b1 * (item.a2.val : Int) +
      item.b2 * (item.a2Prime.val : Int) +
      item.b3 * ((10 ^ length : Nat) : Int) + item.b4 = 0 := by
  obtain ⟨data, hdata, rfl⟩ := Finset.mem_image.mp hitem
  have hvalid := mem_lineNormalizedSecondMomentClass_isValid
    (mem_orientedLineNormalizedSecondMomentClass.mp hdata).1
  simpa only [lineSmallHeightCrossFactorOfData, lineSmallHeightKeyOfData]
    using hvalid.cross_relation

/-- The actual cross pair has the corrected negative affine residue. -/
theorem mem_lineSmallHeightCrossFactorClass_modEq
    {length : Nat} {C D : Finset (Fin (10 ^ length))} {V : Real}
    {j : Fin (length + 1)}
    {item : LineSmallHeightCrossFactor (10 ^ length)}
    (hitem : item ∈ lineSmallHeightCrossFactorClass length C D V j) :
    Int.ModEq (item.a2Prime.val : Int)
      (((10 ^ length : Nat) : Int) * item.b3 + item.b4)
      (-(item.b1 * (item.a2.val : Int))) := by
  have hrelation := mem_lineSmallHeightCrossFactorClass_cross_relation hitem
  rw [Int.modEq_iff_dvd]
  have heq :
      -(item.b1 * (item.a2.val : Int)) -
          (((10 ^ length : Nat) : Int) * item.b3 + item.b4) =
        (item.a2Prime.val : Int) * item.b2 := by
    linear_combination -hrelation
  rw [heq]
  exact dvd_mul_right _ _

/-- Members of a fixed modulus/minimum class satisfy the scaled source box. -/
theorem mem_lineSmallHeightCrossFactorClass_scaled_norm_le
    {length : Nat} {C : Finset (Fin (10 ^ length))} {V : Real}
    {k : Prod (Fin (length + 1)) (Fin (length + 1))}
    {j : Fin (length + 1)}
    {item : LineSmallHeightCrossFactor (10 ^ length)}
    (hitem : item ∈ lineSmallHeightCrossFactorClass length C
      (lineCongruenceHeightClass length C k) V j)
    (hV : 1 ≤ V) :
    norm (scaledPhysicalPair
      (((10 ^ length : Nat) : Real) /
        ((10 ^ k.1.val : Nat) : Real)) (item.b3, item.b4)) ≤
      6 * ((10 ^ j.val : Nat) : Real) * V := by
  obtain ⟨data, hdata, rfl⟩ := Finset.mem_image.mp hitem
  let X : Real := ((10 ^ length : Nat) : Real)
  let A : Real := ((10 ^ k.1.val : Nat) : Real)
  let U : Real := ((10 ^ j.val : Nat) : Real)
  have hfull := (mem_orientedLineNormalizedSecondMomentClass.mp hdata).1
  have hvalid := mem_lineNormalizedSecondMomentClass_isValid hfull
  have hboxes :=
    mem_orientedLineNormalizedSecondMomentClass_cross_mem_boxes hdata hV
  have ha2Band := mem_lineCongruenceHeightClass_modulus_band hvalid.a2_mem
  have ha2PrimeBand :=
    mem_lineCongruenceHeightClass_modulus_band hvalid.a2Prime_mem
  have hcross := hvalid.cross_relation
  have hX : 0 < X := by dsimp only [X]; positivity
  have hAOne : 1 ≤ A := by
    dsimp only [A]
    rw [Nat.cast_pow]
    exact one_le_pow₀ (by norm_num)
  have hAPos : 0 < A := zero_lt_one.trans_le hAOne
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hVNonneg : 0 ≤ V := zero_le_one.trans hV
  have hUV : 0 ≤ 2 * U * V := by positivity
  have hb1 : abs ((lineNormalizedCrossData data).b1 : Real) ≤
      2 * U * V := by
    simpa only [U] using
      (mem_lineCoefficientBox_iff (by positivity)).mp hboxes.1
  have hb2 : abs ((lineNormalizedCrossData data).b2 : Real) ≤
      2 * U * V := by
    simpa only [U] using
      (mem_lineCoefficientBox_iff (by positivity)).mp hboxes.2.1
  have hb4 : abs ((lineNormalizedCrossData data).b4 : Real) ≤
      2 * U * V := by
    simpa only [U] using
      (mem_lineCoefficientBox_iff (by positivity)).mp hboxes.2.2.2
  have ha2 : (data.a2.val : Real) ≤ A := by
    simpa only [A] using ha2Band.2.1
  have ha2Prime : (data.a2Prime.val : Real) ≤ A := by
    simpa only [A] using ha2PrimeBand.2.1
  have hcrossReal :
      ((lineNormalizedCrossData data).b1 : Real) * data.a2.val +
        ((lineNormalizedCrossData data).b2 : Real) * data.a2Prime.val +
        ((lineNormalizedCrossData data).b3 : Real) * X +
        ((lineNormalizedCrossData data).b4 : Real) = 0 := by
    dsimp only [X]
    exact_mod_cast hcross
  have hb3Product :
      abs ((lineNormalizedCrossData data).b3 : Real) * X ≤
        6 * U * V * A := by
    calc
      abs ((lineNormalizedCrossData data).b3 : Real) * X =
          abs (((lineNormalizedCrossData data).b3 : Real) * X) := by
        rw [abs_mul, abs_of_pos hX]
      _ = abs (-(((lineNormalizedCrossData data).b1 : Real) * data.a2.val +
          ((lineNormalizedCrossData data).b2 : Real) * data.a2Prime.val +
          (lineNormalizedCrossData data).b4)) := by
        congr 1
        linarith
      _ = abs (((lineNormalizedCrossData data).b1 : Real) * data.a2.val +
          ((lineNormalizedCrossData data).b2 : Real) * data.a2Prime.val +
          (lineNormalizedCrossData data).b4) := abs_neg _
      _ ≤ abs (((lineNormalizedCrossData data).b1 : Real) * data.a2.val) +
          abs (((lineNormalizedCrossData data).b2 : Real) * data.a2Prime.val) +
          abs ((lineNormalizedCrossData data).b4 : Real) := by
        exact (abs_add_le _ _).trans
          (add_le_add (abs_add_le _ _) le_rfl)
      _ = abs ((lineNormalizedCrossData data).b1 : Real) * data.a2.val +
          abs ((lineNormalizedCrossData data).b2 : Real) * data.a2Prime.val +
          abs ((lineNormalizedCrossData data).b4 : Real) := by
        rw [abs_mul, abs_mul]
        simp only [Nat.abs_cast]
      _ ≤ (2 * U * V) * A + (2 * U * V) * A + 2 * U * V := by
        exact add_le_add
          (add_le_add
            (mul_le_mul hb1 ha2 (by positivity) hUV)
            (mul_le_mul hb2 ha2Prime (by positivity) hUV))
          hb4
      _ ≤ (2 * U * V) * A + (2 * U * V) * A +
          (2 * U * V) * A := by
        apply add_le_add le_rfl
        calc
          2 * U * V = (2 * U * V) * 1 := by ring
          _ ≤ (2 * U * V) * A :=
            mul_le_mul_of_nonneg_left hAOne hUV
      _ = 6 * U * V * A := by ring
  have hb3Scaled :
      (X / A) * abs ((lineNormalizedCrossData data).b3 : Real) ≤
        6 * U * V := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hAPos]
    simpa only [mul_comm X] using hb3Product
  rw [Prod.norm_def]
  simp only [scaledPhysicalPair, Real.norm_eq_abs]
  apply max_le
  · rw [abs_mul, abs_of_nonneg (div_nonneg hX.le hAPos.le)]
    exact hb3Scaled
  · exact hb4.trans (by nlinarith [hUV])

/-- The corrected affine `(b3,b4)` fiber contributes the source factor 640. -/
theorem lineLargeHeightCrossFactorClass_card_real_le
    {length : Nat} (C : Finset (Fin (10 ^ length))) (V : Real)
    (k : Prod (Fin (length + 1)) (Fin (length + 1)))
    (j : Fin (length + 1)) (hV : 1 ≤ V) :
    let D := lineCongruenceHeightClass length C k
    let X : Real := ((10 ^ length : Nat) : Real)
    let M : Real := ((10 ^ k.2.val : Nat) : Real)
    let U : Real := ((10 ^ j.val : Nat) : Real)
    ((lineSmallHeightCrossFactorClass length C D V j).card : Real) ≤
      ((lineLargeHeightKeyClass length C D V j).card : Real) *
        (640 * (1 + 6 * U * V / M + (6 * U * V) ^ 2 / X)) := by
  classical
  let D := lineCongruenceHeightClass length C k
  let X : Real := ((10 ^ length : Nat) : Real)
  let A : Real := ((10 ^ k.1.val : Nat) : Real)
  let M : Real := ((10 ^ k.2.val : Nat) : Real)
  let U : Real := ((10 ^ j.val : Nat) : Real)
  let B : Real := 6 * U * V
  let S := lineSmallHeightCrossFactorClass length C D V j
  let outer := lineLargeHeightKeyClass length C D V j
  let key : LineSmallHeightCrossFactor (10 ^ length) ->
      LineLargeHeightKey (10 ^ length) := fun item => item.toLineLargeHeightKey
  let embedding : LineSmallHeightCrossFactor (10 ^ length) -> Prod Int Int :=
    fun item => (item.b3, item.b4)
  apply card_real_le_card_mul_of_large_height_fiber_bound S outer key
    (640 * (1 + B / M + B ^ 2 / X))
  · intro item hitem
    obtain ⟨data, hdata, rfl⟩ := Finset.mem_image.mp hitem
    exact Finset.mem_image.mpr ⟨data, hdata, rfl⟩
  · intro fixed hfixed
    let fiber := S.filter fun item => key item = fixed
    let pairFiber := fiber.image embedding
    obtain ⟨fixedData, hfixedData, hfixedEq⟩ := Finset.mem_image.mp hfixed
    have hfixedValid := mem_lineNormalizedSecondMomentClass_isValid
      (mem_orientedLineNormalizedSecondMomentClass.mp hfixedData).1
    have hfixedPrimeMem : fixed.a2Prime ∈ D := by
      rw [← hfixedEq]
      exact hfixedValid.a2Prime_mem
    have hmodulusBand :=
      mem_lineCongruenceHeightClass_modulus_band hfixedPrimeMem
    have hminimumBand :=
      mem_lineCongruenceHeightClass_minimum_band hfixedPrimeMem
    have hA : 0 < (10 ^ k.1.val : Nat) := by positivity
    have hAX : 10 ^ k.1.val ≤ 10 ^ length :=
      Nat.pow_le_pow_right (by norm_num) k.1.is_le
    have hM : 0 < M := by dsimp only [M]; positivity
    have hB : 0 ≤ B := by
      dsimp only [B, U]
      positivity
    have hinj : Set.InjOn embedding (fiber : Set _) := by
      intro item hitem item' hitem' heq
      have hitemData := Finset.mem_filter.mp hitem
      have hitem'Data := Finset.mem_filter.mp hitem'
      have hkey := hitemData.2.trans hitem'Data.2.symm
      have hrelation :=
        mem_lineSmallHeightCrossFactorClass_cross_relation hitemData.1
      have hrelation' :=
        mem_lineSmallHeightCrossFactorClass_cross_relation hitem'Data.1
      have ha2PrimePos : 0 < item.a2Prime.val := by
        obtain ⟨data, hdata, hcode⟩ := Finset.mem_image.mp hitemData.1
        subst item
        exact (mem_lineNormalizedSecondMomentClass_isValid
          (mem_orientedLineNormalizedSecondMomentClass.mp hdata).1).a2Prime_pos
      have ha2PrimeNe : (item.a2Prime.val : Int) ≠ 0 := by
        exact_mod_cast ha2PrimePos.ne'
      have ha2PrimeEq : item.a2Prime = item'.a2Prime := by
        simpa only [key, LineSmallHeightCrossFactor.toLineLargeHeightKey]
          using congrArg LineLargeHeightKey.a2Prime hkey
      have ha2Eq : item.a2 = item'.a2 := by
        simpa only [key, LineSmallHeightCrossFactor.toLineLargeHeightKey]
          using congrArg LineLargeHeightKey.a2 hkey
      have hb1 : item.b1 = item'.b1 := by
        simpa only [key, LineSmallHeightCrossFactor.toLineLargeHeightKey]
          using congrArg LineLargeHeightKey.b1 hkey
      have hb3 : item.b3 = item'.b3 := by
        simpa only [embedding] using congrArg Prod.fst heq
      have hb4 : item.b4 = item'.b4 := by
        simpa only [embedding] using congrArg Prod.snd heq
      have hb2 : item.b2 = item'.b2 := by
        apply mul_right_cancel₀ ha2PrimeNe
        rw [← ha2PrimeEq, ← ha2Eq, ← hb1, ← hb3, ← hb4] at hrelation'
        linear_combination hrelation - hrelation'
      apply LineSmallHeightCrossFactor.ext
      · exact ha2PrimeEq
      · exact hb2
      · exact hb3
      · exact hb4
      · exact hb1
      · exact ha2Eq
    have hpairCard : pairFiber.card = fiber.card :=
      Finset.card_image_of_injOn hinj
    have hpairCongruence : forall z, z ∈ pairFiber ->
        Int.ModEq (fixed.a2Prime.val : Int)
          (((10 ^ length : Nat) : Int) * z.1 + z.2)
          (-(fixed.b1 * (fixed.a2.val : Int))) := by
      intro z hz
      obtain ⟨item, hitem, rfl⟩ := Finset.mem_image.mp hz
      have hitemData := Finset.mem_filter.mp hitem
      have hmod := mem_lineSmallHeightCrossFactorClass_modEq hitemData.1
      have hkey := hitemData.2
      rw [← hkey]
      exact hmod
    have hpairBound : forall z, z ∈ pairFiber ->
        norm (scaledPhysicalPair
          (((10 ^ length : Nat) : Real) /
            ((10 ^ k.1.val : Nat) : Real)) z) ≤ B := by
      intro z hz
      obtain ⟨item, hitem, rfl⟩ := Finset.mem_image.mp hz
      have hitemData := (Finset.mem_filter.mp hitem).1
      simpa only [B, U] using
        mem_lineSmallHeightCrossFactorClass_scaled_norm_le hitemData hV
    have haffine := card_affineCongruence_le_sourceMinimumBand
      fixed.a2Prime.val (10 ^ length) (10 ^ k.1.val) M B
      (-(fixed.b1 * (fixed.a2.val : Int))) hA hAX
      (by simpa only [A] using hmodulusBand.1) hM
      (by simpa only [M] using hminimumBand.1) hB pairFiber
      hpairCongruence hpairBound
    calc
      (fiber.card : Real) = (pairFiber.card : Real) := by
        exact_mod_cast hpairCard.symm
      _ ≤ 640 * (1 + B / M + B ^ 2 / X) := by
        simpa only [X] using haffine

end PrimesRestrictedDigits
