import PrimesRestrictedDigits.ExceptionalMinorArcs.LineSmallHeightDivisorFibers

/-!
# Linear and final divisor fibers in the small-height count

This proves the two coprime residue-class transitions and the corrected final raw-coefficient
divisor transition in equation `(15.4)` of `MAYNARD-PRD-PUBLISHED`.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- The corrected final target has a negative sign and no extra factor `X`. -/
def lineSmallHeightFinalTarget {X : Nat}
    (item : LineSmallHeightFourthPair X) : Int :=
  -(item.v2 * (item.a2.val : Int) + item.v3 * (X : Int) + item.v4)

private theorem card_real_le_card_mul_of_fiber_bound
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

private theorem oriented_u_scale_data
    {length : Nat} {C D : Finset (Fin (10 ^ length))} {V : Real}
    {j : Fin (length + 1)}
    {data : LineNormalizedSecondMomentData (10 ^ length)}
    (hdata : data ∈ orientedLineNormalizedSecondMomentClass length C D V j) :
    ((10 ^ j.val : Nat) : Real) / 10 < (data.u.natAbs : Real) ∧
      (data.u.natAbs : Real) ≤ V := by
  have horiented := (mem_orientedLineNormalizedSecondMomentClass.mp hdata).2
  have hfull := (mem_orientedLineNormalizedSecondMomentClass.mp hdata).1
  have hvalid := mem_lineNormalizedSecondMomentClass_isValid hfull
  have hband := mem_lineNormalizedSecondMomentClass_band hfull
  have hheight : data.primitiveHeight = data.u.natAbs :=
    max_eq_left horiented
  refine ⟨?_, ?_⟩
  · simpa only [hheight] using hband.1
  · rw [Nat.cast_natAbs, Int.cast_abs]
    exact hvalid.u_abs_le

/-- The `v3,v3'` transition contributes one factor `40*V/U`. -/
theorem lineSmallHeightThirdPairClass_card_real_le
    {length : Nat} (C D : Finset (Fin (10 ^ length))) (V : Real)
    (j : Fin (length + 1)) (hV : 1 ≤ V) :
    ((lineSmallHeightThirdPairClass length C D V j).card : Real) ≤
      ((lineSmallHeightSecondPrimitiveFactorClass
        length C D V j).card : Real) *
          (40 * V / ((10 ^ j.val : Nat) : Real)) := by
  classical
  let S := lineSmallHeightThirdPairClass length C D V j
  let outer := lineSmallHeightSecondPrimitiveFactorClass length C D V j
  let key : LineSmallHeightThirdPair (10 ^ length) ->
      LineSmallHeightSecondPrimitiveFactor (10 ^ length) :=
    fun item => item.toLineSmallHeightSecondPrimitiveFactor
  let embedding : LineSmallHeightThirdPair (10 ^ length) -> Prod Int Int :=
    fun item => (item.v3, item.v3Prime)
  apply card_real_le_card_mul_of_fiber_bound S outer key
    (40 * V / ((10 ^ j.val : Nat) : Real))
  · intro item hitem
    obtain ⟨data, hdata, rfl⟩ := Finset.mem_image.mp hitem
    exact Finset.mem_image.mpr ⟨data, hdata, rfl⟩
  · intro fixed hfixed
    let fiber := S.filter fun item => key item = fixed
    have hcard : fiber.card ≤
        (lineCoprimeLinearPairFiber
          V fixed.u fixed.uPrime fixed.b3).card := by
      apply Finset.card_le_card_of_injOn embedding
      · intro item hitem
        have hitemData := Finset.mem_filter.mp hitem
        obtain ⟨data, hdata, hcode⟩ := Finset.mem_image.mp hitemData.1
        subst item
        have hvalid := mem_lineNormalizedSecondMomentClass_isValid
          (mem_orientedLineNormalizedSecondMomentClass.mp hdata).1
        have hparent := hitemData.2
        rw [← hparent]
        apply mem_lineCoprimeLinearPairFiber.mpr
        exact ⟨(mem_lineCoefficientBox_iff (zero_le_one.trans hV)).2
            hvalid.v3_abs_le,
          (mem_lineCoefficientBox_iff (zero_le_one.trans hV)).2
            hvalid.v3Prime_abs_le,
          rfl⟩
      · intro item hitem item' hitem' heq
        have hparent := (Finset.mem_filter.mp hitem).2.trans
          (Finset.mem_filter.mp hitem').2.symm
        have hv3 := congrArg Prod.fst heq
        have hv3Prime := congrArg Prod.snd heq
        apply LineSmallHeightThirdPair.ext
        · exact congrArg (fun x => x.a2Prime) hparent
        · exact congrArg (fun x => x.b2) hparent
        · exact congrArg (fun x => x.b3) hparent
        · exact congrArg (fun x => x.b4) hparent
        · exact congrArg (fun x => x.b1) hparent
        · exact congrArg (fun x => x.a2) hparent
        · exact congrArg (fun x => x.uPrime) hparent
        · exact congrArg (fun x => x.v2) hparent
        · exact congrArg (fun x => x.u) hparent
        · exact congrArg (fun x => x.v2Prime) hparent
        · exact hv3
        · exact hv3Prime
    by_cases hfiber : fiber.Nonempty
    · let item := hfiber.choose
      have hitem := Finset.mem_filter.mp hfiber.choose_spec
      obtain ⟨data, hdata, hcode⟩ := Finset.mem_image.mp hitem.1
      have hparent :
          lineSmallHeightSecondPrimitiveFactorOfData data = fixed := by
        calc
          lineSmallHeightSecondPrimitiveFactorOfData data =
              key (lineSmallHeightThirdPairOfData data) := rfl
          _ = key item := congrArg key hcode
          _ = fixed := hitem.2
      have hvalid := mem_lineNormalizedSecondMomentClass_isValid
        (mem_orientedLineNormalizedSecondMomentClass.mp hdata).1
      have hscale := oriented_u_scale_data hdata
      have hu : fixed.u ≠ 0 := by
        rw [← congrArg (fun x => x.u) hparent]
        exact hvalid.u_ne
      have hgcd : Int.gcd fixed.u fixed.uPrime = 1 := by
        rw [← congrArg (fun x => x.u) hparent,
          ← congrArg (fun x => x.uPrime) hparent]
        exact hvalid.primitive_gcd
      have hlower : ((10 ^ j.val : Nat) : Real) / 10 <
          (fixed.u.natAbs : Real) := by
        rw [← congrArg (fun x => x.u) hparent]
        exact hscale.1
      have hupper : (fixed.u.natAbs : Real) ≤ V := by
        rw [← congrArg (fun x => x.u) hparent]
        exact hscale.2
      calc
        (fiber.card : Real) ≤
            ((lineCoprimeLinearPairFiber
              V fixed.u fixed.uPrime fixed.b3).card : Real) := by
          exact_mod_cast hcard
        _ ≤ 40 * V / ((10 ^ j.val : Nat) : Real) :=
          card_lineCoprimeLinearPairFiber_real_le_scale
            V ((10 ^ j.val : Nat) : Real) fixed.u fixed.uPrime fixed.b3
            hV (by positivity) hu hgcd hlower hupper
    · have hempty : fiber = ∅ := Finset.not_nonempty_iff_eq_empty.mp hfiber
      change (fiber.card : Real) ≤
        40 * V / ((10 ^ j.val : Nat) : Real)
      simp only [hempty, Finset.card_empty, Nat.cast_zero]
      exact div_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans hV))
        (by positivity)

/-- The `v4,v4'` transition contributes the second factor `40*V/U`. -/
theorem lineSmallHeightFourthPairClass_card_real_le
    {length : Nat} (C D : Finset (Fin (10 ^ length))) (V : Real)
    (j : Fin (length + 1)) (hV : 1 ≤ V) :
    ((lineSmallHeightFourthPairClass length C D V j).card : Real) ≤
      ((lineSmallHeightThirdPairClass length C D V j).card : Real) *
        (40 * V / ((10 ^ j.val : Nat) : Real)) := by
  classical
  let S := lineSmallHeightFourthPairClass length C D V j
  let outer := lineSmallHeightThirdPairClass length C D V j
  let key : LineSmallHeightFourthPair (10 ^ length) ->
      LineSmallHeightThirdPair (10 ^ length) :=
    fun item => item.toLineSmallHeightThirdPair
  let embedding : LineSmallHeightFourthPair (10 ^ length) -> Prod Int Int :=
    fun item => (item.v4, item.v4Prime)
  apply card_real_le_card_mul_of_fiber_bound S outer key
    (40 * V / ((10 ^ j.val : Nat) : Real))
  · intro item hitem
    obtain ⟨data, hdata, rfl⟩ := Finset.mem_image.mp hitem
    exact Finset.mem_image.mpr ⟨data, hdata, rfl⟩
  · intro fixed hfixed
    let fiber := S.filter fun item => key item = fixed
    have hcard : fiber.card ≤
        (lineCoprimeLinearPairFiber
          V fixed.u fixed.uPrime fixed.b4).card := by
      apply Finset.card_le_card_of_injOn embedding
      · intro item hitem
        have hitemData := Finset.mem_filter.mp hitem
        obtain ⟨data, hdata, hcode⟩ := Finset.mem_image.mp hitemData.1
        subst item
        have hvalid := mem_lineNormalizedSecondMomentClass_isValid
          (mem_orientedLineNormalizedSecondMomentClass.mp hdata).1
        have hparent := hitemData.2
        rw [← hparent]
        apply mem_lineCoprimeLinearPairFiber.mpr
        exact ⟨(mem_lineCoefficientBox_iff (zero_le_one.trans hV)).2
            hvalid.v4_abs_le,
          (mem_lineCoefficientBox_iff (zero_le_one.trans hV)).2
            hvalid.v4Prime_abs_le,
          rfl⟩
      · intro item hitem item' hitem' heq
        have hparent := (Finset.mem_filter.mp hitem).2.trans
          (Finset.mem_filter.mp hitem').2.symm
        have hv4 := congrArg Prod.fst heq
        have hv4Prime := congrArg Prod.snd heq
        apply LineSmallHeightFourthPair.ext
        · exact congrArg (fun x => x.a2Prime) hparent
        · exact congrArg (fun x => x.b2) hparent
        · exact congrArg (fun x => x.b3) hparent
        · exact congrArg (fun x => x.b4) hparent
        · exact congrArg (fun x => x.b1) hparent
        · exact congrArg (fun x => x.a2) hparent
        · exact congrArg (fun x => x.uPrime) hparent
        · exact congrArg (fun x => x.v2) hparent
        · exact congrArg (fun x => x.u) hparent
        · exact congrArg (fun x => x.v2Prime) hparent
        · exact congrArg (fun x => x.v3) hparent
        · exact congrArg (fun x => x.v3Prime) hparent
        · exact hv4
        · exact hv4Prime
    by_cases hfiber : fiber.Nonempty
    · let item := hfiber.choose
      have hitem := Finset.mem_filter.mp hfiber.choose_spec
      obtain ⟨data, hdata, hcode⟩ := Finset.mem_image.mp hitem.1
      have hparent : lineSmallHeightThirdPairOfData data = fixed := by
        calc
          lineSmallHeightThirdPairOfData data =
              key (lineSmallHeightFourthPairOfData data) := rfl
          _ = key item := congrArg key hcode
          _ = fixed := hitem.2
      have hvalid := mem_lineNormalizedSecondMomentClass_isValid
        (mem_orientedLineNormalizedSecondMomentClass.mp hdata).1
      have hscale := oriented_u_scale_data hdata
      have hu : fixed.u ≠ 0 := by
        rw [← congrArg (fun x => x.u) hparent]
        exact hvalid.u_ne
      have hgcd : Int.gcd fixed.u fixed.uPrime = 1 := by
        rw [← congrArg (fun x => x.u) hparent,
          ← congrArg (fun x => x.uPrime) hparent]
        exact hvalid.primitive_gcd
      have hlower : ((10 ^ j.val : Nat) : Real) / 10 <
          (fixed.u.natAbs : Real) := by
        rw [← congrArg (fun x => x.u) hparent]
        exact hscale.1
      have hupper : (fixed.u.natAbs : Real) ≤ V := by
        rw [← congrArg (fun x => x.u) hparent]
        exact hscale.2
      calc
        (fiber.card : Real) ≤
            ((lineCoprimeLinearPairFiber
              V fixed.u fixed.uPrime fixed.b4).card : Real) := by
          exact_mod_cast hcard
        _ ≤ 40 * V / ((10 ^ j.val : Nat) : Real) :=
          card_lineCoprimeLinearPairFiber_real_le_scale
            V ((10 ^ j.val : Nat) : Real) fixed.u fixed.uPrime fixed.b4
            hV (by positivity) hu hgcd hlower hupper
    · have hempty : fiber = ∅ := Finset.not_nonempty_iff_eq_empty.mp hfiber
      change (fiber.card : Real) ≤
        40 * V / ((10 ^ j.val : Nat) : Real)
      simp only [hempty, Finset.card_empty, Nat.cast_zero]
      exact div_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans hV))
        (by positivity)

/-- The corrected final relation contributes the fourth divisor factor. -/
theorem lineSmallHeightCodeClass_card_real_le
    {length : Nat} (C D : Finset (Fin (10 ^ length))) (V Q : Real)
    (j : Fin (length + 1)) (hV : 1 ≤ V)
    (hVX : V < ((10 ^ length : Nat) : Real)) (hQ : 0 ≤ Q)
    (hfactor : forall z : Int,
      (z.natAbs : Real) ≤ 6 * (((10 ^ length : Nat) : Real) ^ 3) ->
      (z.divisorsAntidiag.card : Real) ≤ Q) :
    ((lineSmallHeightCodeClass length C D V j).card : Real) ≤
      ((lineSmallHeightFourthPairClass length C D V j).card : Real) * Q := by
  classical
  let S := lineSmallHeightCodeClass length C D V j
  let outer := lineSmallHeightFourthPairClass length C D V j
  let key : LineSmallHeightCode (10 ^ length) ->
      LineSmallHeightFourthPair (10 ^ length) :=
    fun item => item.toLineSmallHeightFourthPair
  let target := lineSmallHeightFinalTarget (X := 10 ^ length)
  let embedding : LineSmallHeightCode (10 ^ length) -> Prod Int Int :=
    fun item => ((item.d : Int) * item.u, (item.a1.val : Int))
  apply lineZeroCoefficient_card_nonzero_target_real_le
    S outer key target embedding
    (6 * (((10 ^ length : Nat) : Real) ^ 3)) Q
  · intro item hitem
    obtain ⟨data, hdata, rfl⟩ := Finset.mem_image.mp hitem
    exact Finset.mem_image.mpr ⟨data, hdata, rfl⟩
  · intro item hitem
    obtain ⟨data, hdata, rfl⟩ := Finset.mem_image.mp hitem
    have hvalid := mem_lineNormalizedSecondMomentClass_isValid
      (mem_orientedLineNormalizedSecondMomentClass.mp hdata).1
    change lineSmallHeightFinalTarget (lineSmallHeightFourthPairOfData data) ≠ 0
    rw [show lineSmallHeightFinalTarget (lineSmallHeightFourthPairOfData data) =
      (data.d : Int) * data.u * (data.a1.val : Int) by
        exact hvalid.first_divisor_target.symm]
    exact mul_ne_zero (mul_ne_zero (by exact_mod_cast hvalid.d_pos.ne')
      hvalid.u_ne) (by exact_mod_cast hvalid.a1_pos.ne')
  · intro item hitem
    obtain ⟨data, hdata, rfl⟩ := Finset.mem_image.mp hitem
    have hvalid := mem_lineNormalizedSecondMomentClass_isValid
      (mem_orientedLineNormalizedSecondMomentClass.mp hdata).1
    dsimp only [embedding, target, key, lineSmallHeightCodeOfData]
    exact hvalid.first_divisor_target
  · intro fixed item hitem item' hitem' heq
    have hparent := (Finset.mem_filter.mp hitem).2.trans
      (Finset.mem_filter.mp hitem').2.symm
    have hraw := congrArg Prod.fst heq
    have ha1Val : (item.a1.val : Int) = (item'.a1.val : Int) := by
      simpa only [embedding] using congrArg Prod.snd heq
    have hu : item.u ≠ 0 := by
      obtain ⟨data, hdata, hcode⟩ :=
        Finset.mem_image.mp (Finset.mem_filter.mp hitem).1
      subst item
      exact (mem_lineNormalizedSecondMomentClass_isValid
        (mem_orientedLineNormalizedSecondMomentClass.mp hdata).1).u_ne
    have huEq : item.u = item'.u := congrArg (fun x => x.u) hparent
    have hdInt : (item.d : Int) = (item'.d : Int) := by
      apply mul_right_cancel₀ hu
      simpa only [embedding, huEq] using hraw
    have hd : item.d = item'.d := by exact_mod_cast hdInt
    have ha1 : item.a1 = item'.a1 := by
      apply Fin.ext
      exact_mod_cast ha1Val
    apply LineSmallHeightCode.ext
    · exact congrArg (fun x => x.a2Prime) hparent
    · exact congrArg (fun x => x.b2) hparent
    · exact congrArg (fun x => x.b3) hparent
    · exact congrArg (fun x => x.b4) hparent
    · exact congrArg (fun x => x.b1) hparent
    · exact congrArg (fun x => x.a2) hparent
    · exact congrArg (fun x => x.uPrime) hparent
    · exact congrArg (fun x => x.v2) hparent
    · exact huEq
    · exact congrArg (fun x => x.v2Prime) hparent
    · exact congrArg (fun x => x.v3) hparent
    · exact congrArg (fun x => x.v3Prime) hparent
    · exact congrArg (fun x => x.v4) hparent
    · exact congrArg (fun x => x.v4Prime) hparent
    · exact hd
    · exact ha1
  · intro item hitem
    obtain ⟨data, hdata, rfl⟩ := Finset.mem_image.mp hitem
    have hvalid := mem_lineNormalizedSecondMomentClass_isValid
      (mem_orientedLineNormalizedSecondMomentClass.mp hdata).1
    change ((lineSmallHeightFinalTarget
      (lineSmallHeightFourthPairOfData data)).natAbs : Real) ≤
        6 * (((10 ^ length : Nat) : Real) ^ 3)
    rw [show lineSmallHeightFinalTarget (lineSmallHeightFourthPairOfData data) =
      (data.d : Int) * data.u * (data.a1.val : Int) by
        exact hvalid.first_divisor_target.symm]
    let X : Real := ((10 ^ length : Nat) : Real)
    have ha1 : (data.a1.val : Real) ≤ X := by
      dsimp only [X]
      exact_mod_cast data.a1.isLt.le
    have hX : 1 ≤ X := by
      dsimp only [X]
      rw [Nat.cast_pow]
      exact one_le_pow₀ (by norm_num)
    calc
      ((((data.d : Int) * data.u * (data.a1.val : Int)).natAbs : Nat) : Real) =
          abs (((data.d : Int) * data.u : Int) : Real) *
            (data.a1.val : Real) := by
        rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_mul, abs_mul]
        simp
      _ ≤ V * X := by
        exact mul_le_mul hvalid.first_abs_le ha1
          (Nat.cast_nonneg data.a1.val) (zero_le_one.trans hV)
      _ ≤ X ^ 2 := by
        have hVNonneg : 0 ≤ V := zero_le_one.trans hV
        nlinarith [mul_nonneg hVNonneg (zero_le_one.trans hX)]
      _ ≤ 6 * X ^ 3 := by
        have hlinear : 0 ≤ 6 * X - 1 := by linarith
        have haux : 0 ≤ X ^ 2 * (6 * X - 1) :=
          mul_nonneg (sq_nonneg X) hlinear
        nlinarith
  · exact hQ
  · exact hfactor

end PrimesRestrictedDigits
