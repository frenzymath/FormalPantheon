import PrimesRestrictedDigits.SieveAsymptotics.TypeIICellPrimeMass
import PrimesRestrictedDigits.SieveAsymptotics.TypeIIWeightedOneCell
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Boolean support mass of one Type II cell

This converts the logarithmic mass estimate for one remainder cell into the positive Boolean
support estimate used in Proposition 7.2 of `MAYNARD-PRD-PUBLISHED`.
-/

open Filter
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The Boolean product-support count of one full Type II cell. -/
noncomputable def typeIICellSupportCount
    (X : Nat) {k : Nat} (a : Fin k -> Real)
    (delta eta : Real) (C : Finset Nat) : Real :=
  (((primeTupleProductSupport
      (majorArcPrimeTuples X a delta eta)).filter
        (fun n => n ∈ C)).card : Real)

/-- A uniform lower bound on tuple weights gives a Boolean support bound
without any injectivity assumption on the product map. -/
theorem mul_card_primeTupleProductSupport_filter_le_sum_weight
    {ell : Nat} (tuples : Finset (Fin ell -> Nat))
    (C : Finset Nat) (lower : Real) (hlower : 0 <= lower)
    (hweight : ∀ p, p ∈ tuples -> lower <= primeTupleLogWeight p) :
    lower *
        (((primeTupleProductSupport tuples).filter
          (fun n => n ∈ C)).card : Real) <=
      C.sum (primeTupleWeightAtProduct tuples) := by
  classical
  let selected := tuples.filter (fun p => primeTupleProduct p ∈ C)
  have hsupport :
      (primeTupleProductSupport tuples).filter (fun n => n ∈ C) =
        selected.image primeTupleProduct := by
    simp [primeTupleProductSupport, selected, Finset.filter_image]
  have hcardNat :
      ((primeTupleProductSupport tuples).filter
        (fun n => n ∈ C)).card <= selected.card := by
    rw [hsupport]
    exact Finset.card_image_le
  have hcard :
      (((primeTupleProductSupport tuples).filter
          (fun n => n ∈ C)).card : Real) <= (selected.card : Real) := by
    exact_mod_cast hcardNat
  rw [sum_primeTupleWeightAtProduct_eq_sum_filter_product_mem]
  change lower *
      (((primeTupleProductSupport tuples).filter
        (fun n => n ∈ C)).card : Real) <=
    ∑ p ∈ selected, primeTupleLogWeight p
  calc
    lower *
        (((primeTupleProductSupport tuples).filter
          (fun n => n ∈ C)).card : Real) <=
      lower * (selected.card : Real) :=
        mul_le_mul_of_nonneg_left hcard hlower
    _ = ∑ _p ∈ selected, lower := by simp [mul_comm]
    _ <= ∑ p ∈ selected, primeTupleLogWeight p := by
      apply Finset.sum_le_sum
      intro p hp
      exact hweight p (Finset.mem_filter.mp hp).1

/-- The eta-quarter coordinate floor for arbitrary, possibly noninterior,
Type II cells. -/
noncomputable def typeIIRemainderEtaCoordinateFloor (eta : Real) : Real :=
  min 1 (eta / 4)

/-- The eta-uniform product floor over every source-allowed arity. -/
noncomputable def typeIIRemainderEtaCellFloor (eta : Real) : Real :=
  typeIIRemainderEtaCoordinateFloor eta ^ typeIIEtaArityCeiling eta

private theorem typeIIRemainderEtaCoordinateFloor_pos
    {eta : Real} (heta : 0 < eta) :
    0 < typeIIRemainderEtaCoordinateFloor eta := by
  simp [typeIIRemainderEtaCoordinateFloor, heta]

private theorem typeIIRemainderEtaCellFloor_pos
    {eta : Real} (heta : 0 < eta) :
    0 < typeIIRemainderEtaCellFloor eta := by
  exact pow_pos (typeIIRemainderEtaCoordinateFloor_pos heta) _

/-- Every Boolean supported product in a full cell contributes at least the
eta-quarter logarithmic weight floor, even when product fibers collide. -/
theorem typeIIRemainderEtaCellFloor_mul_supportCount_le
    {X k : Nat} {a : Fin k -> Real} {delta eta : Real}
    (C : Finset Nat) (hX : 1 < X) (heta : 0 < eta)
    (ha : ∀ i, eta / 2 <= a i)
    (hell : (((k + 1 : Nat) : Real) <= 2 / eta)) :
    typeIIRemainderEtaCellFloor eta *
        Real.log (X : Real) ^ (k + 1) *
          typeIICellSupportCount X a delta eta C <=
      C.sum (majorArcRegionWeightAtProduct X a delta eta) := by
  let q := typeIIRemainderEtaCoordinateFloor eta
  have hq0 : 0 <= q := (typeIIRemainderEtaCoordinateFloor_pos heta).le
  have hq1 : q <= 1 := min_le_left _ _
  have hqEta : q <= eta / 4 := min_le_right _ _
  have hellNat : k + 1 <= typeIIEtaArityCeiling eta := by
    exact_mod_cast hell.trans (Nat.le_ceil (2 / eta))
  have hpower : q ^ typeIIEtaArityCeiling eta <= q ^ (k + 1) :=
    pow_le_pow_of_le_one hq0 hq1 hellNat
  have hweight (p : Fin (k + 1) -> Nat)
      (hp : p ∈ majorArcPrimeTuples X a delta eta) :
      typeIIRemainderEtaCellFloor eta *
          Real.log (X : Real) ^ (k + 1) <= primeTupleLogWeight p := by
    have hpRegion := (mem_majorArcPrimeTuples_iff.mp hp).2
    have hcoordinate : ∀ i, q <= normalizedPrimeLog X (p i) := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact hqEta.trans <|
          (le_max_left (eta / 4)
            (1 - (∑ i, a i) - ((k + 1 : Nat) : Real) * delta)).trans
              hpRegion.2.2
      · have hprefix :
            normalizedPrimeLog X (p j.castSucc) ∈
              Set.Ioc (a j) (a j + delta) := by
          simpa [majorArcLogRegion, projectedLogBox, Fin.init_def] using
            hpRegion.1 j
        have hetaQuarterHalf : eta / 4 <= eta / 2 := by linarith
        exact hqEta.trans <| hetaQuarterHalf.trans <| (ha j).trans hprefix.1.le
    have hproduct :
        q ^ typeIIEtaArityCeiling eta <=
          ∏ i, normalizedPrimeLog X (p i) := by
      calc
        q ^ typeIIEtaArityCeiling eta <= q ^ (k + 1) := hpower
        _ = ∏ _i : Fin (k + 1), q := by simp
        _ <= ∏ i, normalizedPrimeLog X (p i) :=
          Finset.prod_le_prod (fun _ _ => hq0)
            (fun i _ => hcoordinate i)
    rw [primeTupleLogWeight_eq_log_pow_mul_normalizedPrimeLog_prod hX]
    dsimp only [typeIIRemainderEtaCellFloor]
    calc
      q ^ typeIIEtaArityCeiling eta *
          Real.log (X : Real) ^ (k + 1) =
        Real.log (X : Real) ^ (k + 1) *
          q ^ typeIIEtaArityCeiling eta := by ring
      _ <= Real.log (X : Real) ^ (k + 1) *
          ∏ i, normalizedPrimeLog X (p i) :=
        mul_le_mul_of_nonneg_left hproduct (by positivity)
  simpa [typeIICellSupportCount, majorArcRegionWeightAtProduct] using
    mul_card_primeTupleProductSupport_filter_le_sum_weight
      (majorArcPrimeTuples X a delta eta) C
      (typeIIRemainderEtaCellFloor eta *
        Real.log (X : Real) ^ (k + 1))
      (mul_nonneg (typeIIRemainderEtaCellFloor_pos heta).le (by positivity))
      hweight

/-- The decimal local density is nonnegative. -/
theorem restrictedDigitDensity_nonneg (digit : Fin 10) :
    0 <= (restrictedDigitDensity digit : Real) := by
  rw [restrictedDigitDensity_eq]
  split_ifs <;> norm_num

/-- The decimal local density is at most its larger value `10 / 9`. -/
theorem restrictedDigitDensity_le_ten_ninths (digit : Fin 10) :
    (restrictedDigitDensity digit : Real) <= 10 / 9 := by
  rw [restrictedDigitDensity_eq]
  split_ifs <;> norm_num

/--
Rewrite complex norm as the real weighted discrepancy over the exact ambient natural carrier.
-/
theorem norm_typeIIOneCellWeightedDiscrepancy_eq_abs
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

private theorem exists_typeIIRemainderCellPowerThreshold
    (eta : Real) (heta : 0 < eta) :
    ∃ length0 : Nat, ∀ length : Nat, length0 <= length ->
      1 <= length ∧ 2 <= ((10 ^ length : Nat) : Real) ^ (eta / 2) := by
  have hX : Tendsto (fun length : Nat => ((10 ^ length : Nat) : Real))
      atTop atTop := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      (tendsto_pow_atTop_atTop_of_one_lt
        (by norm_num : (1 : Real) < 10))
  have hpow : Tendsto
      (fun length : Nat => ((10 ^ length : Nat) : Real) ^ (eta / 2))
      atTop atTop :=
    (tendsto_rpow_atTop (by positivity)).comp hX
  have heventually : ∀ᶠ length : Nat in atTop,
      1 <= length ∧ 2 <= ((10 ^ length : Nat) : Real) ^ (eta / 2) := by
    filter_upwards [eventually_ge_atTop (1 : Nat),
      hpow.eventually_ge_atTop (2 : Real)] with length hlength hlarge
    exact ⟨hlength, hlarge⟩
  exact eventually_atTop.mp heventually

private theorem typeIIOneCellSupportMass_scalar
    (floor L C delta card total : Real) (k : Nat)
    (hfloor : 0 < floor) (hL : 0 < L) (hC : 0 <= C)
    (hdelta : 0 <= delta) (hcard : 0 <= card)
    (hbound : floor * L ^ (k + 1) * total <=
      229 * card / L + 3 * C * delta ^ k * card * L ^ k) :
    total <= (229 / floor + 3 * C / floor) *
      (card / L ^ (k + 2) + delta ^ k * card / L) := by
  have hdenom : 0 < floor * L ^ (k + 1) :=
    mul_pos hfloor (pow_pos hL _)
  have hdivide : total <=
      (229 * card / L + 3 * C * delta ^ k * card * L ^ k) /
        (floor * L ^ (k + 1)) := by
    apply (le_div_iff₀ hdenom).2
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hbound
  have heq :
      (229 * card / L + 3 * C * delta ^ k * card * L ^ k) /
          (floor * L ^ (k + 1)) =
        (229 / floor) * (card / L ^ (k + 2)) +
          (3 * C / floor) * (delta ^ k * card / L) := by
    field_simp [hfloor.ne', hL.ne']
    ring
  rw [heq] at hdivide
  let t1 : Real := card / L ^ (k + 2)
  let t2 : Real := delta ^ k * card / L
  let c1 : Real := 229 / floor
  let c2 : Real := 3 * C / floor
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
/-- The eta-uniform positive Boolean support mass of one Type II cell. -/
theorem exists_typeIIOneCellSupportMass_eta_upper
    (eta : Real) (heta : 0 < eta) :
    ∃ Ceta : Real, 0 < Ceta ∧
      ∀ mu : Real, 0 < mu ->
        ∃ length0 : Nat, 1 <= length0 ∧
          ∀ length : Nat, length0 <= length ->
          ∀ (digit : Fin 10) (k : Nat) (a : Fin k -> Real)
            (I : Finset (Fin k)),
            let XNat : Nat := 10 ^ length
            let X : Real := (XNat : Real)
            let delta : Real := majorArcM2LogLogDelta XNat
            let A : Finset Nat := paddedRestrictedNumbers digit length
            let B : Finset Nat := maynardAmbientCarrier X
            let supportCount : Finset Nat -> Real :=
              typeIICellSupportCount XNat a delta eta
            (∀ i, eta / 2 <= a i) ->
            (∑ i, a i) < 1 - eta / 2 ->
            (((k + 1 : Nat) : Real) <= 2 / eta) ->
            ((∑ i ∈ I, a i) ∈
                  Set.Icc (9 / 25 + mu) (17 / 40 - mu) ∨
              (∑ i ∈ I, a i) ∈
                  Set.Icc (23 / 40 + mu) (16 / 25 - mu)) ->
            supportCount A +
                (restrictedDigitDensity digit : Real) *
                  (A.card : Real) / X * supportCount B <=
              Ceta *
                (((A.card : Real) / Real.log X ^ (k + 2)) +
                  delta ^ k * (A.card : Real) / Real.log X) := by
  obtain ⟨Cprime, hCprime, hprime⟩ :=
    exists_typeIICellPrimeMass_eta_upper eta heta
  have hweighted := exists_typeIIWeightedOneCellLogError eta heta
  obtain ⟨powerLength, hpower⟩ :=
    exists_typeIIRemainderCellPowerThreshold eta heta
  let floor : Real := typeIIRemainderEtaCellFloor eta
  let Ceta : Real := 229 / floor + 3 * Cprime / floor
  have hfloor : 0 < floor := by
    simpa only [floor] using typeIIRemainderEtaCellFloor_pos heta
  have hCeta : 0 < Ceta := by
    dsimp only [Ceta]
    positivity
  refine ⟨Ceta, hCeta, ?_⟩
  intro mu hmu
  obtain ⟨weightedLength, hweightedLength, hweightedAt⟩ :=
    hweighted mu hmu
  let length0 := max 1 (max weightedLength powerLength)
  refine ⟨length0, by simp [length0], ?_⟩
  intro length hlength digit k a I
  have hlengths :
      1 <= length ∧ weightedLength <= length ∧ powerLength <= length := by
    simpa only [length0, max_le_iff] using hlength
  let XNat : Nat := 10 ^ length
  let X : Real := (XNat : Real)
  let delta : Real := majorArcM2LogLogDelta XNat
  let A : Finset Nat := paddedRestrictedNumbers digit length
  let B : Finset Nat := maynardAmbientCarrier X
  let supportCount : Finset Nat -> Real :=
    typeIICellSupportCount XNat a delta eta
  dsimp only
  intro ha hsum hell hconvenient
  let L : Real := Real.log X
  let card : Real := (A.card : Real)
  let rho : Real := (restrictedDigitDensity digit : Real)
  let lambda : Real := rho * card / X
  let weightSum : Finset Nat -> Real := fun C =>
    ∑ n ∈ C, majorArcRegionWeightAtProduct XNat a delta eta n
  let mass : Real := supportCount A + lambda * supportCount B
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
        (Nat.pow_le_pow_right (by norm_num : 0 < (10 : Nat)) hlengths.1)
    exact (Real.lt_log_iff_exp_lt (by positivity)).mpr <|
      Real.exp_one_lt_three.trans_le
        (by exact_mod_cast (show 3 <= XNat by omega))
  have hlogL : 0 < Real.log L := Real.log_pos hL
  have hdelta : 0 < delta := by
    dsimp only [delta, majorArcM2LogLogDelta, L]
    exact inv_pos.mpr hlogL
  have hinv : L⁻¹ <= delta := by
    have hlogLLe : Real.log L <= L :=
      (Real.log_le_sub_one_of_pos (by linarith : 0 < L)).trans (by linarith)
    have honeDiv := one_div_le_one_div_of_le hlogL hlogLLe
    simpa only [delta, majorArcM2LogLogDelta, L, one_div] using honeDiv
  have hlargeBase : 2 <= (X : Real) ^ (eta / 2) := by
    simpa only [X, XNat] using (hpower length hlengths.2.2).2
  have hlarge : ∀ i, 2 <= (XNat : Real) ^ (a i) := by
    intro i
    apply hlargeBase.trans
    exact Real.rpow_le_rpow_of_exponent_le hX.le (ha i)
  have hrho : 0 <= rho := by
    simpa only [rho] using restrictedDigitDensity_nonneg digit
  have hrhoUpper : rho <= 10 / 9 := by
    simpa only [rho] using restrictedDigitDensity_le_ten_ninths digit
  have hlambda : 0 <= lambda := by
    dsimp only [lambda]
    positivity
  have hweightedReal :
      |weightSum A - lambda * weightSum B| <= 229 * card / L := by
    have hbound := hweightedAt length hlengths.2.1 digit k a I
      ha hsum hell hconvenient
    rw [norm_typeIIOneCellWeightedDiscrepancy_eq_abs
      digit length k a delta eta] at hbound
    simpa only [weightSum, lambda, rho, card, L, A, B, X, XNat, delta] using
      hbound
  have hambient : weightSum B <=
      Cprime * delta ^ k * (XNat : Real) * L ^ k := by
    have hbound := hprime XNat k a delta hXNat hdelta hinv ha hlarge hell
    dsimp only [weightSum, B, X]
    rw [maynardAmbientCarrier_natCast]
    simpa only [L, X] using hbound
  have hsupportA :
      floor * L ^ (k + 1) * supportCount A <= weightSum A := by
    simpa only [floor, L, supportCount, weightSum] using
      typeIIRemainderEtaCellFloor_mul_supportCount_le
        A hXNat heta ha hell
  have hsupportB :
      floor * L ^ (k + 1) * supportCount B <= weightSum B := by
    simpa only [floor, L, supportCount, weightSum] using
      typeIIRemainderEtaCellFloor_mul_supportCount_le
        B hXNat heta ha hell
  have hscaleMass :
      floor * L ^ (k + 1) * mass <= weightSum A + lambda * weightSum B := by
    dsimp only [mass]
    calc
      floor * L ^ (k + 1) *
          (supportCount A + lambda * supportCount B) =
        floor * L ^ (k + 1) * supportCount A +
          lambda * (floor * L ^ (k + 1) * supportCount B) := by ring
      _ <= weightSum A + lambda * weightSum B :=
        add_le_add hsupportA (mul_le_mul_of_nonneg_left hsupportB hlambda)
  have hpositiveMass :
      weightSum A + lambda * weightSum B <=
        |weightSum A - lambda * weightSum B| +
          2 * lambda * weightSum B := by
    have hself :
        weightSum A - lambda * weightSum B <=
          |weightSum A - lambda * weightSum B| := le_abs_self _
    linarith
  have hlambdaAmbient :
      2 * lambda * weightSum B <=
        3 * Cprime * delta ^ k * card * L ^ k := by
    calc
      2 * lambda * weightSum B <=
          2 * lambda * (Cprime * delta ^ k * (XNat : Real) * L ^ k) :=
        mul_le_mul_of_nonneg_left hambient (by positivity)
      _ = 2 * rho * Cprime * delta ^ k * card * L ^ k := by
        dsimp only [lambda, X]
        field_simp [show (XNat : Real) ≠ 0 by positivity]
      _ <= 3 * Cprime * delta ^ k * card * L ^ k := by
        have hrhoThree : 2 * rho <= 3 := by linarith
        have hfactor : 0 <= Cprime * delta ^ k * card * L ^ k := by positivity
        calc
          2 * rho * Cprime * delta ^ k * card * L ^ k =
              (2 * rho) * (Cprime * delta ^ k * card * L ^ k) := by ring
          _ <= 3 * (Cprime * delta ^ k * card * L ^ k) :=
            mul_le_mul_of_nonneg_right hrhoThree hfactor
          _ = 3 * Cprime * delta ^ k * card * L ^ k := by ring
  have hcombined : floor * L ^ (k + 1) * mass <=
      229 * card / L + 3 * Cprime * delta ^ k * card * L ^ k := by
    exact hscaleMass.trans <| hpositiveMass.trans <|
      add_le_add hweightedReal hlambdaAmbient
  have hscalar := typeIIOneCellSupportMass_scalar floor L Cprime delta card mass
    k hfloor (zero_lt_one.trans hL) hCprime.le hdelta.le (by positivity)
    hcombined
  simpa only [Ceta, mass, lambda, rho, card, L, A, B, X, delta,
    supportCount] using hscalar

end

end PrimesRestrictedDigits
