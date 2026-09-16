import Waring.Analytic.ChenTenCumulativeVolume

/-!
# Lower volume comparison for Chen's cumulative count

The half-open unit partition admits a total rounding rule. Minkowski's
inequality then puts the ball of radius `X^(1/5) - 15` inside the signed-cell
union, yielding the lower bound and the `O(X^(14/5))` error estimate used in
Chen's Lemma 10 [CHEN1964-EN, p. 1565, equation (36)].
-/

namespace Waring.Analytic

open Set MeasureTheory
open scoped BigOperators ENNReal Pointwise

open BoxIntegral
open BoxIntegral.unitPartition

noncomputable section

/-- Cell magnitude chosen so that the half-open signed cell contains `x`. -/
def roundBase (x : Fin 15 → Real) : Fin 15 → Nat := fun i =>
  if 0 < x i then Nat.ceil |x i| - 1 else Nat.floor |x i|

/-- Positive coordinates use the positive cell; zero uses the nonpositive cell. -/
def roundSign (x : Fin 15 → Real) : Fin 15 → Bool := fun i => decide (0 < x i)

/-- The rounding magnitude and sign place every point in their associated cell. -/
theorem round_point_mem_signedCell
    {x : Fin 15 → Real} :
    x ∈ signedCell (roundBase x) (roundSign x) := by
  apply (BoxIntegral.unitPartition.mem_box_iff (n := 1)).mpr
  intro i
  by_cases hp : 0 < x i
  · have habs : |x i| = x i := abs_of_pos hp
    have hceilpos : 0 < Nat.ceil |x i| := Nat.ceil_pos.mpr (by simpa [habs] using hp)
    have hlt0 : Nat.ceil |x i| - 1 < Nat.ceil |x i| := by omega
    have hlower_abs : ((Nat.ceil |x i| - 1 : Nat) : Real) < |x i| :=
      (Nat.lt_ceil).mp hlt0
    have hlower : ((Nat.ceil |x i| - 1 : Nat) : Real) < x i := by
      simpa [habs] using hlower_abs
    have hupper : x i ≤ ((Nat.ceil |x i| - 1 : Nat) : Real) + 1 := by
      have hc : |x i| ≤ (Nat.ceil |x i| : Real) := Nat.le_ceil _
      rw [Nat.cast_pred hceilpos]
      linarith
    simp [cellIndex, roundBase, roundSign, hp, decide_true]
    exact ⟨hlower, hupper⟩
  · have hn : x i ≤ 0 := le_of_not_gt hp
    have habs : |x i| = -x i := abs_of_nonpos hn
    have hfloor : ((Nat.floor |x i| : Nat) : Real) ≤ |x i| :=
      Nat.floor_le (abs_nonneg _)
    have hfloor' : |x i| < ((Nat.floor |x i| : Nat) : Real) + 1 :=
      Nat.lt_floor_add_one _
    have hlower : (-((Nat.floor |x i| : Nat) : Real) - 1) < x i := by
      have h' : -((Nat.floor |x i| : Nat) : Real) - 1 < -|x i| := by
        linarith
      simpa [habs] using h'
    have hupper : x i ≤ -((Nat.floor |x i| : Nat) : Real) := by
      have h' : -|x i| ≤ -((Nat.floor |x i| : Nat) : Real) := by
        linarith
      simpa [habs] using h'
    simp [cellIndex, roundBase, roundSign, hp, decide_false]
    exact ⟨hlower, hupper⟩

/-- The rounded coordinate magnitude plus one does not undershoot the original magnitude. -/
theorem roundBase_add_one_sub_abs_nonneg
    (x : Fin 15 → Real) (i : Fin 15) :
    0 ≤ ((roundBase x i + 1 : Nat) : Real) - |x i| := by
  by_cases hp : 0 < x i
  · have habs : |x i| = x i := abs_of_pos hp
    have hc : x i ≤ (Nat.ceil (x i) : Real) := Nat.le_ceil (x i)
    simpa [roundBase, hp, habs] using sub_nonneg.mpr hc
  · have hn : x i ≤ 0 := le_of_not_gt hp
    have habs : |x i| = -x i := abs_of_nonpos hn
    have hf : |x i| < ((Nat.floor |x i| : Nat) : Real) + 1 :=
      Nat.lt_floor_add_one _
    have h' : 0 ≤ ((Nat.floor |x i| : Nat) : Real) + 1 - |x i| := by
      linarith [hf]
    simpa [roundBase, hp] using h'

/-- The coordinatewise rounding excess is at most one. -/
theorem roundBase_add_one_sub_abs_le_one
    (x : Fin 15 → Real) (i : Fin 15) :
    ((roundBase x i + 1 : Nat) : Real) - |x i| ≤ 1 := by
  by_cases hp : 0 < x i
  · have habs : |x i| = x i := abs_of_pos hp
    have hc : ((Nat.ceil (x i) : Nat) : Real) < x i + 1 :=
      Nat.ceil_lt_add_one (show (0 : Real) ≤ x i by linarith)
    have h' : ((Nat.ceil (x i) : Nat) : Real) - x i ≤ 1 := by linarith [hc]
    simpa [roundBase, hp, habs] using h'
  · have hn : x i ≤ 0 := le_of_not_gt hp
    have habs : |x i| = -x i := abs_of_nonpos hn
    have hf : ((Nat.floor |x i| : Nat) : Real) ≤ |x i| := Nat.floor_le (abs_nonneg _)
    have h' : ((Nat.floor |x i| : Nat) : Real) + 1 - |x i| ≤ 1 := by
      linarith [hf]
    simpa [roundBase, hp] using h'

local instance fact5 : Fact (1 ≤ ENNReal.ofReal (5 : Real)) :=
  fact_iff.mpr (by norm_num)

/-- The fifteen-dimensional real `ell^5` space used for the rounding argument. -/
abbrev P5 := PiLp (ENNReal.ofReal (5 : Real)) (fun _ : Fin 15 => Real)

/-- Regard a fifteen-dimensional real tuple as an element of `P5`. -/
def lp5 (x : Fin 15 → Real) : P5 := WithLp.toLp (ENNReal.ofReal (5 : Real)) x

/-- The `P5` norm is the fifth root of the sum of fifth powers. -/
theorem lp5_norm (x : Fin 15 → Real) :
    ‖lp5 x‖ = (∑ i, |x i| ^ (5 : Real)) ^ (1 / (5 : Real)) := by
  dsimp [lp5]
  rw [PiLp.norm_eq_sum]
  · simp
  · norm_num

/-- The map from real tuples to `P5` preserves addition. -/
theorem lp5_add (x y : Fin 15 → Real) :
    lp5 (fun i => x i + y i) = lp5 x + lp5 y := by
  apply PiLp.ext
  intro i
  simp [lp5]

/-- The `P5` norm of the coordinatewise rounding excess is at most fifteen. -/
theorem roundError_norm_le (x : Fin 15 → Real) :
    ‖lp5 (fun i => ((roundBase x i + 1 : Nat) : Real) - |x i|)‖ ≤ 15 := by
  rw [lp5_norm]
  have hsum :
      (∑ i, Real.rpow
        (abs (((roundBase x i + 1 : Nat) : Real) - |x i|)) (5 : Real)) ≤ (15 : Real) := by
    calc
      ∑ i, Real.rpow
          (abs (((roundBase x i + 1 : Nat) : Real) - |x i|)) (5 : Real) ≤
          ∑ _i : Fin 15, (1 : Real) := by
        exact Finset.sum_le_sum fun i _ => by
          rw [abs_of_nonneg (roundBase_add_one_sub_abs_nonneg x i)]
          simpa using (Real.rpow_le_rpow
            (roundBase_add_one_sub_abs_nonneg x i)
            (roundBase_add_one_sub_abs_le_one x i)
            (show (0 : Real) ≤ 5 by norm_num))
      _ = 15 := by norm_num
  have hroot :
      (∑ i, Real.rpow
        (abs (((roundBase x i + 1 : Nat) : Real) - |x i|)) (5 : Real)) ^
          (1 / (5 : Real)) ≤ (15 : Real) ^ (1 / (5 : Real)) :=
    Real.rpow_le_rpow
      (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _)
      hsum (by norm_num)
  exact hroot.trans (Real.rpow_le_self_of_one_le (by norm_num) (by norm_num))

/-- The rounded magnitude tuple has norm at most the original norm plus fifteen. -/
theorem roundBase_lp_norm_le (x : Fin 15 → Real) :
    ‖lp5 (fun i => ((roundBase x i + 1 : Nat) : Real))‖ ≤
      ‖lp5 (fun i => |x i|)‖ + 15 := by
  have heq : (fun i => ((roundBase x i + 1 : Nat) : Real)) =
      (fun i => |x i|) +
        (fun i => ((roundBase x i + 1 : Nat) : Real) - |x i|) := by
    funext i
    simp
  rw [heq]
  change ‖lp5 (fun i => |x i| +
    (((roundBase x i + 1 : Nat) : Real) - |x i|))‖ ≤ _
  rw [lp5_add]
  calc
    ‖lp5 (fun i => |x i|) +
        lp5 (fun i => ((roundBase x i + 1 : Nat) : Real) - |x i|)‖ ≤
        ‖lp5 (fun i => |x i|)‖ +
          ‖lp5 (fun i => ((roundBase x i + 1 : Nat) : Real) - |x i|)‖ :=
      norm_add_le _ _
    _ ≤ ‖lp5 (fun i => |x i|)‖ + 15 :=
      add_le_add (le_refl _) (roundError_norm_le x)

/-- Taking coordinatewise absolute values preserves the `P5` norm. -/
theorem lp5_abs_norm (x : Fin 15 → Real) :
    ‖lp5 (fun i => |x i|)‖ = ‖lp5 x‖ := by
  rw [lp5_norm, lp5_norm]
  simp only [abs_abs]

/-- Raising the real fifth root of a natural number to the fifth power recovers it. -/
theorem rpow_fifth_root_pow_five (X : Nat) :
    ((X : Real) ^ (1 / (5 : Real))) ^ (5 : Nat) = (X : Real) := by
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by positivity)]
  norm_num

/-- A rounded tuple inside the fifth-power radius satisfies the natural sum bound. -/
theorem round_sum_nat_le
    {X : Nat} {x : Fin 15 → Real}
    (hnorm : ‖lp5 (fun i => ((roundBase x i + 1 : Nat) : Real))‖ ≤
      (X : Real) ^ (1 / (5 : Real))) :
    ∑ i, (roundBase x i + 1) ^ 5 ≤ X := by
  have hroot :
      (∑ i, |((roundBase x i + 1 : Nat) : Real)| ^ (5 : Real)) ^
          (1 / (5 : Real)) ≤ (X : Real) ^ (1 / (5 : Real)) := by
    rw [lp5_norm] at hnorm
    exact hnorm
  have hsum_nonneg : 0 ≤ ∑ i,
      |((roundBase x i + 1 : Nat) : Real)| ^ (5 : Real) := by
    exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _
  have hroot_nonneg : 0 ≤
      (∑ i, |((roundBase x i + 1 : Nat) : Real)| ^ (5 : Real)) ^
        (1 / (5 : Real)) :=
    Real.rpow_nonneg hsum_nonneg (1 / (5 : Real))
  have hpow := Real.rpow_le_rpow
    hroot_nonneg hroot (by norm_num : (0 : Real) ≤ 5)
  have hpow' :
      (∑ i, |((roundBase x i + 1 : Nat) : Real)| ^ (5 : Real)) ≤
        (X : Real) := by
    rw [← Real.rpow_mul hsum_nonneg, ← Real.rpow_mul (by positivity)] at hpow
    norm_num at hpow ⊢
    simpa [rpow_fifth_root_pow_five] using hpow
  have hpow_nat :
      (∑ i, (((roundBase x i + 1 : Nat) : Real) ^ (5 : Nat))) ≤ (X : Real) := by
    have hi : ∀ i, 0 ≤ (roundBase x i : Real) + 1 := by
      intro i
      positivity
    simpa [abs_of_nonneg (hi _)] using hpow'
  exact_mod_cast hpow_nat

/-- Each rounded coordinate is below `X` when the rounded fifth-power sum is at most `X`. -/
theorem roundBase_lt_of_round_sum_le
    {X : Nat} {x : Fin 15 → Real}
    (hpow : ∑ i, (roundBase x i + 1) ^ 5 ≤ X) (i : Fin 15) :
    roundBase x i < X := by
  have hterm : (roundBase x i + 1) ^ 5 ≤ X := by
    calc
      (roundBase x i + 1) ^ 5 ≤
          ∑ j, (roundBase x j + 1) ^ 5 := by
        simpa using (Finset.single_le_sum
          (s := (Finset.univ : Finset (Fin 15)))
          (f := fun j : Fin 15 => (roundBase x j + 1) ^ 5)
          (fun j _ => Nat.zero_le _) (Finset.mem_univ i))
      _ ≤ X := hpow
  have hs : roundBase x i + 1 ≤ X :=
    (Nat.le_pow (by norm_num : 0 < (5 : Nat))).trans hterm
  omega

/-- The inward-shifted fifth-power ball is covered by valid signed cells. -/
theorem ball15_inner_subset_signedUnion15
    (X : Nat) :
    ball15 ((X : Real) ^ (1 / (5 : Real)) - 15) ⊆ signedUnion15 X := by
  classical
  intro x hx
  let rX : Real := (X : Real) ^ (1 / (5 : Real))
  have hinner : ‖lp5 x‖ ≤ rX - 15 := by
    change (∑ i, Real.rpow |x i| (5 : Real)) ^ (1 / (5 : Real)) ≤
      rX - 15 at hx
    rw [lp5_norm]
    simpa [rX] using hx
  have hround :
      ‖lp5 (fun i => ((roundBase x i + 1 : Nat) : Real))‖ ≤ rX := by
    calc
      ‖lp5 (fun i => ((roundBase x i + 1 : Nat) : Real))‖ ≤
          ‖lp5 (fun i => |x i|)‖ + 15 := roundBase_lp_norm_le x
      _ = ‖lp5 x‖ + 15 := by rw [lp5_abs_norm]
      _ ≤ (rX - 15) + 15 := by linarith
      _ = rX := by ring
  have hsum : ∑ i, (roundBase x i + 1) ^ 5 ≤ X :=
    round_sum_nat_le hround
  have hbase : ∀ i, roundBase x i < X := fun i =>
    roundBase_lt_of_round_sum_le hsum i
  let a : Fin 15 → Fin X := fun i => ⟨roundBase x i, hbase i⟩
  have ha : valid15 X a := by
    dsimp [valid15, a]
    simpa using hsum
  have hxcell : x ∈ signedCell (finTupleVal a) (roundSign x) := by
    change x ∈ signedCell (roundBase x) (roundSign x)
    exact round_point_mem_signedCell (x := x)
  apply Set.mem_iUnion.mpr
  refine ⟨(a, roundSign x), ?_⟩
  apply Set.mem_iUnion.mpr
  refine ⟨?_, hxcell⟩
  apply Finset.mem_product.mpr
  exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩, Finset.mem_univ _⟩

/-- Lower cubic-volume comparison for the cumulative count. -/
theorem K15_lower
    (X : Nat)
    (hX : (15 : Real) ≤ (X : Real) ^ (1 / (5 : Real))) :
    chenTenT15 * ((X : Real) ^ (1 / (5 : Real)) - 15) ^ 15 ≤ (K15 X : Real) := by
  have hrad : 0 ≤ (X : Real) ^ (1 / (5 : Real)) - 15 := by linarith
  have hmono : volume (ball15 ((X : Real) ^ (1 / (5 : Real)) - 15)) ≤
      volume (signedUnion15 X) :=
    measure_mono (ball15_inner_subset_signedUnion15 X)
  have hunion_ne : volume (signedUnion15 X) ≠ ∞ := by
    rw [volume_signedUnion15]
    exact ENNReal.natCast_ne_top _
  have hmonoReal := ENNReal.toReal_mono hunion_ne hmono
  rw [volume_ball15_toReal _ hrad, volume_signedUnion15] at hmonoReal
  norm_num at hmonoReal ⊢
  nlinarith [hmonoReal]

/-- Removing fifteen from a radius changes its fifteenth power by at most `225 * r ^ 14`. -/
theorem fifteenth_power_sub_bound (r : Real) (hr : 15 ≤ r) :
    r ^ 15 - (r - 15) ^ 15 ≤ 225 * r ^ 14 := by
  have hnonneg : 0 ≤ r - 15 := by linarith
  have hfactor : r ^ 15 - (r - 15) ^ 15 =
      (r - (r - 15)) * ∑ k ∈ Finset.range 15,
        r ^ (14 - k) * (r - 15) ^ k := by
    norm_num [Finset.sum_range_succ]
    ring
  have hterm : ∀ k ∈ Finset.range 15,
      r ^ (14 - k) * (r - 15) ^ k ≤ r ^ 14 := by
    intro k hk
    have hk15 : k ≤ 14 := by
      have := Finset.mem_range.mp hk
      omega
    have h2 : (r - 15) ^ k ≤ r ^ k :=
      pow_le_pow_left₀ hnonneg (by linarith) k
    have h3 : r ^ (14 - k) * (r - 15) ^ k ≤
        r ^ (14 - k) * r ^ k :=
      mul_le_mul_of_nonneg_left h2 (pow_nonneg (by linarith) _)
    calc
      r ^ (14 - k) * (r - 15) ^ k ≤ r ^ (14 - k) * r ^ k := h3
      _ = r ^ 14 := by
        rw [← pow_add]
        congr 1
        omega
  have hsum : ∑ k ∈ Finset.range 15, r ^ (14 - k) * (r - 15) ^ k ≤
      ∑ _k ∈ Finset.range 15, r ^ 14 :=
    Finset.sum_le_sum (fun k hk => hterm k hk)
  have hsum' : ∑ k ∈ Finset.range 15, r ^ (14 - k) * (r - 15) ^ k ≤
      15 * r ^ 14 := by
    calc
      _ ≤ ∑ _k ∈ Finset.range 15, r ^ 14 := hsum
      _ = 15 * r ^ 14 := by simp
  rw [hfactor]
  nlinarith [hsum']

/-- Explicit cumulative error bound in Chen's normalization. -/
theorem K15_error_bound
    (X : Nat)
    (hX : (15 : Real) ≤ (X : Real) ^ (1 / (5 : Real))) :
    |(K15 X : Real) - chenTenT15 * (X : Real) ^ 3| ≤
      1000 * chenTenT15 * (X : Real) ^ (14 / (5 : Real)) := by
  let r : Real := (X : Real) ^ (1 / (5 : Real))
  have hr : (15 : Real) ≤ r := by simpa [r] using hX
  have ht : 0 ≤ chenTenT15 := by
    dsimp [chenTenT15]
    positivity
  have hu : (K15 X : Real) ≤ chenTenT15 * (X : Real) ^ 3 := by
    have hu' := K15_upper X
    have htwo : 0 < (2 : Real) ^ 15 := by positivity
    nlinarith [hu']
  have hl : chenTenT15 * (r - 15) ^ 15 ≤ (K15 X : Real) := by
    simpa [r] using K15_lower X hX
  have hr15 : r ^ 15 = (X : Real) ^ 3 := by
    simpa [r] using rpow_fifth_radius_pow_fifteen X
  have hpoly := fifteenth_power_sub_bound r hr
  have hdiff : chenTenT15 * (X : Real) ^ 3 - (K15 X : Real) ≤
      225 * chenTenT15 * r ^ 14 := by
    calc
      chenTenT15 * (X : Real) ^ 3 - (K15 X : Real) =
          chenTenT15 * r ^ 15 - (K15 X : Real) := by rw [hr15]
      _ ≤ chenTenT15 * r ^ 15 - chenTenT15 * (r - 15) ^ 15 := by linarith
      _ = chenTenT15 * (r ^ 15 - (r - 15) ^ 15) := by ring
      _ ≤ chenTenT15 * (225 * r ^ 14) :=
        mul_le_mul_of_nonneg_left hpoly ht
      _ = 225 * chenTenT15 * r ^ 14 := by ring
  have hr14 : r ^ 14 = (X : Real) ^ (14 / (5 : Real)) := by
    dsimp [r]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by positivity)]
    norm_num
  have habs : |(K15 X : Real) - chenTenT15 * (X : Real) ^ 3| =
      chenTenT15 * (X : Real) ^ 3 - (K15 X : Real) := by
    rw [abs_of_nonpos (sub_nonpos.mpr hu)]
    ring
  rw [habs]
  rw [hr14] at hdiff
  have hnonnegpow : 0 ≤ (X : Real) ^ (14 / (5 : Real)) := by positivity
  nlinarith [hdiff, ht, hnonnegpow]

end

end Waring.Analytic
