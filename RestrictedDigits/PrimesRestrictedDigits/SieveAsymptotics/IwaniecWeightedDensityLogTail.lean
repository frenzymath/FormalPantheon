import PrimesRestrictedDigits.BasicEstimates.StrictAbelSummation
import PrimesRestrictedDigits.SieveAsymptotics.DecimalDensityRatio

/-!
# Logarithmic tails of normalized sieve-density jumps

This is the first partial-summation step in Iwaniec's Lemma 21, Eq. (8.2),
`IWANIEC-ROSSER-SIEVE-1980`, printed p. 198.
-/

open Finset MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

private noncomputable def reciprocalDensityJump
    (P : Finset Nat) (z : Real) (n : Nat) : Real :=
  if n ∈ P then
    (n : Real)⁻¹ *
      (sieveDensityBelow P (fun q => (q : Real)⁻¹) (n : Real) /
        sieveDensityBelow P (fun q => (q : Real)⁻¹) z)
  else 0

private theorem sum_reciprocalDensityJump_range
    (P : Finset Nat) {t z : Real} (ht : 0 <= t)
    (hprime : ∀ p ∈ P, p.Prime) :
    (∑ k ∈ range (Nat.ceil t), reciprocalDensityJump P z k) =
      (1 - sieveDensityBelow P (fun q => (q : Real)⁻¹) t) /
        sieveDensityBelow P (fun q => (q : Real)⁻¹) z := by
  let V := sieveDensityBelow P (fun q => (q : Real)⁻¹)
  let S := P.filter (fun p : Nat => (p : Real) < t)
  have hVz : V z ≠ 0 := ne_of_gt
    (sieveDensityBelow_reciprocal_pos P z hprime)
  have htelescope := sum_mul_sieveDensityBelow_eq_sub
    P (fun q => (q : Real)⁻¹) (show (0 : Real) <= t from ht)
  have hVzero : V 0 = 1 := by
    have hempty : P.filter (fun p : Nat => (p : Real) < 0) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro p hp
      exact not_lt_of_ge (Nat.cast_nonneg p)
    simp [V, sieveDensityBelow, hempty]
  change (∑ p ∈ P.filter (fun p : Nat =>
      (0 : Real) <= (p : Real) ∧ (p : Real) < t),
    (p : Real)⁻¹ * V p) = V 0 - V t at htelescope
  have htel : (∑ p ∈ S, (p : Real)⁻¹ * V p) = 1 - V t := by
    rw [hVzero] at htelescope
    simpa [S] using htelescope
  have hcarrier :
      (range (Nat.ceil t)).filter (fun k => k ∈ P) = S := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, S]
    constructor
    · rintro ⟨hkceil, hkP⟩
      exact ⟨hkP, Nat.lt_ceil.mp hkceil⟩
    · rintro ⟨hkP, hkt⟩
      exact ⟨Nat.lt_ceil.mpr hkt, hkP⟩
  calc
    (∑ k ∈ range (Nat.ceil t), reciprocalDensityJump P z k) =
        (∑ k ∈ S, (k : Real)⁻¹ * (V k / V z)) := by
      rw [← hcarrier]
      simp [reciprocalDensityJump, Finset.filter_mem_eq_inter, V]
    _ = (∑ k ∈ S, (k : Real)⁻¹ * V k) / V z := by
      rw [sum_div]
      apply sum_congr rfl
      intro k hk
      ring
    _ = (1 - V t) / V z := by rw [htel]

private theorem continuousOn_one_div_mul_log {a b : Real}
    (ha : 1 < a) :
    ContinuousOn (fun t : Real => 1 / (t * Real.log t)) (Icc a b) := by
  have hlog : ContinuousOn Real.log (Icc a b) := by
    apply Real.continuousOn_log.mono
    intro t ht
    exact ne_of_gt (by linarith [ha, ht.1])
  apply continuousOn_const.div (continuousOn_id.mul hlog)
  intro t ht
  apply mul_ne_zero
  · change t ≠ 0
    exact ne_of_gt (by linarith [ha, ht.1])
  · exact ne_of_gt (Real.log_pos (by linarith [ha, ht.1]))

private theorem continuousOn_one_div_mul_log_sq {a b : Real}
    (ha : 1 < a) :
    ContinuousOn (fun t : Real => 1 / (t * Real.log t ^ 2))
      (Icc a b) := by
  have hlog : ContinuousOn Real.log (Icc a b) := by
    apply Real.continuousOn_log.mono
    intro t ht
    exact ne_of_gt (by linarith [ha, ht.1])
  apply continuousOn_const.div (continuousOn_id.mul (hlog.pow 2))
  intro t ht
  apply mul_ne_zero
  · change t ≠ 0
    exact ne_of_gt (by linarith [ha, ht.1])
  · exact pow_ne_zero _
      (ne_of_gt (Real.log_pos (by linarith [ha, ht.1])))

private theorem integral_one_div_mul_log_sq {a b : Real}
    (ha : 1 < a) (hab : a <= b) :
    (∫ t in a..b, 1 / (t * Real.log t ^ 2)) =
      1 / Real.log a - 1 / Real.log b := by
  have hcont : ContinuousOn (-Real.log⁻¹) (Icc a b) := by
    have hlog : ContinuousOn Real.log (Icc a b) := by
      apply Real.continuousOn_log.mono
      intro t ht
      exact ne_of_gt (by linarith [ha, ht.1])
    exact (hlog.inv₀ (by
      intro t ht
      exact ne_of_gt (Real.log_pos (by linarith [ha, ht.1])))).neg
  have hderiv : ∀ t ∈ Ioo a b,
      HasDerivAt (-Real.log⁻¹) (1 / (t * Real.log t ^ 2)) t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (by linarith [ha, ht.1])
    have hlog0 : Real.log t ≠ 0 :=
      ne_of_gt (Real.log_pos (by linarith [ha, ht.1]))
    have hd := ((Real.hasDerivAt_log ht0).inv hlog0).neg
    apply hd.congr_deriv
    symm
    field_simp [ht0, hlog0]
  have hint : IntervalIntegrable
      (fun t : Real => 1 / (t * Real.log t ^ 2)) volume a b :=
    (continuousOn_one_div_mul_log_sq ha).intervalIntegrable_of_Icc hab
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hab hcont hderiv hint]
  simp only [Pi.neg_apply, Pi.inv_apply]
  ring

private theorem ceil_eq_floor_add_one_of_not_natCast
    {t : Real} (ht : 0 <= t)
    (hnot : t ∉ Set.range (fun n : Nat => (n : Real))) :
    Nat.ceil t = Nat.floor t + 1 := by
  apply le_antisymm (Nat.ceil_le_floor_add_one t)
  rw [Nat.add_one_le_ceil_iff]
  apply lt_of_not_ge
  intro hle
  have hfloor := Nat.floor_le ht
  have heq : t = (Nat.floor t : Real) := le_antisymm hle hfloor
  exact hnot ⟨Nat.floor t, heq.symm⟩

private theorem range_ceil_eq_Icc_floor_of_not_natCast
    {t : Real} (ht : 0 <= t)
    (hnot : t ∉ Set.range (fun n : Nat => (n : Real))) :
    range (Nat.ceil t) = Finset.Icc 0 (Nat.floor t) := by
  rw [ceil_eq_floor_add_one_of_not_natCast ht hnot]
  ext k
  simp

private theorem intervalIntegrable_mul_strictPrefix
    (c : Nat -> Real) {g : Real -> Real} {a b : Real}
    (ha : 0 <= a) (hab : a <= b)
    (hg : IntervalIntegrable g volume a b) :
    IntervalIntegrable
      (fun t => g t * ∑ k ∈ range (Nat.ceil t), c k)
      volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  have hgOn : IntegrableOn g (Icc a b) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hg
  have hfloor := integrableOn_mul_sum_Icc (m := 0) c ha hgOn
  apply hfloor.congr
  have hnull : volume (Set.range (fun n : Nat => (n : Real))) = 0 :=
    Set.countable_range (fun n : Nat => (n : Real)) |>.measure_zero volume
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp hnull)] with t ht hnot
  rw [range_ceil_eq_Icc_floor_of_not_natCast (ha.trans ht.1) hnot]

/-- The exact strict-Abel identity for logarithmically weighted normalized
density jumps. See `IWANIEC-ROSSER-SIEVE-1980`, p. 198. -/
theorem sum_reciprocal_mul_densityRatio_mul_logRatio_eq
    (P : Finset Nat) {u z : Real} (hu : 1 < u) (huz : u <= z)
    (hprime : ∀ p ∈ P, p.Prime) :
    (∑ p ∈ P.filter (fun p : Nat =>
        u <= (p : Real) ∧ (p : Real) < z),
      (p : Real)⁻¹ *
        (sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) /
          sieveDensityBelow P (fun q => (q : Real)⁻¹) z) *
        (Real.log (p : Real) / Real.log z)) =
      (Real.log u / Real.log z) *
          (sieveDensityBelow P (fun q => (q : Real)⁻¹) u /
            sieveDensityBelow P (fun q => (q : Real)⁻¹) z) - 1 +
        ∫ t in u..z,
          (sieveDensityBelow P (fun q => (q : Real)⁻¹) t /
              sieveDensityBelow P (fun q => (q : Real)⁻¹) z) /
            (t * Real.log z) := by
  let V : Real -> Real :=
    sieveDensityBelow P (fun q => (q : Real)⁻¹)
  let f : Real -> Real := fun t => Real.log t / Real.log z
  let d : Real -> Real := fun t => 1 / (t * Real.log z)
  let c : Nat -> Real := reciprocalDensityJump P z
  have hzOne : 1 < z := hu.trans_le huz
  have hlogz : 0 < Real.log z := Real.log_pos hzOne
  have hVz : V z ≠ 0 := ne_of_gt
    (sieveDensityBelow_reciprocal_pos P z hprime)
  have hfCont : ContinuousOn f (Icc u z) := by
    dsimp [f]
    apply (Real.continuousOn_log.div_const (Real.log z)).mono
    intro t ht
    exact (by simp; linarith [hu, ht.1])
  have hfDerivAt (t : Real) (ht : 0 < t) : HasDerivAt f (d t) t := by
    have ht0 : t ≠ 0 := ne_of_gt ht
    have hd := (Real.hasDerivAt_log ht0).div_const (Real.log z)
    apply hd.congr_deriv
    dsimp [d]
    field_simp [hlogz.ne']
  have hdCont : ContinuousOn d (Icc u z) := by
    apply continuousOn_const.div (continuousOn_id.mul continuousOn_const)
    intro t ht
    apply mul_ne_zero
    · change t ≠ 0
      exact ne_of_gt (by linarith [hu, ht.1])
    · exact hlogz.ne'
  have hdInt : IntervalIntegrable d volume u z :=
    hdCont.intervalIntegrable_of_Icc huz
  have hfDiff : ∀ t ∈ Ioo u z, DifferentiableAt Real f t := by
    intro t ht
    exact (hfDerivAt t (by linarith [hu, ht.1])).differentiableAt
  have hfInt : IntervalIntegrable (deriv f) volume u z := by
    apply hdInt.congr_uIoo
    intro t ht
    rw [Set.uIoo_of_le huz] at ht
    exact (hfDerivAt t (by linarith [hu, ht.1])).deriv.symm
  have hdEval : (∫ t in u..z, d t) = 1 - f u := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      huz hfCont (by
        intro t ht
        exact hfDerivAt t (by linarith [hu, ht.1])) hdInt]
    dsimp [f]
    rw [div_self hlogz.ne']
  have hprefix (t : Real) (ht : 0 <= t) :
      (∑ k ∈ range (Nat.ceil t), c k) = (1 - V t) / V z :=
    sum_reciprocalDensityJump_range P ht hprime
  have hprefixInt : IntervalIntegrable
      (fun t => d t * ∑ k ∈ range (Nat.ceil t), c k)
      volume u z :=
    intervalIntegrable_mul_strictPrefix c (by linarith [hu]) huz hdInt
  have hratioInt : IntervalIntegrable (fun t => d t * (V t / V z))
      volume u z := by
    apply ((hdInt.div_const (V z)).sub hprefixInt).congr_uIoo
    intro t ht
    rw [Set.uIoo_of_le huz] at ht
    have ht0 : 0 <= t := by linarith [hu, ht.1]
    change d t / V z - d t * (∑ k ∈ range (Nat.ceil t), c k) =
      d t * (V t / V z)
    rw [hprefix t ht0]
    field_simp [hVz]
    all_goals ring
  have hIntegralPrefix :
      (∫ t in u..z, d t * ∑ k ∈ range (Nat.ceil t), c k) =
        (1 - f u) / V z - ∫ t in u..z, d t * (V t / V z) := by
    calc
      (∫ t in u..z, d t * ∑ k ∈ range (Nat.ceil t), c k) =
          ∫ t in u..z, d t / V z - d t * (V t / V z) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht0 : 0 <= t := by
          rw [Set.uIcc_of_le huz] at ht
          linarith [hu, ht.1]
        change d t * (∑ k ∈ range (Nat.ceil t), c k) =
          d t / V z - d t * (V t / V z)
        rw [hprefix t ht0]
        field_simp [hVz]
      _ = (∫ t in u..z, d t) / V z -
          ∫ t in u..z, d t * (V t / V z) := by
        rw [intervalIntegral.integral_sub (hdInt.div_const (V z)) hratioInt,
          intervalIntegral.integral_div]
      _ = (1 - f u) / V z -
          ∫ t in u..z, d t * (V t / V z) := by rw [hdEval]
  have hcarrier :
      (naturalLeftClosedRightOpenInterval u z).filter (fun k => k ∈ P) =
        P.filter (fun p : Nat =>
          u <= (p : Real) ∧ (p : Real) < z) := by
    ext k
    simp only [Finset.mem_filter, mem_naturalLeftClosedRightOpenInterval]
    aesop
  have hLhs :
      (∑ k ∈ naturalLeftClosedRightOpenInterval u z, f k * c k) =
        ∑ p ∈ P.filter (fun p : Nat =>
            u <= (p : Real) ∧ (p : Real) < z),
          (p : Real)⁻¹ * (V p / V z) *
            (Real.log p / Real.log z) := by
    rw [← hcarrier]
    simp [c, f, reciprocalDensityJump, Finset.filter_mem_eq_inter]
    apply sum_congr rfl
    intro k hk
    ring
  have hAbel := sum_mul_eq_sub_sub_integral_mul_strict
    c huz hfCont hfDiff hfInt
  have hDerivIntegral :
      (∫ t in u..z, deriv f t * ∑ k ∈ range (Nat.ceil t), c k) =
        ∫ t in u..z, d t * ∑ k ∈ range (Nat.ceil t), c k := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le huz] at ht
    change deriv f t * (∑ k ∈ range (Nat.ceil t), c k) =
      d t * (∑ k ∈ range (Nat.ceil t), c k)
    rw [(hfDerivAt t (by linarith [hu, ht.1])).deriv]
  have hRatioIntegral :
      (∫ t in u..z, d t * (V t / V z)) =
        ∫ t in u..z, (V t / V z) / (t * Real.log z) := by
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp [d]
    ring
  rw [hLhs, hprefix z (by linarith [hu, huz]),
    hprefix u (by linarith [hu]), hDerivIntegral, hIntegralPrefix,
    hRatioIntegral] at hAbel
  change
    (∑ p ∈ P.filter (fun p : Nat =>
        u <= (p : Real) ∧ (p : Real) < z),
      (p : Real)⁻¹ * (V p / V z) *
        (Real.log p / Real.log z)) =
      (Real.log u / Real.log z) * (V u / V z) - 1 +
        ∫ t in u..z, (V t / V z) / (t * Real.log z)
  rw [hAbel]
  dsimp [f, d]
  rw [div_self hlogz.ne']
  field_simp [hVz]
  all_goals ring

private theorem intervalIntegrable_densityRatio_div_mul_log
    (P : Finset Nat) {u z : Real} (hu : 1 < u) (huz : u <= z)
    (hprime : ∀ p ∈ P, p.Prime) :
    IntervalIntegrable
      (fun t =>
        (sieveDensityBelow P (fun q => (q : Real)⁻¹) t /
            sieveDensityBelow P (fun q => (q : Real)⁻¹) z) /
          (t * Real.log z)) volume u z := by
  let V : Real -> Real :=
    sieveDensityBelow P (fun q => (q : Real)⁻¹)
  let d : Real -> Real := fun t => 1 / (t * Real.log z)
  let c : Nat -> Real := reciprocalDensityJump P z
  have hzOne : 1 < z := hu.trans_le huz
  have hlogz : 0 < Real.log z := Real.log_pos hzOne
  have hVz : V z ≠ 0 := ne_of_gt
    (sieveDensityBelow_reciprocal_pos P z hprime)
  have hdCont : ContinuousOn d (Icc u z) := by
    apply continuousOn_const.div (continuousOn_id.mul continuousOn_const)
    intro t ht
    apply mul_ne_zero
    · change t ≠ 0
      exact ne_of_gt (by linarith [hu, ht.1])
    · exact hlogz.ne'
  have hdInt : IntervalIntegrable d volume u z :=
    hdCont.intervalIntegrable_of_Icc huz
  have hprefixInt : IntervalIntegrable
      (fun t => d t * ∑ k ∈ range (Nat.ceil t), c k)
      volume u z :=
    intervalIntegrable_mul_strictPrefix c (by linarith [hu]) huz hdInt
  have hproductInt : IntervalIntegrable (fun t => d t * (V t / V z))
      volume u z := by
    apply ((hdInt.div_const (V z)).sub hprefixInt).congr_uIoo
    intro t ht
    rw [Set.uIoo_of_le huz] at ht
    have ht0 : 0 <= t := by linarith [hu, ht.1]
    change d t / V z - d t * (∑ k ∈ range (Nat.ceil t), c k) =
      d t * (V t / V z)
    rw [sum_reciprocalDensityJump_range P ht0 hprime]
    change d t / V z - d t * ((1 - V t) / V z) =
      d t * (V t / V z)
    field_simp [hVz]
    all_goals ring
  apply hproductInt.congr
  intro t ht
  dsimp [d, V]
  ring

/-- The strict logarithmic density-tail estimate under a dimension-one ratio
majorant on the same half-open interval. -/
theorem sum_reciprocal_mul_densityRatio_mul_logRatio_le_of_ratioMajorant
    (P : Finset Nat) {K u z : Real} (hK : 0 <= K)
    (hu : 2 <= u) (huz : u < z) (hprime : ∀ p ∈ P, p.Prime)
    (hratio : ∀ t : Real, u <= t -> t < z ->
      sieveDensityBelow P (fun q => (q : Real)⁻¹) t /
          sieveDensityBelow P (fun q => (q : Real)⁻¹) z <=
        (Real.log z / Real.log t) * (1 + K / Real.log t)) :
    (∑ p ∈ P.filter (fun p : Nat =>
        u <= (p : Real) ∧ (p : Real) < z),
      (p : Real)⁻¹ *
        (sieveDensityBelow P (fun q => (q : Real)⁻¹) (p : Real) /
          sieveDensityBelow P (fun q => (q : Real)⁻¹) z) *
        (Real.log (p : Real) / Real.log z)) <=
      (∫ t in u..z, 1 / (t * Real.log t)) +
        2 * K / Real.log u := by
  let V : Real -> Real :=
    sieveDensityBelow P (fun q => (q : Real)⁻¹)
  have huOne : 1 < u := by linarith
  have hzOne : 1 < z := huOne.trans huz
  have hlogu : 0 < Real.log u := Real.log_pos huOne
  have hlogz : 0 < Real.log z := Real.log_pos hzOne
  have hboundaryRaw := hratio u le_rfl huz
  have hboundary :
      (Real.log u / Real.log z) * (V u / V z) <=
        1 + K / Real.log u := by
    calc
      (Real.log u / Real.log z) * (V u / V z) <=
          (Real.log u / Real.log z) *
            ((Real.log z / Real.log u) * (1 + K / Real.log u)) :=
        mul_le_mul_of_nonneg_left hboundaryRaw
          (div_nonneg hlogu.le hlogz.le)
      _ = 1 + K / Real.log u := by
        field_simp [hlogu.ne', hlogz.ne']
  have hleftInt : IntervalIntegrable
      (fun t => (V t / V z) / (t * Real.log z)) volume u z :=
    intervalIntegrable_densityRatio_div_mul_log P huOne huz.le hprime
  have hmainInt : IntervalIntegrable
      (fun t : Real => 1 / (t * Real.log t)) volume u z :=
    (continuousOn_one_div_mul_log huOne).intervalIntegrable_of_Icc huz.le
  have herrBaseInt : IntervalIntegrable
      (fun t : Real => 1 / (t * Real.log t ^ 2)) volume u z :=
    (continuousOn_one_div_mul_log_sq huOne).intervalIntegrable_of_Icc huz.le
  have herrInt : IntervalIntegrable
      (fun t : Real => K / (t * Real.log t ^ 2)) volume u z := by
    apply (herrBaseInt.const_mul K).congr
    intro t ht
    ring
  have hsumInt : IntervalIntegrable
      (fun t : Real =>
        1 / (t * Real.log t) + K / (t * Real.log t ^ 2)) volume u z :=
    hmainInt.add herrInt
  have hintegral :
      (∫ t in u..z, (V t / V z) / (t * Real.log z)) <=
        ∫ t in u..z,
          1 / (t * Real.log t) + K / (t * Real.log t ^ 2) := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo
      huz.le hleftInt hsumInt
    intro t ht
    have hut : u < t := ht.1
    have htPos : 0 < t := (by linarith [hu] : 0 < u).trans hut
    have hlogt : 0 < Real.log t :=
      Real.log_pos ((by linarith [hu] : 1 < u).trans hut)
    calc
      (V t / V z) / (t * Real.log z) <=
          ((Real.log z / Real.log t) * (1 + K / Real.log t)) /
            (t * Real.log z) :=
        div_le_div_of_nonneg_right (hratio t (le_of_lt ht.1) ht.2)
          (mul_pos htPos hlogz).le
      _ = 1 / (t * Real.log t) + K / (t * Real.log t ^ 2) := by
        field_simp [ne_of_gt htPos, hlogt.ne', hlogz.ne']
  have herrEval :
      (∫ t in u..z, K / (t * Real.log t ^ 2)) =
        K * (1 / Real.log u - 1 / Real.log z) := by
    calc
      (∫ t in u..z, K / (t * Real.log t ^ 2)) =
          ∫ t in u..z, K * (1 / (t * Real.log t ^ 2)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        ring
      _ = K * (∫ t in u..z, 1 / (t * Real.log t ^ 2)) := by
        rw [intervalIntegral.integral_const_mul]
      _ = K * (1 / Real.log u - 1 / Real.log z) := by
        rw [integral_one_div_mul_log_sq huOne huz.le]
  have hintegral' :
      (∫ t in u..z, (V t / V z) / (t * Real.log z)) <=
        (∫ t in u..z, 1 / (t * Real.log t)) +
          K * (1 / Real.log u - 1 / Real.log z) := by
    rw [intervalIntegral.integral_add hmainInt herrInt, herrEval] at hintegral
    exact hintegral
  rw [sum_reciprocal_mul_densityRatio_mul_logRatio_eq
    P huOne huz.le hprime]
  calc
    (Real.log u / Real.log z) * (V u / V z) - 1 +
        ∫ t in u..z, (V t / V z) / (t * Real.log z) <=
      (1 + K / Real.log u) - 1 +
        ((∫ t in u..z, 1 / (t * Real.log t)) +
          K * (1 / Real.log u - 1 / Real.log z)) :=
      add_le_add (sub_le_sub_right hboundary 1) hintegral'
    _ = (∫ t in u..z, 1 / (t * Real.log t)) +
        2 * K / Real.log u - K / Real.log z := by ring
    _ <= (∫ t in u..z, 1 / (t * Real.log t)) +
        2 * K / Real.log u := by
      exact sub_le_self _ (div_nonneg hK hlogz.le)

end PrimesRestrictedDigits
