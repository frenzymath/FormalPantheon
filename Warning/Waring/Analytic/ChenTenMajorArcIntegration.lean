import Waring.Analytic.ChenTenMajorArcTranslation
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Integrating the translated Chen major-arc error

This file supplies the regularity and elementary uniform estimates that turn
the checked pointwise `6*q` approximation into a per-arc integral estimate
[CHEN1964-EN, p. 1562, equations (28)-(29); CHEN1964-ZH, p. 728,
equations (24)-(25)].  The bound here is deliberately the coarse bridge before
the later oscillatory-integral refinement.
-/

namespace Waring.Analytic

open MeasureTheory Set
open scoped BigOperators Interval

noncomputable section

/-- The fifth-power perturbation integral depends continuously on its real
frequency parameter. -/
theorem continuous_fifthPerturbationIntegral (P : Nat) :
    Continuous fun z : Real => fifthPerturbationIntegral z P := by
  unfold fifthPerturbationIntegral
  apply intervalIntegral.continuous_of_dominated_interval
      (bound := fun _ : Real => (1 : Real))
  · intro z
    exact (by fun_prop : Continuous fun t : Real =>
      Complex.exp
        (Complex.I * ((2 * Real.pi * z * t ^ 5 : Real) : Complex))).aestronglyMeasurable
  · intro z
    filter_upwards with t
    intro _ht
    rw [Complex.norm_exp_I_mul_ofReal]
  · exact continuous_const.intervalIntegrable 0 P
  · filter_upwards with t
    intro _ht
    fun_prop

/-- Chen's finite fifth-power Weyl sum has its trivial cardinality bound. -/
theorem norm_fifthPowerExponentialSum_le (P : Nat) (alpha : Real) :
    ‖fifthPowerExponentialSum P alpha‖ <= P := by
  unfold fifthPowerExponentialSum
  calc
    ‖∑ x : Fin P, realFifthPowerExponential alpha x‖ <=
        ∑ x : Fin P, ‖realFifthPowerExponential alpha x‖ :=
      norm_sum_le _ _
    _ = P := by
      simp only [realFifthPowerExponential,
        Complex.norm_exp_I_mul_ofReal]
      simp

/-- The modeled Weyl sum on an indexed arc is also bounded trivially by
`P`. -/
theorem norm_chenTenMajorArcWeylModel_le
    (P : Nat) (i : ChenTenArcIndex P) (z : Real) :
    ‖chenTenMajorArcWeylModel P i z‖ <= P := by
  have hq : (0 : Real) < i.denominator := by
    exact_mod_cast i.denominator_pos
  have hcomplete := norm_completePowerSum_le 5
    (i.numerator : ZMod i.denominator)
  have hintegral := norm_fifthPerturbationIntegral_le z P
  unfold chenTenMajorArcWeylModel
  calc
    ‖(i.denominator : Complex)⁻¹ *
          completePowerSum 5 (i.numerator : ZMod i.denominator) *
          fifthPerturbationIntegral z P‖ =
        (i.denominator : Real)⁻¹ *
          ‖completePowerSum 5 (i.numerator : ZMod i.denominator)‖ *
          ‖fifthPerturbationIntegral z P‖ := by
      rw [norm_mul, norm_mul, norm_inv, Complex.norm_natCast]
    _ <= (i.denominator : Real)⁻¹ * i.denominator *
          ‖fifthPerturbationIntegral z P‖ := by
      gcongr
    _ = ‖fifthPerturbationIntegral z P‖ := by
      field_simp
    _ <= P := hintegral

/-- The finite factor in a fifteenth-power difference is bounded by fifteen
copies of the common fourteenth-power majorant. -/
theorem norm_fifteenthPowerDifferenceFactor_le
    (X Y : Complex) (A : Real) (hA : 0 <= A)
    (hX : ‖X‖ <= A) (hY : ‖Y‖ <= A) :
    ‖fifteenthPowerDifferenceFactor X Y‖ <= 15 * A ^ 14 := by
  unfold fifteenthPowerDifferenceFactor
  calc
    ‖∑ k ∈ Finset.range 15, X ^ k * Y ^ (14 - k)‖ <=
        ∑ k ∈ Finset.range 15, ‖X ^ k * Y ^ (14 - k)‖ :=
      norm_sum_le _ _
    _ <= ∑ _k ∈ Finset.range 15, A ^ 14 := by
      apply Finset.sum_le_sum
      intro k hk
      have hk14 : k <= 14 := by
        have hk15 := Finset.mem_range.mp hk
        omega
      rw [norm_mul, norm_pow, norm_pow]
      calc
        ‖X‖ ^ k * ‖Y‖ ^ (14 - k) <=
            A ^ k * A ^ (14 - k) := by
          exact mul_le_mul
            (pow_le_pow_left₀ (norm_nonneg X) hX k)
            (pow_le_pow_left₀ (norm_nonneg Y) hY (14 - k))
            (pow_nonneg (norm_nonneg Y) _) (pow_nonneg hA _)
        _ = A ^ 14 := by
          rw [← pow_add]
          congr 1
          omega
    _ = 15 * A ^ 14 := by simp

/-- The translated actual and modeled integrands differ by at most the coarse
uniform majorant `90*q*P^14` on one Chen arc. -/
theorem norm_chenTenRepresentationIntegrand_sub_modelIntegrand_le_uniform
    {P : Nat} (hP : 1 <= P) (N : Nat) (i : ChenTenArcIndex P) (z : Real)
    (hz : z ∈ Set.Icc (-chenTenMajorArcRadius P i)
      (chenTenMajorArcRadius P i)) :
    ‖chenTenRepresentationIntegrand P N
          (chenTenMajorArcCenter i + z) -
        chenTenMajorArcModelIntegrand P N i z‖ <=
      90 * (i.denominator : Real) * (P : Real) ^ 14 := by
  have hfactor :
      ‖fifteenthPowerDifferenceFactor
          (fifthPowerExponentialSum P
            (chenTenMajorArcCenter i + z))
          (chenTenMajorArcWeylModel P i z)‖ <=
        15 * (P : Real) ^ 14 :=
    norm_fifteenthPowerDifferenceFactor_le _ _ P (by positivity)
      (norm_fifthPowerExponentialSum_le P _)
      (norm_chenTenMajorArcWeylModel_le P i z)
  calc
    ‖chenTenRepresentationIntegrand P N
          (chenTenMajorArcCenter i + z) -
        chenTenMajorArcModelIntegrand P N i z‖ <=
        (6 * (i.denominator : Real)) *
          ‖fifteenthPowerDifferenceFactor
            (fifthPowerExponentialSum P
              (chenTenMajorArcCenter i + z))
            (chenTenMajorArcWeylModel P i z)‖ :=
      norm_chenTenRepresentationIntegrand_sub_modelIntegrand_le
        hP N i z hz
    _ <= (6 * (i.denominator : Real)) *
          (15 * (P : Real) ^ 14) := by
      gcongr
    _ = 90 * (i.denominator : Real) * (P : Real) ^ 14 := by ring

/-- The modeled translated representation integrand is continuous. -/
theorem continuous_chenTenMajorArcModelIntegrand
    (P N : Nat) (i : ChenTenArcIndex P) :
    Continuous fun z : Real => chenTenMajorArcModelIntegrand P N i z := by
  unfold chenTenMajorArcModelIntegrand chenTenMajorArcWeylModel
    chenTenTargetPhase chenTenMajorArcCenter
  have hpsi := continuous_fifthPerturbationIntegral P
  fun_prop

/-- Integrating the coarse uniform pointwise estimate over one indexed arc
gives the denominator-independent error `18*P^10`. -/
theorem norm_setIntegral_chenTenRepresentationIntegrand_sub_model_le
    {P : Nat} (hP : 1 <= P) (N : Nat) (i : ChenTenArcIndex P) :
    ‖(∫ alpha in chenTenArc P i,
          chenTenRepresentationIntegrand P N alpha) -
        ∫ z in -chenTenMajorArcRadius P i..chenTenMajorArcRadius P i,
          chenTenMajorArcModelIntegrand P N i z‖ <=
      18 * (P : Real) ^ 10 := by
  have hPpos : 0 < P := Nat.zero_lt_of_lt hP
  have hradius := chenTenMajorArcRadius_pos hPpos i
  rw [setIntegral_chenTenArc_eq_intervalIntegral_add hPpos]
  have hactual : IntervalIntegrable
      (fun z : Real => chenTenRepresentationIntegrand P N
        (chenTenMajorArcCenter i + z)) MeasureTheory.volume
      (-chenTenMajorArcRadius P i) (chenTenMajorArcRadius P i) :=
    ((continuous_chenTenRepresentationIntegrand P N).comp
      (continuous_const.add continuous_id)).intervalIntegrable _ _
  have hmodel : IntervalIntegrable
      (fun z : Real => chenTenMajorArcModelIntegrand P N i z)
      MeasureTheory.volume (-chenTenMajorArcRadius P i)
      (chenTenMajorArcRadius P i) :=
    (continuous_chenTenMajorArcModelIntegrand P N i).intervalIntegrable _ _
  rw [← intervalIntegral.integral_sub hactual hmodel]
  calc
    ‖∫ z in -chenTenMajorArcRadius P i..chenTenMajorArcRadius P i,
        (chenTenRepresentationIntegrand P N
            (chenTenMajorArcCenter i + z) -
          chenTenMajorArcModelIntegrand P N i z)‖ <=
        (90 * (i.denominator : Real) * (P : Real) ^ 14) *
          |chenTenMajorArcRadius P i -
            (-chenTenMajorArcRadius P i)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro z hz
      have hordered :
          -chenTenMajorArcRadius P i <= chenTenMajorArcRadius P i := by
        linarith [hradius]
      have hz' := Set.uIoc_subset_uIcc hz
      rw [Set.uIcc_of_le hordered] at hz'
      exact norm_chenTenRepresentationIntegrand_sub_modelIntegrand_le_uniform
        hP N i z hz'
    _ = 18 * (P : Real) ^ 10 := by
      rw [abs_of_nonneg (by linarith [hradius])]
      rw [chenTenMajorArcRadius_eq_pointwiseRadius]
      have hq : (i.denominator : Real) ≠ 0 := by
        exact_mod_cast i.denominator_pos.ne'
      have hPR : (P : Real) ≠ 0 := by exact_mod_cast hPpos.ne'
      field_simp
      norm_num

/-- Summing the per-arc estimate controls the difference between the actual
major-arc sum and the sum of modeled centered integrals. -/
theorem norm_sum_setIntegral_chenTenRepresentationIntegrand_sub_model_le
    {P : Nat} (hP : 1 <= P) (N : Nat) :
    ‖(∑ i : ChenTenArcIndex P,
          ∫ alpha in chenTenArc P i,
            chenTenRepresentationIntegrand P N alpha) -
        ∑ i : ChenTenArcIndex P,
          ∫ z in -chenTenMajorArcRadius P i..chenTenMajorArcRadius P i,
            chenTenMajorArcModelIntegrand P N i z‖ <=
      Fintype.card (ChenTenArcIndex P) *
        (18 * (P : Real) ^ 10) := by
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ i : ChenTenArcIndex P,
        ((∫ alpha in chenTenArc P i,
            chenTenRepresentationIntegrand P N alpha) -
          ∫ z in -chenTenMajorArcRadius P i..chenTenMajorArcRadius P i,
            chenTenMajorArcModelIntegrand P N i z)‖ <=
        ∑ i : ChenTenArcIndex P,
          ‖(∫ alpha in chenTenArc P i,
              chenTenRepresentationIntegrand P N alpha) -
            ∫ z in -chenTenMajorArcRadius P i..chenTenMajorArcRadius P i,
              chenTenMajorArcModelIntegrand P N i z‖ :=
      norm_sum_le _ _
    _ <= ∑ _i : ChenTenArcIndex P, 18 * (P : Real) ^ 10 := by
      apply Finset.sum_le_sum
      intro i _hi
      exact norm_setIntegral_chenTenRepresentationIntegrand_sub_model_le
        hP N i
    _ = Fintype.card (ChenTenArcIndex P) *
        (18 * (P : Real) ^ 10) := by simp

/-- After exact model separation, the same finite-sum bound compares the
actual major arcs with the indexed singular terms times their
denominator-dependent truncated singular integrals. -/
theorem norm_sum_setIntegral_chenTenRepresentationIntegrand_sub_singular_le
    {P : Nat} (hP : 1 <= P) (N : Nat) :
    ‖(∑ i : ChenTenArcIndex P,
          ∫ alpha in chenTenArc P i,
            chenTenRepresentationIntegrand P N alpha) -
        ∑ i : ChenTenArcIndex P,
          chenTenIndexedSingularTerm N i *
            chenTenTruncatedSingularIntegral P N i‖ <=
      Fintype.card (ChenTenArcIndex P) *
        (18 * (P : Real) ^ 10) := by
  rw [← sum_intervalIntegral_chenTenMajorArcModelIntegrand_eq]
  exact
    norm_sum_setIntegral_chenTenRepresentationIntegrand_sub_model_le hP N

end

end Waring.Analytic
