import Waring.Analytic.ChenTenOscillatoryIntegral
import Waring.Analytic.ChenTenMajorArcIntegration
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Chen's full singular integral

This module packages the real-frequency kernel, its cubic outer decay,
whole-line integrability, conjugation symmetry, and an explicit tail estimate.
-/

namespace Waring.Analytic

open MeasureTheory Set Filter Asymptotics
open scoped Interval Topology ComplexConjugate

noncomputable section

/-- Chen's full singular integral over the real frequency line. -/
def chenTenSingularIntegral (P N : Nat) : Complex :=
  ∫ z : Real, chenTenSingularIntegralKernel P N z

/-- The real-frequency singular-integral kernel is continuous. -/
theorem continuous_chenTenSingularIntegralKernel (P N : Nat) :
    Continuous (chenTenSingularIntegralKernel P N) := by
  unfold chenTenSingularIntegralKernel chenTenTargetPhase
  have hpsi := continuous_fifthPerturbationIntegral P
  fun_prop

/-- Conjugating the target phase reverses its real frequency. -/
theorem conj_chenTenTargetPhase (N : Nat) (z : Real) :
    conj (chenTenTargetPhase N z) = chenTenTargetPhase N (-z) := by
  unfold chenTenTargetPhase
  rw [← Complex.exp_conj]
  congr 1
  apply Complex.ext <;> simp

/-- Conjugating the kernel reverses the real frequency. -/
theorem conj_chenTenSingularIntegralKernel (P N : Nat) (z : Real) :
    conj (chenTenSingularIntegralKernel P N z) =
      chenTenSingularIntegralKernel P N (-z) := by
  unfold chenTenSingularIntegralKernel
  rw [map_mul, map_pow, conj_fifthPerturbationIntegral,
    conj_chenTenTargetPhase]

/-- The kernel norm is even in the frequency. -/
theorem norm_chenTenSingularIntegralKernel_neg (P N : Nat) (z : Real) :
    ‖chenTenSingularIntegralKernel P N (-z)‖ =
      ‖chenTenSingularIntegralKernel P N z‖ := by
  rw [← conj_chenTenSingularIntegralKernel, Complex.norm_conj]

/-- The checked trivial perturbation bound gives the kernel bound `P^15`. -/
theorem norm_chenTenSingularIntegralKernel_le_trivial
    (P N : Nat) (z : Real) :
    ‖chenTenSingularIntegralKernel P N z‖ ≤ (P : Real) ^ 15 := by
  calc
    ‖chenTenSingularIntegralKernel P N z‖ =
        ‖fifthPerturbationIntegral z P‖ ^ 15 := by
      simp [chenTenSingularIntegralKernel, norm_pow]
    _ ≤ (P : Real) ^ 15 := pow_le_pow_left₀ (norm_nonneg _)
      (norm_fifthPerturbationIntegral_le z P) 15

/-- The checked oscillatory bound gives cubic decay of the full kernel. -/
theorem norm_chenTenSingularIntegralKernel_le_decay
    (P N : Nat) {z : Real} (hz : z ≠ 0) :
    ‖chenTenSingularIntegralKernel P N z‖ ≤
      (2 : Real) ^ 15 * |z| ^ (-3 : Real) := by
  have hpsi := norm_fifthPerturbationIntegral_le_two_mul_abs_rpow z P hz
  have hpow : ‖fifthPerturbationIntegral z P‖ ^ 15 ≤
      (2 * |z| ^ (-(1 : Real) / 5)) ^ 15 := by
    gcongr
  calc
    ‖chenTenSingularIntegralKernel P N z‖ =
        ‖fifthPerturbationIntegral z P‖ ^ 15 := by
      simp [chenTenSingularIntegralKernel, norm_pow]
    _ ≤ (2 * |z| ^ (-(1 : Real) / 5)) ^ 15 := hpow
    _ = (2 : Real) ^ 15 * |z| ^ (-3 : Real) := by
      rw [mul_pow]
      have hpow' : (|z| ^ (-(1 : Real) / 5)) ^ (15 : Nat) =
          |z| ^ (-3 : Real) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg z)]
        norm_num
      rw [hpow']

private theorem norm_chenTenSingularIntegralKernel_le_rpow
    (P N : Nat) {z : Real} (hz : 0 < z) :
    ‖chenTenSingularIntegralKernel P N z‖ <=
      (2 : Real) ^ 15 * z ^ (-3 : Real) := by
  simpa [abs_of_pos hz] using
    norm_chenTenSingularIntegralKernel_le_decay P N hz.ne'

private theorem chenTenSingularIntegralKernel_isBigO_atTop (P N : Nat) :
    chenTenSingularIntegralKernel P N =O[atTop]
      (fun z : Real => z ^ (-3 : Real)) := by
  rw [isBigO_iff]
  refine ⟨(2 : Real) ^ 15, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : Real)] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hz.le _)]
  exact norm_chenTenSingularIntegralKernel_le_rpow P N hz

/-- The full real-frequency kernel is Bochner integrable. -/
theorem integrable_chenTenSingularIntegralKernel (P N : Nat) :
    Integrable (chenTenSingularIntegralKernel P N) := by
  apply (continuous_chenTenSingularIntegralKernel P N).locallyIntegrable
    |>.integrable_of_isBigO_atTop_of_norm_isNegInvariant
      (g := fun z : Real => z ^ (-3 : Real))
  · filter_upwards with z
    exact (norm_chenTenSingularIntegralKernel_neg P N z).symm
  · exact chenTenSingularIntegralKernel_isBigO_atTop P N
  · rw [integrableAtFilter_rpow_atTop_iff]
    norm_num

private theorem integrableOn_chenTenDecayMajorant_Ici {r : Real} (hr : 0 < r) :
    IntegrableOn (fun z : Real => (2 : Real) ^ 15 * z ^ (-3 : Real)) (Ici r) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  exact (integrableOn_Ioi_rpow_of_lt (a := (-3 : Real))
    (c := r) (by norm_num) hr).const_mul _

private theorem norm_setIntegral_chenTenSingularIntegralKernel_Ici_le
    (P N : Nat) {r : Real} (hr : 0 < r) :
    ‖∫ z in Ici r, chenTenSingularIntegralKernel P N z‖ ≤
      ((2 : Real) ^ 15 / 2) * r ^ (-2 : Real) := by
  have hmajor := integrableOn_chenTenDecayMajorant_Ici hr
  have hkernel : IntegrableOn (chenTenSingularIntegralKernel P N) (Ici r) :=
    (integrable_chenTenSingularIntegralKernel P N).integrableOn
  calc
    ‖∫ z in Ici r, chenTenSingularIntegralKernel P N z‖ ≤
        ∫ z in Ici r, (2 : Real) ^ 15 * z ^ (-3 : Real) := by
      apply norm_integral_le_of_norm_le hmajor
      filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
      have hzpos : 0 < z := hr.trans_le hz
      have hdec := norm_chenTenSingularIntegralKernel_le_rpow P N hzpos
      exact hdec
    _ = (2 : Real) ^ 15 *
          (∫ z in Ici r, z ^ (-3 : Real)) := by
      rw [integral_const_mul]
    _ = ((2 : Real) ^ 15 / 2) * r ^ (-2 : Real) := by
      rw [integral_Ici_eq_integral_Ioi,
        integral_Ioi_rpow_of_lt (a := (-3 : Real)) (by norm_num) hr]
      ring_nf

private theorem norm_setIntegral_chenTenSingularIntegralKernel_Iic_neg_le
    (P N : Nat) {r : Real} (hr : 0 < r) :
    ‖∫ z in Iic (-r), chenTenSingularIntegralKernel P N z‖ ≤
      ((2 : Real) ^ 15 / 2) * r ^ (-2 : Real) := by
  have hchange := integral_comp_neg_Iic (-r)
    (fun z : Real => chenTenSingularIntegralKernel P N (-z))
  have heq :
      (∫ z in Iic (-r), chenTenSingularIntegralKernel P N z) =
        ∫ z in Ici r, conj (chenTenSingularIntegralKernel P N z) := by
    calc
      (∫ z in Iic (-r), chenTenSingularIntegralKernel P N z) =
          ∫ z in Ioi r, chenTenSingularIntegralKernel P N (-z) := by
        simpa only [Function.comp_apply, neg_neg] using hchange
      _ = ∫ z in Ioi r, conj (chenTenSingularIntegralKernel P N z) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro z hz
        exact (conj_chenTenSingularIntegralKernel P N z).symm
      _ = conj (∫ z in Ioi r, chenTenSingularIntegralKernel P N z) := by
        exact integral_conj (μ := volume.restrict (Ioi r))
          (f := fun z : Real => chenTenSingularIntegralKernel P N z)
      _ = conj (∫ z in Ici r, chenTenSingularIntegralKernel P N z) := by
        congr 1
        exact (integral_Ici_eq_integral_Ioi (f :=
          chenTenSingularIntegralKernel P N)).symm
      _ = ∫ z in Ici r, conj (chenTenSingularIntegralKernel P N z) := by
        exact (integral_conj (μ := volume.restrict (Ici r))
          (f := fun z : Real => chenTenSingularIntegralKernel P N z)).symm
  calc
    ‖∫ z in Iic (-r), chenTenSingularIntegralKernel P N z‖ =
        ‖∫ z in Ici r, conj (chenTenSingularIntegralKernel P N z)‖ := by rw [heq]
    _ = ‖conj (∫ z in Ici r, chenTenSingularIntegralKernel P N z)‖ := by
      rw [integral_conj (μ := volume.restrict (Ici r))]
    _ = ‖∫ z in Ici r, chenTenSingularIntegralKernel P N z‖ :=
      Complex.norm_conj _
    _ ≤ ((2 : Real) ^ 15 / 2) * r ^ (-2 : Real) :=
      norm_setIntegral_chenTenSingularIntegralKernel_Ici_le P N hr

private theorem tail_set_eq_outer_intervals {r : Real} :
    {z : Real | r ≤ |z|} = Iic (-r) ∪ Ici r := by
  ext z
  simp only [mem_setOf_eq, mem_union, mem_Iic, mem_Ici]
  constructor
  · intro hz
    by_cases hzr : r ≤ z
    · exact Or.inr hzr
    · left
      have hbranch := (le_abs.mp hz).resolve_left hzr
      linarith
  · intro hz
    rcases hz with hz | hz
    · exact le_abs.mpr (Or.inr (by linarith))
    · exact le_abs.mpr (Or.inl hz)

/-- Subtracting a centered truncation leaves the two outer tails. -/
theorem chenTenSingularIntegral_sub_intervalIntegral_eq_tail
    (P N : Nat) {r : Real} (hr : 0 < r) :
    chenTenSingularIntegral P N -
        (∫ z in -r..r, chenTenSingularIntegralKernel P N z) =
      ∫ z in {z : Real | r ≤ |z|}, chenTenSingularIntegralKernel P N z := by
  let K : Real → Complex := chenTenSingularIntegralKernel P N
  have hint : Integrable K := integrable_chenTenSingularIntegralKernel P N
  have hleft : IntegrableOn K (Iic (-r)) := hint.integrableOn
  have hrightNeg : IntegrableOn K (Ioi (-r)) := hint.integrableOn
  have hrightPos : IntegrableOn K (Ioi r) := hint.integrableOn
  have hfull := intervalIntegral.integral_Iic_add_Ioi hleft hrightNeg
  have hsplit := intervalIntegral.integral_interval_add_Ioi hrightNeg hrightPos
  have hdisj : Disjoint (Iic (-r)) (Ici r) := by
    rw [disjoint_comm]
    exact (Ici_disjoint_Iic).2 (by linarith)
  have htail :
      (∫ z in {z : Real | r ≤ |z|}, K z) =
        (∫ z in Iic (-r), K z) + ∫ z in Ioi r, K z := by
    rw [tail_set_eq_outer_intervals]
    rw [setIntegral_union hdisj measurableSet_Ici hleft hint.integrableOn]
    rw [integral_Ici_eq_integral_Ioi]
  change (∫ z : Real, K z) - (∫ z in -r..r, K z) = _
  calc
    (∫ z : Real, K z) - (∫ z in -r..r, K z) =
        ((∫ z in Iic (-r), K z) + ∫ z in Ioi (-r), K z) -
          ∫ z in -r..r, K z := by rw [hfull]
    _ = (∫ z in Iic (-r), K z) + ∫ z in Ioi r, K z := by
      rw [← hsplit]
      abel
    _ = ∫ z in {z : Real | r ≤ |z|}, K z := htail.symm

/-- The outer tail has norm at most `2^15 * r^(-2)`. -/
theorem norm_setIntegral_chenTenSingularIntegralKernel_tail_le
    (P N : Nat) {r : Real} (hr : 0 < r) :
    ‖∫ z in {z : Real | r ≤ |z|}, chenTenSingularIntegralKernel P N z‖ ≤
      (2 : Real) ^ 15 * r ^ (-2 : Real) := by
  have hneg : Disjoint (Iic (-r)) (Ici r) := by
    rw [disjoint_comm]
    exact (Ici_disjoint_Iic).2 (by linarith)
  have hintneg : IntegrableOn (chenTenSingularIntegralKernel P N) (Iic (-r)) :=
    (integrable_chenTenSingularIntegralKernel P N).integrableOn
  have hintpos : IntegrableOn (chenTenSingularIntegralKernel P N) (Ici r) :=
    (integrable_chenTenSingularIntegralKernel P N).integrableOn
  rw [tail_set_eq_outer_intervals]
  rw [setIntegral_union hneg measurableSet_Ici hintneg hintpos]
  calc
    ‖(∫ z in Iic (-r), chenTenSingularIntegralKernel P N z) +
        ∫ z in Ici r, chenTenSingularIntegralKernel P N z‖ ≤
        ‖∫ z in Iic (-r), chenTenSingularIntegralKernel P N z‖ +
          ‖∫ z in Ici r, chenTenSingularIntegralKernel P N z‖ := norm_add_le _ _
    _ ≤ ((2 : Real) ^ 15 / 2) * r ^ (-2 : Real) +
          ((2 : Real) ^ 15 / 2) * r ^ (-2 : Real) := add_le_add
      (norm_setIntegral_chenTenSingularIntegralKernel_Iic_neg_le P N hr)
      (norm_setIntegral_chenTenSingularIntegralKernel_Ici_le P N hr)
    _ = (2 : Real) ^ 15 * r ^ (-2 : Real) := by ring

/-- The centered truncation differs from the full singular integral by at
most `2^15 * r^(-2)`. -/
theorem norm_chenTenSingularIntegral_sub_intervalIntegral_le
    (P N : Nat) {r : Real} (hr : 0 < r) :
    ‖chenTenSingularIntegral P N -
        (∫ z in -r..r, chenTenSingularIntegralKernel P N z)‖ ≤
      (2 : Real) ^ 15 * r ^ (-2 : Real) := by
  rw [chenTenSingularIntegral_sub_intervalIntegral_eq_tail P N hr]
  exact norm_setIntegral_chenTenSingularIntegralKernel_tail_le P N hr

/-- Conjugating the full integral leaves it unchanged. -/
theorem conj_chenTenSingularIntegral (P N : Nat) :
    conj (chenTenSingularIntegral P N) = chenTenSingularIntegral P N := by
  unfold chenTenSingularIntegral
  rw [← integral_conj]
  calc
    (∫ z : Real, conj (chenTenSingularIntegralKernel P N z)) =
        ∫ z : Real, chenTenSingularIntegralKernel P N (-z) := by
      apply integral_congr_ae
      filter_upwards with z
      exact conj_chenTenSingularIntegralKernel P N z
    _ = ∫ z : Real, chenTenSingularIntegralKernel P N z := by
      simpa using (Measure.measurePreserving_neg (volume : Measure Real)).integral_comp
        (Homeomorph.neg Real).measurableEmbedding
        (chenTenSingularIntegralKernel P N)

/-- The full singular integral is real-valued by frequency reflection. -/
theorem chenTenSingularIntegral_im_eq_zero (P N : Nat) :
    (chenTenSingularIntegral P N).im = 0 :=
  Complex.conj_eq_iff_im.mp (conj_chenTenSingularIntegral P N)

end

end Waring.Analytic
