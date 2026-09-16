import PrimesRestrictedDigits.BasicEstimates.BuchstabSlab
import PrimesRestrictedDigits.BasicEstimates.BuchstabRemainder

/-!
# Prime-sum remainder on a natural Buchstab slab

This file combines the strict Eq. (7.45) decomposition with the explicit
exponent-two remainder estimates on one natural induction slab from
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 7, pp. 217--218.
-/

open Finset MeasureTheory Set
open scoped BigOperators Interval Topology

namespace PrimesRestrictedDigits

private lemma powerSlab_order {m : Nat} {x u : Real} (hx : 1 < x)
    (hm : 2 ≤ m) (hmu : (m : Real) ≤ u) :
    x ^ (1 / u) ≤ x ^ (1 / (m : Real)) := by
  have hm0 : 0 < (m : Real) := by positivity
  apply Real.rpow_le_rpow_of_exponent_le hx.le
  exact one_div_le_one_div_of_le hm0 hmu

private lemma continuousOn_buchstabPrimeWeight_slab
    {m : Nat} {x u : Real} (hx : 1 < x) (hm : 2 ≤ m)
    (hmu : (m : Real) ≤ u) (hlower : 2 ≤ x ^ (1 / u)) :
    ContinuousOn (buchstabPrimeWeight x)
      (Set.Icc (x ^ (1 / u)) (x ^ (1 / (m : Real)))) := by
  let a := x ^ (1 / u)
  let b := x ^ (1 / (m : Real))
  have ht1 : ∀ t ∈ Set.Icc a b, 1 < t := by
    intro t ht
    dsimp [a] at ht
    linarith [hlower, ht.1]
  have hlog : ContinuousOn Real.log (Set.Icc a b) := by
    apply Real.continuousOn_log.mono
    intro t ht
    exact ne_of_gt (zero_lt_one.trans (ht1 t ht))
  have hlog0 : ∀ t ∈ Set.Icc a b, Real.log t ≠ 0 := by
    intro t ht
    exact ne_of_gt (Real.log_pos (ht1 t ht))
  have harg : ContinuousOn (buchstabArgument x) (Set.Icc a b) := by
    unfold buchstabArgument
    exact (continuousOn_const.div hlog hlog0).sub continuousOn_const
  have harg_mem : Set.MapsTo (buchstabArgument x) (Set.Icc a b) (Set.Ici 1) := by
    intro t ht
    have hrange := buchstabArgument_mem_Icc_powerInterval hx (by omega) hmu ht
    have hmreal : (2 : Real) ≤ m := by exact_mod_cast hm
    change (1 : Real) ≤ buchstabArgument x t
    linarith [hrange.1]
  have homega : ContinuousOn
      (fun t => buchstabFunction (buchstabArgument x t)) (Set.Icc a b) :=
    continuousOn_buchstabFunction.comp harg harg_mem
  have hden : ∀ t ∈ Set.Icc a b, t * Real.log t ≠ 0 := by
    intro t ht
    exact mul_ne_zero (ne_of_gt (zero_lt_one.trans (ht1 t ht))) (hlog0 t ht)
  unfold buchstabPrimeWeight
  exact (continuousOn_const.mul homega).div
    (continuousOn_id.mul hlog) hden

private lemma differentiableAt_buchstabPrimeWeight_of_mem_slab
    {m : Nat} {x u t : Real} (hx : 1 < x) (hm : 2 ≤ m)
    (hmu : (m : Real) ≤ u) (hu : u ≤ (m : Real) + 1)
    (hlower : 2 ≤ x ^ (1 / u))
    (ht : t ∈ Set.Ioo (x ^ (1 / u)) (x ^ (1 / (m : Real)))) :
    DifferentiableAt Real (buchstabPrimeWeight x) t := by
  have hgeometry :=
    buchstabArgument_one_lt_and_ne_two_of_mem_slab hx hm hmu hu ht
  have ht1 : 1 < t := by linarith [hlower, ht.1]
  exact (hasDerivAt_buchstabPrimeWeight ht1
    (hasDerivAt_buchstabFunction_of_one_lt_of_ne_two
      hgeometry.1 hgeometry.2)).differentiableAt

private lemma intervalIntegrable_deriv_buchstabPrimeWeight_slab
    {m : Nat} {x u : Real} (hx : 1 < x) (hm : 2 ≤ m)
    (hmu : (m : Real) ≤ u) (hu : u ≤ (m : Real) + 1)
    (hlower : 2 ≤ x ^ (1 / u)) :
    IntervalIntegrable (deriv (buchstabPrimeWeight x)) volume
      (x ^ (1 / u)) (x ^ (1 / (m : Real))) := by
  let a := x ^ (1 / u)
  let b := x ^ (1 / (m : Real))
  let g : Real → Real := fun t =>
    x * (Real.log t + 3) / (t ^ 2 * Real.log t ^ 2)
  have hab : a ≤ b := powerSlab_order hx hm hmu
  have ht1 : ∀ t ∈ Set.Icc a b, 1 < t := by
    intro t ht
    dsimp [a] at ht
    linarith [hlower, ht.1]
  have hlog : ContinuousOn Real.log (Set.Icc a b) := by
    apply Real.continuousOn_log.mono
    intro t ht
    exact ne_of_gt (zero_lt_one.trans (ht1 t ht))
  have hden : ∀ t ∈ Set.Icc a b,
      t ^ 2 * Real.log t ^ 2 ≠ 0 := by
    intro t ht
    exact mul_ne_zero
      (pow_ne_zero _ (ne_of_gt (zero_lt_one.trans (ht1 t ht))))
      (pow_ne_zero _ (ne_of_gt (Real.log_pos (ht1 t ht))))
  have hg_cont : ContinuousOn g (Set.Icc a b) := by
    dsimp [g]
    exact (continuousOn_const.mul (hlog.add continuousOn_const)).div
      ((continuousOn_id.pow 2).mul (hlog.pow 2)) hden
  have hg_int : IntervalIntegrable g volume a b :=
    hg_cont.intervalIntegrable_of_Icc hab
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).2
  have hg_on : IntegrableOn g (Set.Ioo a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).1 hg_int
  apply hg_on.mono'
  · exact (aemeasurable_deriv (buchstabPrimeWeight x)
      (volume.restrict (Set.Ioo a b))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [Real.norm_eq_abs]
    exact abs_deriv_buchstabPrimeWeight_le_of_mem_slab hx hm hmu hu hlower ht

private lemma aemeasurable_primeRemainder_slab
    {m : Nat} {x u : Real} (hlower : 2 ≤ x ^ (1 / u)) :
    AEMeasurable primeRemainder
      (volume.restrict
        (Set.Ioo (x ^ (1 / u)) (x ^ (1 / (m : Real))))) := by
  let a := x ^ (1 / u)
  let b := x ^ (1 / (m : Real))
  have hli : ContinuousOn logarithmicIntegral (Set.Ioo a b) := by
    apply logarithmicIntegral_continuousOn.mono
    intro t ht
    dsimp [a] at ht
    change 1 < t
    linarith [hlower, ht.1]
  unfold primeRemainder
  exact measurable_realPrimeCounting.aemeasurable.sub
    (hli.aemeasurable measurableSet_Ioo)

private lemma buchstabEndpoint_scale
    {x C v M : Real} (hx : 1 < x) (hC : 0 ≤ C)
    (hv : 0 < v) (hvM : v ≤ M) (ht : 2 ≤ x ^ (1 / v)) :
    C * x / Real.log (x ^ (1 / v)) ^ 3 +
        x / (x ^ (1 / v) * Real.log (x ^ (1 / v))) ≤
      M ^ 2 * (1 + C / Real.log 2) * (x / Real.log x ^ 2) := by
  let t := x ^ (1 / v)
  have hx0 : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have htpos : 0 < t := by dsimp [t]; positivity
  have ht1 : 1 < t := by dsimp [t]; linarith
  have hlogt : 0 < Real.log t := Real.log_pos ht1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_le : Real.log 2 ≤ Real.log t :=
    Real.log_le_log (by norm_num) (by simpa [t] using ht)
  have hinvlog : (Real.log t)⁻¹ ≤ (Real.log 2)⁻¹ :=
    (inv_le_inv₀ hlogt hlog2).mpr hlog2_le
  have hlogeq : Real.log t = (1 / v) * Real.log x := by
    dsimp [t]
    exact Real.log_rpow hx0 (1 / v)
  have hlogx_eq : Real.log x = v * Real.log t := by
    rw [hlogeq]
    field_simp
  have hM : 0 < M := hv.trans_le hvM
  have hvsq : v ^ 2 ≤ M ^ 2 := by nlinarith
  have hCratio : C / Real.log t ≤ C / Real.log 2 := by
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinvlog hC
  have hlog_le_t : Real.log t ≤ t := by
    linarith [Real.log_le_sub_one_of_pos htpos]
  have hlogratio : Real.log t / t ≤ 1 :=
    (div_le_one htpos).2 hlog_le_t
  have hscale : 0 ≤ x / Real.log x ^ 2 := by positivity
  have hCeq :
      C * x / Real.log t ^ 3 =
        v ^ 2 * (C / Real.log t) * (x / Real.log x ^ 2) := by
    rw [hlogx_eq]
    field_simp
  have hjumpeq :
      x / (t * Real.log t) =
        v ^ 2 * (Real.log t / t) * (x / Real.log x ^ 2) := by
    rw [hlogx_eq]
    field_simp
  have hCmul :
      v ^ 2 * (C / Real.log t) ≤ M ^ 2 * (C / Real.log 2) := by
    exact mul_le_mul hvsq hCratio (by positivity) (sq_nonneg M)
  have hjumpmul : v ^ 2 * (Real.log t / t) ≤ M ^ 2 := by
    calc
      v ^ 2 * (Real.log t / t) ≤ M ^ 2 * 1 :=
        mul_le_mul hvsq hlogratio (by positivity) (sq_nonneg M)
      _ = M ^ 2 := by ring
  change C * x / Real.log t ^ 3 + x / (t * Real.log t) ≤ _
  rw [hCeq, hjumpeq]
  calc
    v ^ 2 * (C / Real.log t) * (x / Real.log x ^ 2) +
        v ^ 2 * (Real.log t / t) * (x / Real.log x ^ 2) ≤
      (M ^ 2 * (C / Real.log 2)) * (x / Real.log x ^ 2) +
        M ^ 2 * (x / Real.log x ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_right hCmul hscale)
        (mul_le_mul_of_nonneg_right hjumpmul hscale)
    _ = M ^ 2 * (1 + C / Real.log 2) *
        (x / Real.log x ^ 2) := by ring

private lemma buchstabIntegral_scale
    {x C u M b : Real} (hx : 1 < x) (hC : 0 ≤ C)
    (hu : 0 < u) (huM : u ≤ M) (ha : 2 ≤ x ^ (1 / u))
    (hb : 2 ≤ b) :
    C * x *
        (((1 / 2 : Real) * (Real.log (x ^ (1 / u)) ^ 2)⁻¹ +
            (Real.log (x ^ (1 / u)) ^ 3)⁻¹) -
          ((1 / 2 : Real) * (Real.log b ^ 2)⁻¹ +
            (Real.log b ^ 3)⁻¹)) ≤
      M ^ 2 * (C / 2 + C / Real.log 2) *
        (x / Real.log x ^ 2) := by
  let a := x ^ (1 / u)
  have hx0 : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have ha1 : 1 < a := by dsimp [a]; linarith
  have hloga : 0 < Real.log a := Real.log_pos ha1
  have hb1 : 1 < b := by linarith
  have hlogb : 0 < Real.log b := Real.log_pos hb1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_le : Real.log 2 ≤ Real.log a :=
    Real.log_le_log (by norm_num) (by simpa [a] using ha)
  have hinvlog : (Real.log a)⁻¹ ≤ (Real.log 2)⁻¹ :=
    (inv_le_inv₀ hloga hlog2).mpr hlog2_le
  have hlogeq : Real.log a = (1 / u) * Real.log x := by
    dsimp [a]
    exact Real.log_rpow hx0 (1 / u)
  have hlogx_eq : Real.log x = u * Real.log a := by
    rw [hlogeq]
    field_simp
  have hM : 0 < M := hu.trans_le huM
  have husq : u ^ 2 ≤ M ^ 2 := by nlinarith
  have hKb : 0 ≤
      (1 / 2 : Real) * (Real.log b ^ 2)⁻¹ +
        (Real.log b ^ 3)⁻¹ := by positivity
  have hdrop :
      ((1 / 2 : Real) * (Real.log a ^ 2)⁻¹ +
          (Real.log a ^ 3)⁻¹) -
        ((1 / 2 : Real) * (Real.log b ^ 2)⁻¹ +
          (Real.log b ^ 3)⁻¹) ≤
      (1 / 2 : Real) * (Real.log a ^ 2)⁻¹ +
        (Real.log a ^ 3)⁻¹ := by linarith
  have hfirst :
      C * x *
          (((1 / 2 : Real) * (Real.log a ^ 2)⁻¹ +
              (Real.log a ^ 3)⁻¹) -
            ((1 / 2 : Real) * (Real.log b ^ 2)⁻¹ +
              (Real.log b ^ 3)⁻¹)) ≤
        C * x * ((1 / 2 : Real) * (Real.log a ^ 2)⁻¹ +
          (Real.log a ^ 3)⁻¹) :=
    mul_le_mul_of_nonneg_left hdrop (mul_nonneg hC hx0.le)
  have hKaeq :
      C * x * ((1 / 2 : Real) * (Real.log a ^ 2)⁻¹ +
          (Real.log a ^ 3)⁻¹) =
        u ^ 2 * (C * ((1 / 2 : Real) + (Real.log a)⁻¹)) *
          (x / Real.log x ^ 2) := by
    rw [hlogx_eq]
    field_simp
  have hbracket :
      C * ((1 / 2 : Real) + (Real.log a)⁻¹) ≤
        C * ((1 / 2 : Real) + (Real.log 2)⁻¹) := by
    apply mul_le_mul_of_nonneg_left _ hC
    linarith
  have hcoef :
      u ^ 2 * (C * ((1 / 2 : Real) + (Real.log a)⁻¹)) ≤
        M ^ 2 * (C * ((1 / 2 : Real) + (Real.log 2)⁻¹)) :=
    mul_le_mul husq hbracket (by positivity) (sq_nonneg M)
  have hscale : 0 ≤ x / Real.log x ^ 2 := by positivity
  change C * x *
      (((1 / 2 : Real) * (Real.log a ^ 2)⁻¹ +
          (Real.log a ^ 3)⁻¹) -
        ((1 / 2 : Real) * (Real.log b ^ 2)⁻¹ +
          (Real.log b ^ 3)⁻¹)) ≤ _
  calc
    C * x *
        (((1 / 2 : Real) * (Real.log a ^ 2)⁻¹ +
            (Real.log a ^ 3)⁻¹) -
          ((1 / 2 : Real) * (Real.log b ^ 2)⁻¹ +
            (Real.log b ^ 3)⁻¹)) ≤
      C * x * ((1 / 2 : Real) * (Real.log a ^ 2)⁻¹ +
        (Real.log a ^ 3)⁻¹) := hfirst
    _ = u ^ 2 * (C * ((1 / 2 : Real) + (Real.log a)⁻¹)) *
        (x / Real.log x ^ 2) := hKaeq
    _ ≤ M ^ 2 * (C * ((1 / 2 : Real) + (Real.log 2)⁻¹)) *
        (x / Real.log x ^ 2) :=
      mul_le_mul_of_nonneg_right hcoef hscale
    _ = M ^ 2 * (C / 2 + C / Real.log 2) *
        (x / Real.log x ^ 2) := by ring

/-- The transformed-weight prime sum differs from the Eq. (7.45) main integral
by an explicit log-square error under the global weak PNT remainder bound. -/
theorem abs_sum_prime_buchstabPrimeWeight_sub_main_le
    {m : Nat} {x u C : Real}
    (hx : 1 < x) (hm : 2 ≤ m)
    (hmu : (m : Real) ≤ u) (hu : u ≤ (m : Real) + 1)
    (hlower : 2 ≤ x ^ (1 / u)) (hC : 0 ≤ C)
    (hPNT : ∀ t : Real, 2 ≤ t →
      |primeRemainder t| ≤ C * t / Real.log t ^ 2) :
    |(∑ p ∈
        (naturalLeftClosedRightOpenInterval (x ^ (1 / u))
          (x ^ (1 / (m : Real)))).filter Nat.Prime,
        buchstabPrimeWeight x p) -
      ∫ t in (x ^ (1 / u))..(x ^ (1 / (m : Real))),
        buchstabPrimeWeight x t / Real.log t| ≤
      ((m : Real) + 1) ^ 2 *
          (2 + C / 2 + 3 * C / Real.log 2) *
        (x / Real.log x ^ 2) := by
  let a := x ^ (1 / u)
  let b := x ^ (1 / (m : Real))
  let M := (m : Real) + 1
  have hx0 : 0 < x := by linarith
  have hm0 : 0 < (m : Real) := by positivity
  have hu0 : 0 < u := hm0.trans_le hmu
  have hM : 0 < M := by dsimp [M]; positivity
  have huM : u ≤ M := by simpa [M] using hu
  have hmM : (m : Real) ≤ M := by dsimp [M]; linarith
  have hab : a ≤ b := powerSlab_order hx hm hmu
  have ha2 : 2 ≤ a := by simpa [a] using hlower
  have hb2 : 2 ≤ b := ha2.trans hab
  have ha1 : 1 < a := by linarith
  have hcont : ContinuousOn (buchstabPrimeWeight x) (Set.Icc a b) := by
    simpa [a, b] using
      continuousOn_buchstabPrimeWeight_slab hx hm hmu hlower
  have hdiff : ∀ t ∈ Set.Ioo a b,
      DifferentiableAt Real (buchstabPrimeWeight x) t := by
    intro t ht
    exact differentiableAt_buchstabPrimeWeight_of_mem_slab
      hx hm hmu hu hlower (by simpa [a, b] using ht)
  have hint : IntervalIntegrable
      (deriv (buchstabPrimeWeight x)) volume a b := by
    simpa [a, b] using
      intervalIntegrable_deriv_buchstabPrimeWeight_slab hx hm hmu hu hlower
  have hdecomp := sum_prime_halfOpen_eq_main_add_remainders
    (f := buchstabPrimeWeight x) ha1 hab hcont hdiff hint
  have harg_a := buchstabArgument_mem_Icc_powerInterval hx (by omega) hmu
    (show a ∈ Set.Icc a b from ⟨le_rfl, hab⟩)
  have harg_b := buchstabArgument_mem_Icc_powerInterval hx (by omega) hmu
    (show b ∈ Set.Icc a b from ⟨hab, le_rfl⟩)
  have hmreal : (2 : Real) ≤ m := by exact_mod_cast hm
  have hva : 1 ≤ buchstabArgument x a := by linarith [harg_a.1]
  have hvb : 1 ≤ buchstabArgument x b := by linarith [harg_b.1]
  have hEa0 := abs_buchstabPrimeWeight_mul_strictPrimeRemainder_le
    (x := x) (C := C) (t := a) (by linarith) ha2 hva (hPNT a ha2)
  have hEb0 := abs_buchstabPrimeWeight_mul_strictPrimeRemainder_le
    (x := x) (C := C) (t := b) (by linarith) hb2 hvb (hPNT b hb2)
  have hEa :
      |buchstabPrimeWeight x a * strictPrimeRemainder a| ≤
        M ^ 2 * (1 + C / Real.log 2) *
          (x / Real.log x ^ 2) := by
    apply hEa0.trans
    simpa [a] using buchstabEndpoint_scale
      (x := x) (C := C) (v := u) (M := M)
      hx hC hu0 huM hlower
  have hEb :
      |buchstabPrimeWeight x b * strictPrimeRemainder b| ≤
        M ^ 2 * (1 + C / Real.log 2) *
          (x / Real.log x ^ 2) := by
    apply hEb0.trans
    simpa [b] using buchstabEndpoint_scale
      (x := x) (C := C) (v := (m : Real)) (M := M)
      hx hC hm0 hmM hb2
  have hR : ∀ t ∈ Set.Ioo a b,
      |primeRemainder t| ≤ C * t / Real.log t ^ 2 := by
    intro t ht
    exact hPNT t (ha2.trans ht.1.le)
  have hD : ∀ t ∈ Set.Ioo a b,
      |deriv (buchstabPrimeWeight x) t| ≤
        x * (Real.log t + 3) / (t ^ 2 * Real.log t ^ 2) := by
    intro t ht
    exact abs_deriv_buchstabPrimeWeight_le_of_mem_slab
      hx hm hmu hu hlower (by simpa [a, b] using ht)
  have hRm : AEMeasurable primeRemainder
      (volume.restrict (Set.Ioo a b)) := by
    simpa [a, b] using
      (aemeasurable_primeRemainder_slab (m := m) hlower)
  have hInt0 := abs_integral_mul_deriv_of_log_bounds
    (x := x) (C := C) (R := primeRemainder)
    (f := buchstabPrimeWeight x) ha2 hab hR hD hRm
  have hInt :
      |∫ t in a..b,
          primeRemainder t * deriv (buchstabPrimeWeight x) t| ≤
        M ^ 2 * (C / 2 + C / Real.log 2) *
          (x / Real.log x ^ 2) := by
    apply hInt0.trans
    exact buchstabIntegral_scale
      (x := x) (C := C) (u := u) (M := M) (b := b)
      hx hC hu0 huM ha2 hb2
  have hInt' :
      |∫ t in a..b,
          deriv (buchstabPrimeWeight x) t * primeRemainder t| ≤
        M ^ 2 * (C / 2 + C / Real.log 2) *
          (x / Real.log x ^ 2) := by
    have hcomm :
        (∫ t in a..b,
            deriv (buchstabPrimeWeight x) t * primeRemainder t) =
          ∫ t in a..b,
            primeRemainder t * deriv (buchstabPrimeWeight x) t := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact mul_comm _ _
    rw [hcomm]
    exact hInt
  change |(∑ p ∈
      (naturalLeftClosedRightOpenInterval a b).filter Nat.Prime,
      buchstabPrimeWeight x p) -
    ∫ t in a..b, buchstabPrimeWeight x t / Real.log t| ≤ _
  have hres :
      |(∑ p ∈
          (naturalLeftClosedRightOpenInterval a b).filter Nat.Prime,
          buchstabPrimeWeight x p) -
        ∫ t in a..b, buchstabPrimeWeight x t / Real.log t| ≤
      |buchstabPrimeWeight x b * strictPrimeRemainder b| +
        |buchstabPrimeWeight x a * strictPrimeRemainder a| +
        |∫ t in a..b,
          deriv (buchstabPrimeWeight x) t * primeRemainder t| := by
    rw [hdecomp]
    calc
      |((∫ t in a..b, buchstabPrimeWeight x t / Real.log t) +
            buchstabPrimeWeight x b * strictPrimeRemainder b -
            buchstabPrimeWeight x a * strictPrimeRemainder a -
            (∫ t in a..b,
              deriv (buchstabPrimeWeight x) t * primeRemainder t)) -
          ∫ t in a..b, buchstabPrimeWeight x t / Real.log t| =
        |(buchstabPrimeWeight x b * strictPrimeRemainder b -
            buchstabPrimeWeight x a * strictPrimeRemainder a) -
          ∫ t in a..b,
            deriv (buchstabPrimeWeight x) t * primeRemainder t| := by
        congr 1
        ring
      _ ≤ |buchstabPrimeWeight x b * strictPrimeRemainder b -
            buchstabPrimeWeight x a * strictPrimeRemainder a| +
          |∫ t in a..b,
            deriv (buchstabPrimeWeight x) t * primeRemainder t| :=
        abs_sub _ _
      _ ≤ (|buchstabPrimeWeight x b * strictPrimeRemainder b| +
            |buchstabPrimeWeight x a * strictPrimeRemainder a|) +
          |∫ t in a..b,
            deriv (buchstabPrimeWeight x) t * primeRemainder t| := by
        exact add_le_add (abs_sub _ _) le_rfl
      _ = _ := by ring
  apply hres.trans
  calc
    |buchstabPrimeWeight x b * strictPrimeRemainder b| +
        |buchstabPrimeWeight x a * strictPrimeRemainder a| +
        |∫ t in a..b,
          deriv (buchstabPrimeWeight x) t * primeRemainder t| ≤
      (M ^ 2 * (1 + C / Real.log 2) *
          (x / Real.log x ^ 2) +
        M ^ 2 * (1 + C / Real.log 2) *
          (x / Real.log x ^ 2)) +
        M ^ 2 * (C / 2 + C / Real.log 2) *
          (x / Real.log x ^ 2) :=
      add_le_add (add_le_add hEb hEa) hInt'
    _ = M ^ 2 * (2 + C / 2 + 3 * C / Real.log 2) *
        (x / Real.log x ^ 2) := by ring

end PrimesRestrictedDigits
