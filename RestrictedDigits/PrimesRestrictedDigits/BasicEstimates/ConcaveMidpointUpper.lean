import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import PrimesRestrictedDigits.BasicEstimates.ConvexTrapezoidalUpper
/-! # ConcaveMidpointUpper -/

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

def midpoint_integral (f : Real -> Real) (N : Nat) (a b : Real) : Real :=
  (b - a) / (N : Real) *
    ∑ k ∈ Finset.range N,
      f (a + ((k : Real) + 1 / 2) * (b - a) / (N : Real))

private theorem intervalIntegral_le_midpoint_one_of_concaveOn
    {f : Real -> Real} {a b : Real}
    (hf : ConcaveOn Real (Icc a b) f)
    (hab : a <= b)
    (hfi : IntervalIntegrable f volume a b) :
    (∫ x in a..b, f x) <= (b - a) * f ((a + b) / 2) := by
  let m : Real := (a + b) / 2
  have ham : a <= m := by dsimp [m]; linarith
  have hmb : m <= b := by dsimp [m]; linarith
  have hleft : IntervalIntegrable f volume a m := by
    apply hfi.mono_set
    rw [uIcc_of_le ham, uIcc_of_le hab]
    exact Icc_subset_Icc_right hmb
  have hright : IntervalIntegrable f volume m b := by
    apply hfi.mono_set
    rw [uIcc_of_le hmb, uIcc_of_le hab]
    exact Icc_subset_Icc_left ham
  have hreflected : IntervalIntegrable
      (fun x : Real => f (a + b - x)) volume a m := by
    have h := (hright.comp_sub_left (a + b)).symm
    have hleft : a + b - b = a := by ring
    have hmid : a + b - m = m := by dsimp [m]; ring
    simpa only [hleft, hmid] using h
  have hpair : ∀ x ∈ Icc a m,
      f x + f (a + b - x) <= 2 * f m := by
    intro x hx
    have hy : a + b - x ∈ Icc a b := by
      constructor <;> dsimp [m] at hx ⊢ <;> linarith [hx.1, hx.2]
    have hx' : x ∈ Icc a b :=
      ⟨hx.1, hx.2.trans hmb⟩
    have hconcave := hf.2 hx' hy (show 0 <= (1 / 2 : Real) by norm_num)
      (show 0 <= (1 / 2 : Real) by norm_num)
      (show (1 / 2 : Real) + 1 / 2 = 1 by norm_num)
    have hmidpoint :
        (1 / 2 : Real) * x + (1 / 2 : Real) * (a + b - x) = m := by
      dsimp [m]
      ring
    simp only [smul_eq_mul, hmidpoint] at hconcave
    linarith
  have hpairIntegrable : IntervalIntegrable
      (fun x : Real => f x + f (a + b - x)) volume a m :=
    hleft.add hreflected
  have hconstantIntegrable : IntervalIntegrable
      (fun _ : Real => 2 * f m) volume a m :=
    intervalIntegrable_const
  have hmono :
      (∫ x in a..m, (f x + f (a + b - x))) <=
        ∫ _x in a..m, (2 * f m) :=
    intervalIntegral.integral_mono_on ham hpairIntegrable
      hconstantIntegrable hpair
  have hreflection :
      (∫ x in a..m, f (a + b - x)) = ∫ x in m..b, f x := by
    convert
      (intervalIntegral.integral_comp_sub_left
        (f := f) (a := a) (b := m) (d := a + b)) using 1
    dsimp [m]
    ring
  calc
    (∫ x in a..b, f x) =
        (∫ x in a..m, f x) + ∫ x in m..b, f x :=
      (intervalIntegral.integral_add_adjacent_intervals hleft hright).symm
    _ = ∫ x in a..m, (f x + f (a + b - x)) := by
      rw [intervalIntegral.integral_add hleft hreflected, hreflection]
    _ <= ∫ _x in a..m, (2 * f m) := hmono
    _ = (b - a) * f ((a + b) / 2) := by
      rw [intervalIntegral.integral_const]
      dsimp [m]
      ring

private theorem midpointUniformGridPoint_mem_Icc
    {a b : Real} (hab : a <= b) {N k : Nat}
    (hN : 0 < N) (hk : k <= N) :
    a + (k : Real) * (b - a) / (N : Real) ∈ Icc a b := by
  have hNReal : (0 : Real) < N := by exact_mod_cast hN
  have hkReal : (k : Real) <= N := by exact_mod_cast hk
  have htNonneg : 0 <= (k : Real) / (N : Real) :=
    div_nonneg (Nat.cast_nonneg k) hNReal.le
  have htOne : (k : Real) / (N : Real) <= 1 :=
    (div_le_one hNReal).2 hkReal
  rw [show (k : Real) * (b - a) / (N : Real) =
    ((k : Real) / (N : Real)) * (b - a) by ring]
  constructor
  · exact le_add_of_nonneg_right (mul_nonneg htNonneg (sub_nonneg.mpr hab))
  · calc
      a + ((k : Real) / (N : Real)) * (b - a) <=
          a + 1 * (b - a) :=
        by simpa only [add_comm] using
          (add_le_add_left
            (mul_le_mul_of_nonneg_right htOne (sub_nonneg.mpr hab)) a)
      _ = b := by ring

theorem ConcaveOn.intervalIntegral_le_compositeMidpoint
    {f : Real -> Real} {a b : Real}
    (hf : ConcaveOn Real (Icc a b) f)
    (hab : a <= b)
    (hfi : IntervalIntegrable f volume a b)
    {N : Nat} (hN : 0 < N) :
    (∫ x in a..b, f x) <= midpoint_integral f N a b := by
  let step : Real := (b - a) / (N : Real)
  let point (k : Nat) : Real := a + (k : Real) * step
  have hstepNonneg : 0 <= step := by
    exact div_nonneg (sub_nonneg.mpr hab) (Nat.cast_nonneg N)
  have hpoint (k : Nat) (hk : k <= N) : point k ∈ Icc a b := by
    simpa [point, step, mul_div_assoc] using
      (midpointUniformGridPoint_mem_Icc hab hN hk)
  have hcellOrder (k : Nat) : point k <= point (k + 1) := by
    rw [show point (k + 1) = point k + step by
      dsimp [point]
      push_cast
      ring]
    exact le_add_of_nonneg_right hstepNonneg
  have hcellSubset (k : Nat) (hk : k < N) :
      Icc (point k) (point (k + 1)) ⊆ Icc a b := by
    intro x hx
    exact ⟨(hpoint k hk.le).1.trans hx.1,
      hx.2.trans (hpoint (k + 1) (by omega)).2⟩
  have hcellIntegrable (k : Nat) (hk : k < N) :
      IntervalIntegrable f volume (point k) (point (k + 1)) := by
    apply hfi.mono_set
    rw [uIcc_of_le (hcellOrder k), uIcc_of_le hab]
    exact hcellSubset k hk
  have hcellBound (k : Nat) (hk : k < N) :
      (∫ x in point k..point (k + 1), f x) <=
        step * f (a + ((k : Real) + 1 / 2) * step) := by
    have hbound := intervalIntegral_le_midpoint_one_of_concaveOn
      (hf.subset (hcellSubset k hk) (convex_Icc _ _))
      (hcellOrder k) (hcellIntegrable k hk)
    convert hbound using 1
    dsimp [point]
    push_cast
    ring
  have hendpoint : point N = b := by
    dsimp [point, step]
    have hNne : (N : Real) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
    ring
  have hsumIntegral :
      (∑ k ∈ Finset.range N, ∫ x in point k..point (k + 1), f x) =
        ∫ x in point 0..point N, f x :=
    intervalIntegral.sum_integral_adjacent_intervals
      (fun k hk => hcellIntegrable k hk)
  calc
    (∫ x in a..b, f x) =
        ∑ k ∈ Finset.range N, ∫ x in point k..point (k + 1), f x := by
      rw [hsumIntegral]
      simp [point, hendpoint]
    _ <= ∑ k ∈ Finset.range N,
        step * f (a + ((k : Real) + 1 / 2) * step) := by
      exact Finset.sum_le_sum fun k hk => hcellBound k (Finset.mem_range.mp hk)
    _ = midpoint_integral f N a b := by
      rw [← Finset.mul_sum]
      simp only [midpoint_integral, step, mul_div_assoc]

private theorem midpoint_integral_mono_on
    {f g : Real -> Real} {a b : Real} {N : Nat}
    (hab : a <= b) (hN : 0 < N)
    (hfg : ∀ x ∈ Icc a b, f x <= g x) :
    midpoint_integral f N a b <= midpoint_integral g N a b := by
  unfold midpoint_integral
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k hk => ?_)
    (div_nonneg (sub_nonneg.mpr hab) (Nat.cast_nonneg N))
  apply hfg
  have hklt : k < N := Finset.mem_range.mp hk
  have hNReal : (0 : Real) < N := by exact_mod_cast hN
  have hkSuccReal : (k : Real) + 1 <= N := by
    exact_mod_cast (Nat.succ_le_iff.mpr hklt)
  have htNonneg : 0 <= ((k : Real) + 1 / 2) / (N : Real) := by
    positivity
  have htOne : ((k : Real) + 1 / 2) / (N : Real) <= 1 :=
    (div_le_one hNReal).2 (by linarith [hkSuccReal])
  rw [show ((k : Real) + 1 / 2) * (b - a) / (N : Real) =
    (((k : Real) + 1 / 2) / (N : Real)) * (b - a) by ring]
  constructor
  · exact le_add_of_nonneg_right (mul_nonneg htNonneg (sub_nonneg.mpr hab))
  · calc
      a + (((k : Real) + 1 / 2) / (N : Real)) * (b - a) <=
          a + 1 * (b - a) :=
        by simpa only [add_comm] using
          (add_le_add_left
            (mul_le_mul_of_nonneg_right htOne (sub_nonneg.mpr hab)) a)
      _ = b := by ring

theorem
    iteratedIntervalIntegral_le_tensorCompositeMidpoint_of_separatelyConcaveOn
    {f : Real -> Real -> Real} {a b c d : Real} {Nx Ny : Nat}
    (hab : a <= b) (hcd : c <= d)
    (hNx : 0 < Nx) (hNy : 0 < Ny)
    (hconcX : ∀ y ∈ Icc c d,
      ConcaveOn Real (Icc a b) (fun x => f x y))
    (hconcY : ∀ x ∈ Icc a b,
      ConcaveOn Real (Icc c d) (f x))
    (hfiber : ∀ x ∈ Icc a b,
      IntervalIntegrable (f x) volume c d)
    (hnested : IntervalIntegrable
      (fun x => ∫ y in c..d, f x y) volume a b) :
    (∫ x in a..b, ∫ y in c..d, f x y) <=
      midpoint_integral
        (fun x => midpoint_integral (f x) Ny c d) Nx a b := by
  have hconcNested : ConcaveOn Real (Icc a b)
      (fun x => ∫ y in c..d, f x y) := by
    have hset : ConcaveOn Real (Icc a b)
        (fun x => ∫ y in Ioc c d, f x y) := by
      apply MeasureTheory.integral_concaveOn_of_integrand_ae (convex_Icc a b)
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
        exact hconcX y (Ioc_subset_Icc_self hy)
      · intro x hx
        exact (hfiber x hx).1
    simpa only [intervalIntegral.integral_of_le hcd] using hset
  calc
    (∫ x in a..b, ∫ y in c..d, f x y) <=
        midpoint_integral (fun x => ∫ y in c..d, f x y) Nx a b :=
      ConcaveOn.intervalIntegral_le_compositeMidpoint
        hconcNested hab hnested hNx
    _ <= midpoint_integral
        (fun x => midpoint_integral (f x) Ny c d) Nx a b := by
      apply midpoint_integral_mono_on hab hNx
      intro x hx
      exact ConcaveOn.intervalIntegral_le_compositeMidpoint
        (hconcY x hx) hcd (hfiber x hx) hNy

theorem
    iteratedIntervalIntegral_le_tensorTrapezoidalCompositeMidpoint_of_convexOn_concaveOn
    {f : Real -> Real -> Real} {a b c d : Real} {Nx Ny : Nat}
    (hab : a <= b) (hcd : c <= d)
    (hNx : 0 < Nx) (hNy : 0 < Ny)
    (hconvX : ∀ y ∈ Icc c d,
      ConvexOn Real (Icc a b) (fun x => f x y))
    (hconcY : ∀ x ∈ Icc a b,
      ConcaveOn Real (Icc c d) (f x))
    (hfiber : ∀ x ∈ Icc a b,
      IntervalIntegrable (f x) volume c d)
    (hnested : IntervalIntegrable
      (fun x => ∫ y in c..d, f x y) volume a b) :
    (∫ x in a..b, ∫ y in c..d, f x y) <=
      trapezoidal_integral
        (fun x => midpoint_integral (f x) Ny c d) Nx a b := by
  have hconvNested : ConvexOn Real (Icc a b)
      (fun x => ∫ y in c..d, f x y) := by
    have hset : ConvexOn Real (Icc a b)
        (fun x => ∫ y in Ioc c d, f x y) := by
      apply MeasureTheory.integral_convexOn_of_integrand_ae (convex_Icc a b)
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
        exact hconvX y (Ioc_subset_Icc_self hy)
      · intro x hx
        exact (hfiber x hx).1
    simpa only [intervalIntegral.integral_of_le hcd] using hset
  have hinner : ∀ x ∈ Icc a b,
      (∫ y in c..d, f x y) <= midpoint_integral (f x) Ny c d := by
    intro x hx
    exact ConcaveOn.intervalIntegral_le_compositeMidpoint
      (hconcY x hx) hcd (hfiber x hx) hNy
  calc
    (∫ x in a..b, ∫ y in c..d, f x y) <=
        trapezoidal_integral
          (fun x => ∫ y in c..d, f x y) Nx a b :=
      ConvexOn.intervalIntegral_le_trapezoidalIntegral
        hconvNested hab hnested hNx
    _ <= trapezoidal_integral
        (fun x => midpoint_integral (f x) Ny c d) Nx a b := by
      unfold trapezoidal_integral
      refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_)
        (div_nonneg (sub_nonneg.mpr hab) (Nat.cast_nonneg Nx))
      · gcongr
        · exact hinner a ⟨le_rfl, hab⟩
        · exact hinner b ⟨hab, le_rfl⟩
      · apply Finset.sum_le_sum
        intro k hk
        apply hinner
        have hklt : k < Nx - 1 := Finset.mem_range.mp hk
        simpa only [Nat.cast_add, Nat.cast_one] using
          (midpointUniformGridPoint_mem_Icc hab hNx (k := k + 1) (by omega))

end

end PrimesRestrictedDigits
