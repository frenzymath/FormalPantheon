import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule
/-! # ConvexTrapezoidalUpper -/

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

private theorem intervalIntegral_le_trapezoidal_one_of_convexOn
    {f : Real -> Real} {a b : Real}
    (hf : ConvexOn Real (Icc a b) f)
    (hab : a <= b)
    (hfi : IntervalIntegrable f volume a b) :
    (∫ x in a..b, f x) <= trapezoidal_integral f 1 a b := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  have htransformedIntegrable : IntervalIntegrable
      (fun t : Real => f (a + (b - a) * t)) volume 0 1 := by
    have hshifted : IntervalIntegrable
        (fun x : Real => f (a + x)) volume (a - a) (b - a) :=
      hfi.comp_add_left a
    have hscaled := hshifted.comp_mul_left (c := b - a)
    simpa [hba] using hscaled
  have hchordIntegrable : IntervalIntegrable
      (fun t : Real => (1 - t) * f a + t * f b) volume 0 1 := by
    exact (((continuous_const.sub continuous_id).mul continuous_const).add
      (continuous_id.mul continuous_const)).intervalIntegrable 0 1
  have hpointwise : ∀ t ∈ Icc (0 : Real) 1,
      f (a + (b - a) * t) <= (1 - t) * f a + t * f b := by
    intro t ht
    have hconvex := hf.2
      (show a ∈ Icc a b from ⟨le_rfl, hab.le⟩)
      (show b ∈ Icc a b from ⟨hab.le, le_rfl⟩)
      (sub_nonneg.mpr ht.2) ht.1 (by ring)
    calc
      f (a + (b - a) * t) = f ((1 - t) * a + t * b) := by
        congr 1
        ring
      _ <= (1 - t) * f a + t * f b := by
        simpa only [smul_eq_mul] using hconvex
  have hunit :
      (∫ t in (0 : Real)..1, f (a + (b - a) * t)) <=
        ∫ t in (0 : Real)..1, ((1 - t) * f a + t * f b) :=
    intervalIntegral.integral_mono_on zero_le_one
      htransformedIntegrable hchordIntegrable hpointwise
  have hchord :
      (∫ t in (0 : Real)..1, ((1 - t) * f a + t * f b)) =
        (f a + f b) / 2 := by
    calc
      (∫ t in (0 : Real)..1, ((1 - t) * f a + t * f b)) =
          ∫ t in (0 : Real)..1, (f a + t * (f b - f a)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        ring
      _ = (f a + f b) / 2 := by
        have hid : IntervalIntegrable (fun t : Real => t) volume 0 1 :=
          intervalIntegral.intervalIntegrable_id
        rw [intervalIntegral.integral_add intervalIntegrable_const
          (hid.mul_const (f b - f a)),
          intervalIntegral.integral_const, intervalIntegral.integral_mul_const,
          integral_id]
        norm_num
        ring
  have hchange :
      (b - a) * (∫ t in (0 : Real)..1, f (a + (b - a) * t)) =
        ∫ x in a..b, f x := by
    simp
  calc
    (∫ x in a..b, f x) =
        (b - a) * (∫ t in (0 : Real)..1, f (a + (b - a) * t)) := hchange.symm
    _ <= (b - a) *
        (∫ t in (0 : Real)..1, ((1 - t) * f a + t * f b)) :=
      mul_le_mul_of_nonneg_left hunit (sub_nonneg.mpr hab.le)
    _ = (b - a) / 2 * (f a + f b) := by rw [hchord]; ring
    _ = trapezoidal_integral f 1 a b := (trapezoidal_integral_one f a b).symm

private theorem uniformGridPoint_mem_Icc
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

private theorem trapezoidal_integral_mono_on
    {f g : Real -> Real} {a b : Real} {N : Nat}
    (hab : a <= b) (hN : 0 < N)
    (hfg : ∀ x ∈ Icc a b, f x <= g x) :
    trapezoidal_integral f N a b <= trapezoidal_integral g N a b := by
  unfold trapezoidal_integral
  refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_)
    (div_nonneg (sub_nonneg.mpr hab) (Nat.cast_nonneg N))
  · gcongr
    · exact hfg a ⟨le_rfl, hab⟩
    · exact hfg b ⟨hab, le_rfl⟩
  · apply Finset.sum_le_sum
    intro k hk
    apply hfg
    have hklt : k < N - 1 := Finset.mem_range.mp hk
    simpa only [Nat.cast_add, Nat.cast_one] using
      (uniformGridPoint_mem_Icc hab hN (k := k + 1) (by omega))

theorem ConvexOn.intervalIntegral_le_trapezoidalIntegral
    {f : Real -> Real} {a b : Real}
    (hf : ConvexOn Real (Icc a b) f)
    (hab : a <= b)
    (hfi : IntervalIntegrable f volume a b)
    {N : Nat} (hN : 0 < N) :
    (∫ x in a..b, f x) <= trapezoidal_integral f N a b := by
  let step : Real := (b - a) / (N : Real)
  let point (k : Nat) : Real := a + (k : Real) * step
  have hstepNonneg : 0 <= step := by
    exact div_nonneg (sub_nonneg.mpr hab) (Nat.cast_nonneg N)
  have hpoint (k : Nat) (hk : k <= N) : point k ∈ Icc a b := by
    simpa [point, step, mul_div_assoc] using
      (uniformGridPoint_mem_Icc hab hN hk)
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
        trapezoidal_integral f 1 (point k) (point (k + 1)) :=
    intervalIntegral_le_trapezoidal_one_of_convexOn
      (hf.subset (hcellSubset k hk) (convex_Icc _ _))
      (hcellOrder k) (hcellIntegrable k hk)
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
        trapezoidal_integral f 1 (point k) (point (k + 1)) := by
      exact Finset.sum_le_sum fun k hk => hcellBound k (Finset.mem_range.mp hk)
    _ = trapezoidal_integral f N a (a + (N : Real) * step) := by
      simpa [point] using
        (sum_trapezoidal_integral_adjacent_intervals
          (f := f) (a := a) (h := step) hN)
    _ = trapezoidal_integral f N a b := by
      rw [show a + (N : Real) * step = b by simpa [point] using hendpoint]

theorem
    iteratedIntervalIntegral_le_tensorTrapezoidalIntegral_of_separatelyConvexOn
    {f : Real -> Real -> Real} {a b c d : Real} {Nx Ny : Nat}
    (hab : a <= b) (hcd : c <= d)
    (hNx : 0 < Nx) (hNy : 0 < Ny)
    (hconvX : ∀ y ∈ Icc c d,
      ConvexOn Real (Icc a b) (fun x => f x y))
    (hconvY : ∀ x ∈ Icc a b,
      ConvexOn Real (Icc c d) (f x))
    (hfiber : ∀ x ∈ Icc a b,
      IntervalIntegrable (f x) volume c d)
    (hnested : IntervalIntegrable
      (fun x => ∫ y in c..d, f x y) volume a b) :
    (∫ x in a..b, ∫ y in c..d, f x y) <=
      trapezoidal_integral
        (fun x => trapezoidal_integral (f x) Ny c d) Nx a b := by
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
  calc
    (∫ x in a..b, ∫ y in c..d, f x y) <=
        trapezoidal_integral
          (fun x => ∫ y in c..d, f x y) Nx a b :=
      ConvexOn.intervalIntegral_le_trapezoidalIntegral
        hconvNested hab hnested hNx
    _ <= trapezoidal_integral
        (fun x => trapezoidal_integral (f x) Ny c d) Nx a b := by
      apply trapezoidal_integral_mono_on hab hNx
      intro x hx
      exact ConvexOn.intervalIntegral_le_trapezoidalIntegral
        (hconvY x hx) hcd (hfiber x hx) hNy

end

end PrimesRestrictedDigits
