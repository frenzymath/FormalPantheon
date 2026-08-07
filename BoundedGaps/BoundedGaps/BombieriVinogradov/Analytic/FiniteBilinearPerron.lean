import BoundedGaps.BombieriVinogradov.Analytic.PerronEnvelope
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# The finite bilinear Perron bridge

This file lifts the half-integer Perron estimate through finite coefficient
sums, factors the logarithmic phases over a positive rectangle, and proves
the fixed-character scalar inequality immediately preceding equation (6.4).
The normalization remains raw: no division by `pi` occurs here.

Source: `AkbaryHambrook2013v2`, Section 6, p. 17, equation (6.3) through the
display before equation (6.4). Semantic review: `SEM-453`.
-/

open MeasureTheory
open scoped Interval BigOperators

namespace BoundedGaps.Maynard

noncomputable section

/-- Finite coefficient summation of the uniform half-integer Perron error.
The natural frequencies need not be distinct. -/
theorem norm_integral_finset_halfIntegerPerron_sub_steps_le
    {ι : Type*} (s : Finset ι) (r : ι → ℕ) (c : ι → ℂ)
    {k : ℕ} {L T : ℝ}
    (hr : ∀ i ∈ s, 0 < r i) (hk : 0 < k) (hL : 0 < L)
    (hrL : ∀ i ∈ s, (r i : ℝ) ≤ L) (hkL : (k : ℝ) ≤ L)
    (hT : 0 < T) :
    ‖(∫ t in -T..T, ∑ i ∈ s,
        c i * symmetricPerronIntegrand (Real.log (r i : ℝ))
          (Real.log ((k : ℝ) + 1 / 2)) t) -
      ∑ i ∈ s, c i * (if r i ≤ k then (Real.pi : ℂ) else 0)‖ ≤
      (2 * L / (T * Real.log (4 / 3 : ℝ))) *
        ∑ i ∈ s, ‖c i‖ := by
  have hint (i : ι) (hi : i ∈ s) :
      IntervalIntegrable
        (fun t : ℝ => c i *
          symmetricPerronIntegrand (Real.log (r i : ℝ))
            (Real.log ((k : ℝ) + 1 / 2)) t) volume (-T) T := by
    apply Continuous.intervalIntegrable
    unfold symmetricPerronIntegrand
    fun_prop
  rw [intervalIntegral.integral_finsetSum hint]
  simp_rw [intervalIntegral.integral_const_mul]
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ i ∈ s,
        (c i * (∫ t in -T..T,
          symmetricPerronIntegrand (Real.log (r i : ℝ))
            (Real.log ((k : ℝ) + 1 / 2)) t) -
          c i * (if r i ≤ k then (Real.pi : ℂ) else 0))‖ ≤
        ∑ i ∈ s,
          ‖c i‖ * (2 * L / (T * Real.log (4 / 3 : ℝ))) := by
      apply norm_sum_le_of_le
      intro i hi
      rw [← mul_sub, norm_mul]
      exact mul_le_mul_of_nonneg_left
        (norm_integral_log_natCast_halfIntegerPerron_sub_step_le
          (hr i hi) hk hL (hrL i hi) hkL hT)
        (norm_nonneg _)
    _ = (2 * L / (T * Real.log (4 / 3 : ℝ))) *
        ∑ i ∈ s, ‖c i‖ := by
      rw [← Finset.sum_mul]
      ring

/-- The explicit real-log phase representing `n^(-it)`. -/
noncomputable def natLogTwist (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (-Complex.I * ((t * Real.log (n : ℝ) : ℝ) : ℂ))

/-- Logarithmic phases factor over positive natural products. -/
theorem natLogTwist_mul {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (t : ℝ) :
    natLogTwist (m * n) t = natLogTwist m t * natLogTwist n t := by
  unfold natLogTwist
  rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity), mul_add]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Every explicit logarithmic phase has norm one. -/
@[simp] theorem norm_natLogTwist (n : ℕ) (t : ℝ) :
    ‖natLogTwist n t‖ = 1 := by
  unfold natLogTwist
  have hphase : -Complex.I * ((t * Real.log (n : ℝ) : ℝ) : ℂ) =
      ((-(t * Real.log (n : ℝ)) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hphase, Complex.norm_exp_ofReal_mul_I]

/-- Fixed-character, factorized, coefficient-summed form of equation (6.3).
The estimate remains unnormalized by `pi`. -/
theorem norm_integral_bilinearPerron_sub_cutoff_le
    (q : ℕ) (χ : DirichletCharacter ℂ q)
    (sm sn : Finset ℕ) (a b : ℕ → ℂ)
    {k : ℕ} {L T : ℝ}
    (hk : 0 < k) (hL : 0 < L) (hkL : (k : ℝ) ≤ L) (hT : 0 < T)
    (hmPos : ∀ m ∈ sm, 0 < m)
    (hnPos : ∀ n ∈ sn, 0 < n)
    (hprod : ∀ m ∈ sm, ∀ n ∈ sn, ((m * n : ℕ) : ℝ) ≤ L) :
    ‖(∫ t in -T..T,
        ((Real.log ((k : ℝ) + 1 / 2) *
          Real.sinc (Real.log ((k : ℝ) + 1 / 2) * t) : ℝ) : ℂ) *
          (∑ m ∈ sm, ∑ n ∈ sn,
            (a m * natLogTwist m t) * (b n * natLogTwist n t) * χ (m * n))) -
      (Real.pi : ℂ) *
        (∑ m ∈ sm, ∑ n ∈ sn.filter (fun n => m * n ≤ k),
          a m * b n * χ (m * n))‖ ≤
      2 * L / (T * Real.log (4 / 3 : ℝ)) *
        (∑ m ∈ sm, ‖a m‖) * (∑ n ∈ sn, ‖b n‖) := by
  classical
  let s := sm ×ˢ sn
  let r : ℕ × ℕ → ℕ := fun x => x.1 * x.2
  let c : ℕ × ℕ → ℂ := fun x => a x.1 * b x.2 * χ (x.1 * x.2)
  have hr : ∀ x ∈ s, 0 < r x := by
    intro x hx
    rw [Finset.mem_product] at hx
    exact Nat.mul_pos (hmPos x.1 hx.1) (hnPos x.2 hx.2)
  have hrL : ∀ x ∈ s, (r x : ℝ) ≤ L := by
    intro x hx
    rw [Finset.mem_product] at hx
    exact hprod x.1 hx.1 x.2 hx.2
  have hagg := norm_integral_finset_halfIntegerPerron_sub_steps_le
    s r c hr hk hL hrL hkL hT
  have hintegrand (t : ℝ) :
      (∑ x ∈ s, c x *
        symmetricPerronIntegrand (Real.log (r x : ℝ))
          (Real.log ((k : ℝ) + 1 / 2)) t) =
        ((Real.log ((k : ℝ) + 1 / 2) *
          Real.sinc (Real.log ((k : ℝ) + 1 / 2) * t) : ℝ) : ℂ) *
          (∑ m ∈ sm, ∑ n ∈ sn,
            (a m * natLogTwist m t) * (b n * natLogTwist n t) * χ (m * n)) := by
    rw [Finset.sum_product]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hmm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hnn
    simp only [c, r, symmetricPerronIntegrand]
    change (a m * b n * χ (m * n)) *
        (natLogTwist (m * n) t *
          ((Real.log ((k : ℝ) + 1 / 2) *
            Real.sinc (Real.log ((k : ℝ) + 1 / 2) * t) : ℝ) : ℂ)) = _
    rw [natLogTwist_mul (hmPos m hmm) (hnPos n hnn)]
    ring
  have hcutoff :
      (∑ x ∈ s, c x * (if r x ≤ k then (Real.pi : ℂ) else 0)) =
        (Real.pi : ℂ) *
          (∑ m ∈ sm, ∑ n ∈ sn.filter (fun n => m * n ≤ k),
            a m * b n * χ (m * n)) := by
    rw [Finset.sum_product, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _hmm
    rw [Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _hnn
    by_cases hmn : m * n ≤ k <;> simp [r, c, hmn]
    ring
  have hcoeff :
      (∑ x ∈ s, ‖c x‖) ≤
        (∑ m ∈ sm, ‖a m‖) * (∑ n ∈ sn, ‖b n‖) := by
    rw [Finset.sum_product, Finset.sum_mul_sum]
    apply Finset.sum_le_sum
    intro m _hmm
    apply Finset.sum_le_sum
    intro n _hnn
    simp only [c, norm_mul]
    calc
      ‖a m‖ * ‖b n‖ * ‖χ (m * n)‖ ≤ ‖a m‖ * ‖b n‖ * 1 :=
        mul_le_mul_of_nonneg_left (χ.norm_le_one _)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = ‖a m‖ * ‖b n‖ := mul_one _
  have herror : 0 ≤ 2 * L / (T * Real.log (4 / 3 : ℝ)) := by positivity
  rw [intervalIntegral.integral_congr (fun t _ => hintegrand t), hcutoff] at hagg
  calc
    ‖(∫ t in -T..T,
        ((Real.log ((k : ℝ) + 1 / 2) *
          Real.sinc (Real.log ((k : ℝ) + 1 / 2) * t) : ℝ) : ℂ) *
          (∑ m ∈ sm, ∑ n ∈ sn,
            (a m * natLogTwist m t) * (b n * natLogTwist n t) * χ (m * n))) -
      (Real.pi : ℂ) *
        (∑ m ∈ sm, ∑ n ∈ sn.filter (fun n => m * n ≤ k),
          a m * b n * χ (m * n))‖ ≤
        2 * L / (T * Real.log (4 / 3 : ℝ)) * ∑ x ∈ s, ‖c x‖ := hagg
    _ ≤ 2 * L / (T * Real.log (4 / 3 : ℝ)) *
        ((∑ m ∈ sm, ‖a m‖) * (∑ n ∈ sn, ‖b n‖)) :=
      mul_le_mul_of_nonneg_left hcoeff herror
    _ = 2 * L / (T * Real.log (4 / 3 : ℝ)) *
        (∑ m ∈ sm, ‖a m‖) * (∑ n ∈ sn, ‖b n‖) := by ring

/-- The fixed-character scalar inequality immediately before equation (6.4).
Its right side is uniform in the positive cutoff `k`. -/
theorem pi_mul_norm_bilinearCutoff_le_integral_perronEnvelope_add
    (q : ℕ) (χ : DirichletCharacter ℂ q)
    (sm sn : Finset ℕ) (a b : ℕ → ℂ)
    {k : ℕ} {L T : ℝ}
    (hk : 0 < k) (hL : 0 < L) (hkL : (k : ℝ) ≤ L) (hT : 0 < T)
    (hmPos : ∀ m ∈ sm, 0 < m)
    (hnPos : ∀ n ∈ sn, 0 < n)
    (hprod : ∀ m ∈ sm, ∀ n ∈ sn, ((m * n : ℕ) : ℝ) ≤ L) :
    Real.pi *
        ‖∑ m ∈ sm, ∑ n ∈ sn.filter (fun n => m * n ≤ k),
          a m * b n * χ (m * n)‖ ≤
      (∫ t in -T..T,
        perronEnvelope (Real.log (2 * L)) t *
          ‖∑ m ∈ sm, ∑ n ∈ sn,
            (a m * natLogTwist m t) * (b n * natLogTwist n t) * χ (m * n)‖) +
      2 * L / (T * Real.log (4 / 3 : ℝ)) *
        (∑ m ∈ sm, ‖a m‖) * (∑ n ∈ sn, ‖b n‖) := by
  classical
  let beta : ℝ := Real.log ((k : ℝ) + 1 / 2)
  let B : ℝ := Real.log (2 * L)
  let rect : ℝ → ℂ := fun t =>
    ∑ m ∈ sm, ∑ n ∈ sn,
      (a m * natLogTwist m t) * (b n * natLogTwist n t) * χ (m * n)
  let cutoff : ℂ :=
    ∑ m ∈ sm, ∑ n ∈ sn.filter (fun n => m * n ≤ k),
      a m * b n * χ (m * n)
  let error : ℝ := 2 * L / (T * Real.log (4 / 3 : ℝ)) *
    (∑ m ∈ sm, ‖a m‖) * (∑ n ∈ sn, ‖b n‖)
  have hbeta : 0 < beta := by
    apply Real.log_pos
    have hkone : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hbetaB : beta ≤ B :=
    log_natCast_add_half_le_log_two_mul hk hL hkL
  have hB : 0 ≤ B := hbeta.le.trans hbetaB
  have hraw :
      ‖(∫ t in -T..T,
          ((beta * Real.sinc (beta * t) : ℝ) : ℂ) * rect t) -
        (Real.pi : ℂ) * cutoff‖ ≤ error := by
    simpa only [beta, rect, cutoff, error] using
      norm_integral_bilinearPerron_sub_cutoff_le
        q χ sm sn a b hk hL hkL hT hmPos hnPos hprod
  have hrect : Continuous rect := by
    dsimp only [rect, natLogTwist]
    fun_prop
  have hbound : IntervalIntegrable
      (fun t => perronEnvelope B t * ‖rect t‖) volume (-T) T :=
    ((continuous_perronEnvelope hB).mul hrect.norm).intervalIntegrable _ _
  have hintegral :
      ‖∫ t in -T..T,
        ((beta * Real.sinc (beta * t) : ℝ) : ℂ) * rect t‖ ≤
        ∫ t in -T..T, perronEnvelope B t * ‖rect t‖ := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by linarith) _ hbound
    filter_upwards with t ht
    have hkernel := abs_mul_sinc_le_perronEnvelope hbeta.le hbetaB t
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul] using
      mul_le_mul_of_nonneg_right hkernel (norm_nonneg (rect t))
  let I : ℂ := ∫ t in -T..T,
    ((beta * Real.sinc (beta * t) : ℝ) : ℂ) * rect t
  have htriangle : ‖(Real.pi : ℂ) * cutoff‖ ≤
      ‖I‖ + ‖I - (Real.pi : ℂ) * cutoff‖ := by
    simpa only [sub_sub_cancel] using
      norm_sub_le I (I - (Real.pi : ℂ) * cutoff)
  calc
    Real.pi * ‖∑ m ∈ sm, ∑ n ∈ sn.filter (fun n => m * n ≤ k),
        a m * b n * χ (m * n)‖ = ‖(Real.pi : ℂ) * cutoff‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    _ ≤ ‖I‖ + ‖I - (Real.pi : ℂ) * cutoff‖ := htriangle
    _ ≤ (∫ t in -T..T, perronEnvelope B t * ‖rect t‖) + error :=
      add_le_add (by simpa only [I] using hintegral)
        (by simpa only [I] using hraw)
    _ = (∫ t in -T..T,
        perronEnvelope (Real.log (2 * L)) t *
          ‖∑ m ∈ sm, ∑ n ∈ sn,
            (a m * natLogTwist m t) * (b n * natLogTwist n t) * χ (m * n)‖) +
        2 * L / (T * Real.log (4 / 3 : ℝ)) *
          (∑ m ∈ sm, ‖a m‖) * (∑ n ∈ sn, ‖b n‖) := by
      rfl

end

end BoundedGaps.Maynard
