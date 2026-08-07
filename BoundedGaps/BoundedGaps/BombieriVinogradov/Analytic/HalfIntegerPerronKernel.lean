import BoundedGaps.BombieriVinogradov.Analytic.TwoFrequencyPerronKernel

/-!
# The Perron kernel at a positive half-integer cutoff

This file specializes the continuous two-frequency kernel to a positive
integer phase and a positive half-integer cutoff. It proves the logarithmic
separation and the exact and uniform error terms used after equation (6.3).

Source: `AkbaryHambrook2013v2`, Section 6, p. 17, equation (6.3) and the
following display. Semantic review: `SEM-452`.
-/

open MeasureTheory
open scoped Interval

namespace BoundedGaps.Maynard

/-- Positive natural indices below a common real cap have the source's
integer/half-integer logarithmic separation. -/
theorem log_four_div_three_div_le_abs_log_natCast_div_natCast_add_half
    {r k : ℕ} {L : ℝ} (hr : 0 < r) (hk : 0 < k) (hL : 0 < L)
    (hrL : (r : ℝ) ≤ L) (hkL : (k : ℝ) ≤ L) :
    Real.log (4 / 3 : ℝ) / L ≤
      |Real.log ((r : ℝ) / ((k : ℝ) + 1 / 2))| := by
  let y : ℝ := (k : ℝ) + 1 / 2
  have hrR : 0 < (r : ℝ) := by positivity
  have hy : 0 < y := by
    dsimp [y]
    positivity
  have hrone : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hLone : (1 : ℝ) ≤ L := hrone.trans hrL
  have hlog_le : Real.log (4 / 3 : ℝ) ≤ 1 / 3 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 / 3 by norm_num)
    norm_num at h ⊢
    exact h
  have hbase : Real.log (4 / 3 : ℝ) / L ≤ 1 / (2 * L + 1) := by
    calc
      Real.log (4 / 3 : ℝ) / L ≤ (1 / 3 : ℝ) / L :=
        div_le_div_of_nonneg_right hlog_le hL.le
      _ = 1 / (3 * L) := by
        field_simp [hL.ne']
      _ ≤ 1 / (2 * L + 1) :=
        one_div_le_one_div_of_le (by positivity) (by nlinarith)
  apply hbase.trans
  by_cases hrk : r ≤ k
  · have hrkR : (r : ℝ) ≤ (k : ℝ) := by exact_mod_cast hrk
    have hry : (r : ℝ) < y := by
      dsimp [y]
      nlinarith
    have hloglt : Real.log (r : ℝ) < Real.log y :=
      Real.log_lt_log hrR hry
    have hratio : 0 < y / (r : ℝ) := div_pos hy hrR
    have hloglower := Real.one_sub_inv_le_log_of_pos hratio
    rw [Real.log_div hy.ne' hrR.ne'] at hloglower
    have hgap : (1 / 2 : ℝ) ≤ y - (r : ℝ) := by
      dsimp [y]
      nlinarith
    have hyL : y ≤ L + 1 / 2 := by
      dsimp [y]
      nlinarith
    have hone : 1 / (2 * L + 1) ≤ (1 / 2 : ℝ) / y := by
      rw [div_le_div_iff₀ (by positivity) hy]
      nlinarith
    have hinv : 1 - (y / (r : ℝ))⁻¹ = (y - (r : ℝ)) / y := by
      field_simp [hy.ne', hrR.ne']
    rw [hinv] at hloglower
    have hhalf : (1 / 2 : ℝ) / y ≤ (y - (r : ℝ)) / y :=
      div_le_div_of_nonneg_right hgap hy.le
    rw [Real.log_div hrR.ne' hy.ne', abs_of_neg (sub_neg.mpr hloglt)]
    simpa only [neg_sub] using hone.trans (hhalf.trans hloglower)
  · have hkr : k < r := lt_of_not_ge hrk
    have hk1r : k + 1 ≤ r := Nat.succ_le_iff.mpr hkr
    have hk1rR : ((k + 1 : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast hk1r
    have hyr : y < (r : ℝ) := by
      dsimp [y]
      norm_num at hk1rR ⊢
      nlinarith
    have hloglt : Real.log y < Real.log (r : ℝ) :=
      Real.log_lt_log hy hyr
    have hratio : 0 < (r : ℝ) / y := div_pos hrR hy
    have hloglower := Real.one_sub_inv_le_log_of_pos hratio
    rw [Real.log_div hrR.ne' hy.ne'] at hloglower
    have hgap : (1 / 2 : ℝ) ≤ (r : ℝ) - y := by
      dsimp [y]
      norm_num at hk1rR ⊢
      nlinarith
    have hone : 1 / (2 * L + 1) ≤ (1 / 2 : ℝ) / (r : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hrR]
      nlinarith
    have hinv : 1 - ((r : ℝ) / y)⁻¹ = ((r : ℝ) - y) / (r : ℝ) := by
      field_simp [hy.ne', hrR.ne']
    rw [hinv] at hloglower
    have hhalf : (1 / 2 : ℝ) / (r : ℝ) ≤
        ((r : ℝ) - y) / (r : ℝ) :=
      div_le_div_of_nonneg_right hgap hrR.le
    rw [Real.log_div hrR.ne' hy.ne', abs_of_pos (sub_pos.mpr hloglt)]
    exact hone.trans (hhalf.trans hloglower)

/-- The positive half-integer cutoff frequency is at most the source's
`log(2*L)` envelope. -/
theorem log_natCast_add_half_le_log_two_mul
    {k : ℕ} {L : ℝ} (hk : 0 < k) (hL : 0 < L)
    (hkL : (k : ℝ) ≤ L) :
    Real.log ((k : ℝ) + 1 / 2) ≤ Real.log (2 * L) := by
  have hkone : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hLone : (1 : ℝ) ≤ L := hkone.trans hkL
  apply Real.log_le_log (by positivity)
  nlinarith

/-- Exact equation-(6.3) specialization. The source's strict real-frequency
step is the inclusive natural cutoff `r <= k`. -/
theorem norm_integral_log_natCast_halfIntegerPerron_sub_step_le_exact
    {r k : ℕ} {T : ℝ} (hr : 0 < r) (hk : 0 < k) (hT : 0 < T) :
    ‖(∫ t in -T..T,
        symmetricPerronIntegrand (Real.log (r : ℝ))
          (Real.log ((k : ℝ) + 1 / 2)) t) -
      (if r ≤ k then (Real.pi : ℂ) else 0)‖ ≤
      2 / (T * |Real.log ((r : ℝ) / ((k : ℝ) + 1 / 2))|) := by
  let y : ℝ := (k : ℝ) + 1 / 2
  have hrR : 0 < (r : ℝ) := by positivity
  have hy : 0 < y := by
    dsimp [y]
    positivity
  have hkone : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hyone : 1 < y := by
    dsimp [y]
    nlinarith
  have halpha : 0 ≤ Real.log (r : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast hr
  have hbeta : 0 < Real.log y := Real.log_pos hyone
  have hcutoff : (r : ℝ) < y ↔ r ≤ k := by
    constructor
    · intro hry
      by_contra hrk
      have hk1r : k + 1 ≤ r := Nat.succ_le_iff.mpr (lt_of_not_ge hrk)
      have hk1rR : ((k + 1 : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast hk1r
      dsimp [y] at hry
      norm_num at hk1rR
      nlinarith
    · intro hrk
      have hrkR : (r : ℝ) ≤ (k : ℝ) := by exact_mod_cast hrk
      dsimp [y]
      nlinarith
  have hlogcutoff : Real.log (r : ℝ) < Real.log y ↔ r ≤ k :=
    (Real.log_lt_log_iff hrR hy).trans hcutoff
  have hry_ne : (r : ℝ) ≠ y := by
    by_cases hrk : r ≤ k
    · exact ne_of_lt (hcutoff.mpr hrk)
    · have hk1r : k + 1 ≤ r := Nat.succ_le_iff.mpr (lt_of_not_ge hrk)
      have hk1rR : ((k + 1 : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast hk1r
      dsimp [y]
      norm_num at hk1rR ⊢
      nlinarith
  have hlog_ne : Real.log (r : ℝ) ≠ Real.log y := by
    intro h
    apply hry_ne
    exact Real.log_injOn_pos (Set.mem_Ioi.2 hrR) (Set.mem_Ioi.2 hy) h
  have hkernel := norm_integral_symmetricPerronIntegrand_sub_step_le
    halpha hbeta hT hlog_ne
  rw [← Real.log_div hrR.ne' hy.ne'] at hkernel
  dsimp [y] at hlogcutoff hkernel ⊢
  simpa only [hlogcutoff] using hkernel

/-- Uniform half-integer form of equation (6.3), using the source separation
`log(4/3)/L`. This remains unnormalized by `pi`. -/
theorem norm_integral_log_natCast_halfIntegerPerron_sub_step_le
    {r k : ℕ} {L T : ℝ}
    (hr : 0 < r) (hk : 0 < k) (hL : 0 < L)
    (hrL : (r : ℝ) ≤ L) (hkL : (k : ℝ) ≤ L) (hT : 0 < T) :
    ‖(∫ t in -T..T,
        symmetricPerronIntegrand (Real.log (r : ℝ))
          (Real.log ((k : ℝ) + 1 / 2)) t) -
      (if r ≤ k then (Real.pi : ℂ) else 0)‖ ≤
      2 * L / (T * Real.log (4 / 3 : ℝ)) := by
  have hexact :=
    norm_integral_log_natCast_halfIntegerPerron_sub_step_le_exact hr hk hT
  have hsep := log_four_div_three_div_le_abs_log_natCast_div_natCast_add_half
    hr hk hL hrL hkL
  have hlog : 0 < Real.log (4 / 3 : ℝ) := Real.log_pos (by norm_num)
  have hsmall : 0 < Real.log (4 / 3 : ℝ) / L := div_pos hlog hL
  calc
    ‖(∫ t in -T..T,
        symmetricPerronIntegrand (Real.log (r : ℝ))
          (Real.log ((k : ℝ) + 1 / 2)) t) -
      (if r ≤ k then (Real.pi : ℂ) else 0)‖ ≤
        2 / (T * |Real.log ((r : ℝ) / ((k : ℝ) + 1 / 2))|) := hexact
    _ ≤ 2 / (T * (Real.log (4 / 3 : ℝ) / L)) :=
      div_le_div_of_nonneg_left (by positivity) (mul_pos hT hsmall)
        (mul_le_mul_of_nonneg_left hsep hT.le)
    _ = 2 * L / (T * Real.log (4 / 3 : ℝ)) := by
      field_simp [hT.ne', hlog.ne', hL.ne']

end BoundedGaps.Maynard
