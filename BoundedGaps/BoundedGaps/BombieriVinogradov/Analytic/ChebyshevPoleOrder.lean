import BoundedGaps.BombieriVinogradov.Analytic.FarRightLogDerivative
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# Explicit Chebyshev pole-order bounds

Abel summation converts a linear upper bound for `Chebyshev.psi` into an
explicit majorant for the positive von Mangoldt Dirichlet series. Combining
Mathlib's bound with SEM-466 gives the corresponding character L-series and
continued L-function estimates.

This is a coarse pole-order bound. It is not Davenport's coefficient-one
principal-zeta estimate on p. 89, which remains a separate zero-free-region
dependency. Source context: `DavenportMNTCh14ZeroFree1980`, pp. 88--89, and
`KoukoulopoulosPNTAP2013`, Lemma 4.3, Case 1. Semantic review: `SEM-467`.
-/

noncomputable section

namespace BoundedGaps.Maynard

open ArithmeticFunction
open Filter Finset Asymptotics MeasureTheory Set

/-- A linear upper bound for `Chebyshev.psi` gives an explicit pole-order
majorant for the positive von Mangoldt Dirichlet series. -/
theorem vonMangoldt_tsum_le_of_psi
    {C sigma : ℝ} (hC : 0 ≤ C) (hsigma : 1 < sigma)
    (hpsi : ∀ x : ℝ, 0 ≤ x → Chebyshev.psi x ≤ C * x) :
    (∑' n : ℕ, vonMangoldt n / (n : ℝ) ^ sigma) ≤
      C * sigma / (sigma - 1) := by
  have hsigma_pos : 0 < sigma := zero_lt_one.trans hsigma
  have hpsi_sum (x : ℝ) :
      (∑ k ∈ Icc 1 ⌊x⌋₊, vonMangoldt k) = Chebyshev.psi x := by
    rw [Chebyshev.psi_eq_sum_Icc,
      ← insert_Icc_add_one_left_eq_Icc (Nat.zero_le ⌊x⌋₊),
      sum_insert (by simp), ArithmeticFunction.map_zero, zero_add]
    norm_num
  have hO :
      (fun n : ℕ => ∑ k ∈ Icc 1 n, vonMangoldt k) =O[atTop]
        fun n => (n : ℝ) ^ (1 : ℝ) := by
    apply isBigO_of_le' (c := ‖C‖) atTop
    intro n
    rw [show (∑ k ∈ Icc 1 n, vonMangoldt k) =
        Chebyshev.psi (n : ℝ) by simpa using hpsi_sum (n : ℝ)]
    simp only [Real.norm_eq_abs, Real.rpow_one, Nat.cast_nonneg,
      abs_of_nonneg, Chebyshev.psi_nonneg, hC]
    exact hpsi _ (Nat.cast_nonneg n)
  have hrepresentation := LSeries_eq_mul_integral_of_nonneg
    (s := (sigma : ℂ)) (fun n => vonMangoldt n) zero_le_one hsigma hO
      (fun _ => vonMangoldt_nonneg)
  have hLSeries_tsum :
      LSeries (fun n => (vonMangoldt n : ℂ)) (sigma : ℂ) =
        (∑' n : ℕ, vonMangoldt n / (n : ℝ) ^ sigma : ℝ) := by
    rw [LSeries, Complex.ofReal_tsum]
    apply tsum_congr
    intro n
    by_cases hn : n = 0
    · subst n
      simp
    · rw [LSeries.term_of_ne_zero hn]
      push_cast
      rw [Complex.ofReal_cpow (Nat.cast_nonneg n) sigma]
      norm_cast
  have hsum_nonneg :
      0 ≤ ∑' n : ℕ, vonMangoldt n / (n : ℝ) ^ sigma :=
    tsum_nonneg fun n => div_nonneg vonMangoldt_nonneg
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hintegral :
      ‖∫ t in Ioi (1 : ℝ),
          (∑ k ∈ Icc 1 ⌊t⌋₊, (vonMangoldt k : ℂ)) *
            (t : ℂ) ^ (-((sigma : ℂ) + 1))‖ ≤
        C / (sigma - 1) := by
    calc
      _ ≤ ∫ t in Ioi (1 : ℝ), C * t ^ (-sigma) := by
        apply norm_integral_le_of_norm_le
        · exact
            (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          have htpos : 0 < t := zero_lt_one.trans ht
          have hpsi_complex :
              (∑ k ∈ Icc 1 ⌊t⌋₊, (vonMangoldt k : ℂ)) =
                (Chebyshev.psi t : ℂ) := by
            exact_mod_cast hpsi_sum t
          rw [hpsi_complex, norm_mul,
            Complex.norm_of_nonneg (Chebyshev.psi_nonneg t),
            Complex.norm_cpow_eq_rpow_re_of_pos htpos]
          change Chebyshev.psi t * t ^ (-(sigma + 1)) ≤
            C * t ^ (-sigma)
          calc
            _ ≤ (C * t) * t ^ (-(sigma + 1)) :=
              mul_le_mul_of_nonneg_right (hpsi t htpos.le)
                (Real.rpow_nonneg htpos.le _)
            _ = C * t ^ (-sigma) := by
              rw [mul_assoc]
              congr 1
              calc
                t * t ^ (-(sigma + 1)) =
                    t ^ (1 : ℝ) * t ^ (-(sigma + 1)) := by
                  rw [Real.rpow_one]
                _ = t ^ ((1 : ℝ) + -(sigma + 1)) :=
                  (Real.rpow_add htpos _ _).symm
                _ = t ^ (-sigma) := by ring_nf
      _ = C / (sigma - 1) := by
        rw [integral_const_mul,
          integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow]
        have hden : -sigma + 1 = -(sigma - 1) := by ring
        rw [hden, neg_div_neg_eq]
        simp only [div_eq_mul_inv, one_mul]
  rw [hLSeries_tsum] at hrepresentation
  rw [← Complex.norm_of_nonneg hsum_nonneg, hrepresentation, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsigma_pos]
  calc
    sigma * ‖∫ t in Ioi (1 : ℝ),
        (∑ k ∈ Icc 1 ⌊t⌋₊, (vonMangoldt k : ℂ)) *
          (t : ℂ) ^ (-((sigma : ℂ) + 1))‖ ≤
        sigma * (C / (sigma - 1)) :=
      mul_le_mul_of_nonneg_left hintegral hsigma_pos.le
    _ = C * sigma / (sigma - 1) := by ring

/-- Explicit specialization using Mathlib's verified Chebyshev constant. -/
theorem vonMangoldt_tsum_le_chebyshev_div_sub_one
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (∑' n : ℕ, vonMangoldt n / (n : ℝ) ^ sigma) ≤
      (Real.log 4 + 4) * sigma / (sigma - 1) :=
  vonMangoldt_tsum_le_of_psi (by positivity) hsigma fun _ hx =>
    Chebyshev.psi_le_const_mul_self hx

/-- Coarse explicit pole-order bound for every naive character L-series. -/
theorem norm_neg_logDeriv_LSeries_le_chebyshev_div_sub_one
    {N : ℕ} (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    ‖-logDeriv (LSeries (fun n : ℕ => χ n)) s‖ ≤
      (Real.log 4 + 4) * s.re / (s.re - 1) :=
  (norm_neg_logDeriv_LSeries_le_vonMangoldt_tsum χ hs).trans
    (vonMangoldt_tsum_le_chebyshev_div_sub_one hs)

/-- Positive-modulus continued-L-function form of the coarse explicit
pole-order bound. -/
theorem norm_neg_logDeriv_LFunction_le_chebyshev_div_sub_one
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    ‖-logDeriv (DirichletCharacter.LFunction χ) s‖ ≤
      (Real.log 4 + 4) * s.re / (s.re - 1) :=
  (norm_neg_logDeriv_LFunction_le_vonMangoldt_tsum χ hs).trans
    (vonMangoldt_tsum_le_chebyshev_div_sub_one hs)

end BoundedGaps.Maynard
