import PrimesRestrictedDigits.PrimeNumberTheorem.PerronSummable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The von Mangoldt Perron endpoint repair

This file corrects the omitted starred endpoint in
`MONTGOMERY-VAUGHAN-MNT-I`, Eq. (6.16), p. 180, and specializes the countable
Perron theorem to the negative logarithmic derivative of the Riemann zeta
function.
-/

open Complex MeasureTheory
open scoped Interval

namespace PrimesRestrictedDigits

open Finset

/-- The half coefficient missing when a starred von Mangoldt sum is replaced
by the weak Chebyshev sum at an integral cutoff. -/
noncomputable def vonMangoldtPerronEndpoint (x : Real) : Real :=
  if ((⌊x⌋₊ : Nat) : Real) = x then
    ArithmeticFunction.vonMangoldt ⌊x⌋₊ / 2
  else 0

/-- The von Mangoldt Perron endpoint is nonnegative. -/
theorem vonMangoldtPerronEndpoint_nonneg (x : Real) :
    0 <= vonMangoldtPerronEndpoint x := by
  rw [vonMangoldtPerronEndpoint]
  split_ifs
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by norm_num)
  · exact le_rfl

/-- Above one, the endpoint correction is at most half the logarithm of the
cutoff. -/
theorem vonMangoldtPerronEndpoint_le_log
    {x : Real} (hx : 1 <= x) :
    vonMangoldtPerronEndpoint x <= Real.log x / 2 := by
  rw [vonMangoldtPerronEndpoint]
  split_ifs with h
  · have hle := ArithmeticFunction.vonMangoldt_le_log (n := ⌊x⌋₊)
    rw [h] at hle
    exact div_le_div_of_nonneg_right hle (by norm_num)
  · exact div_nonneg (Real.log_nonneg hx) (by norm_num)

/-- A positive-cutoff starred sum is the corresponding weak floor-indexed
sum, minus half of an integral endpoint coefficient. -/
theorem starredPerronSum_eq_sum_Ioc_sub_endpoint
    (a : Nat -> Complex) {x : Real} (hx : 0 < x) :
    starredPerronSum a x =
      (∑ n ∈ Ioc 0 ⌊x⌋₊, a n) -
        if (((⌊x⌋₊ : Nat) : Real) = x) then
          a ⌊x⌋₊ / 2
        else 0 := by
  rw [starredPerronSum, tsum_eq_sum (s := Ioc 0 ⌊x⌋₊)]
  · by_cases hfloor : ((⌊x⌋₊ : Nat) : Real) = x
    · rw [if_pos hfloor]
      have hfloor_pos : 0 < ⌊x⌋₊ := by
        exact_mod_cast hfloor.symm ▸ hx
      calc
        (∑ n ∈ Ioc 0 ⌊x⌋₊, perronStarredTerm a x n) =
            ∑ n ∈ Ioc 0 ⌊x⌋₊,
              (a n - if n = ⌊x⌋₊ then a n / 2 else 0) := by
                apply sum_congr rfl
                intro n hn
                have hn_pos : 0 < n := (mem_Ioc.mp hn).1
                by_cases hnfloor : n = ⌊x⌋₊
                · subst n
                  rw [perronStarredTerm, if_neg hfloor_pos.ne',
                    perronWeight_eq_half_of_eq hfloor, if_pos rfl]
                  push_cast
                  ring
                · have hn_lt_floor : n < ⌊x⌋₊ :=
                    lt_of_le_of_ne (mem_Ioc.mp hn).2 hnfloor
                  have hn_lt_x : (n : Real) < x := by
                    rw [← hfloor]
                    exact_mod_cast hn_lt_floor
                  simp [perronStarredTerm, hn_pos.ne', hnfloor,
                    perronWeight_eq_one_of_lt hn_lt_x]
        _ = (∑ n ∈ Ioc 0 ⌊x⌋₊, a n) - a ⌊x⌋₊ / 2 := by
          rw [sum_sub_distrib]
          simp [hfloor_pos]
    · rw [if_neg hfloor]
      simp only [sub_zero]
      have hfloor_lt : ((⌊x⌋₊ : Nat) : Real) < x :=
        lt_of_le_of_ne (Nat.floor_le hx.le) hfloor
      apply sum_congr rfl
      intro n hn
      have hn_pos : 0 < n := (mem_Ioc.mp hn).1
      have hn_lt_x : (n : Real) < x :=
        lt_of_le_of_lt (by exact_mod_cast (mem_Ioc.mp hn).2) hfloor_lt
      simp [perronStarredTerm, hn_pos.ne',
        perronWeight_eq_one_of_lt hn_lt_x]
  · intro n hn
    have hn_zero_or_floor_lt : n = 0 ∨ ⌊x⌋₊ < n := by
      by_cases hnzero : n = 0
      · exact Or.inl hnzero
      · exact Or.inr <| lt_of_not_ge fun hnle =>
          hn (mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hnzero, hnle⟩)
    rcases hn_zero_or_floor_lt with rfl | hfloor_lt_n
    · simp [perronStarredTerm]
    · have hx_lt_n : x < (n : Real) :=
        (Nat.floor_lt hx.le).mp hfloor_lt_n
      simp [perronStarredTerm, perronWeight_eq_zero_of_lt hx_lt_n]

/-- The starred von Mangoldt sum is the weak Chebyshev sum minus the explicit
integral endpoint correction. -/
theorem starredPerronSum_vonMangoldt_eq_psi_sub_endpoint
    {x : Real} (hx : 0 < x) :
    starredPerronSum
        (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) x =
      ((Chebyshev.psi x - vonMangoldtPerronEndpoint x : Real) : Complex) := by
  rw [starredPerronSum_eq_sum_Ioc_sub_endpoint _ hx, Chebyshev.psi,
    vonMangoldtPerronEndpoint]
  push_cast
  by_cases h : ((⌊x⌋₊ : Nat) : Real) = x <;> simp [h]

/-- The vertically parametrized zeta logarithmic-derivative integral in the
proof of Montgomery--Vaughan, Theorem 6.9. -/
noncomputable def zetaPerronIntegral
    (x sigma T : Real) : Complex :=
  ((1 / (2 * Real.pi) : Real) : Complex) *
    ∫ t in -T..T,
      (-logDeriv riemannZeta
          ((sigma : Complex) + Complex.I * t)) *
        (x : Complex) ^ ((sigma : Complex) + Complex.I * t) /
          ((sigma : Complex) + Complex.I * t)

/-- In the half-plane of absolute convergence, the von Mangoldt L-series
Perron integral is the zeta logarithmic-derivative integral. -/
theorem truncatedPerronIntegral_vonMangoldt_eq_zetaPerronIntegral
    {x sigma T : Real} (hsigma : 1 < sigma) :
    truncatedPerronIntegral
        (fun n => (ArithmeticFunction.vonMangoldt n : Complex))
        x sigma T =
      zetaPerronIntegral x sigma T := by
  rw [truncatedPerronIntegral, zetaPerronIntegral]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  have hline : 1 <
      (((sigma : Complex) + Complex.I * t).re) := by
    simpa using hsigma
  change LSeries (fun n =>
      (ArithmeticFunction.vonMangoldt n : Complex))
        ((sigma : Complex) + Complex.I * t) *
          (x : Complex) ^ ((sigma : Complex) + Complex.I * t) /
            ((sigma : Complex) + Complex.I * t) =
      (-logDeriv riemannZeta
        ((sigma : Complex) + Complex.I * t)) *
          (x : Complex) ^ ((sigma : Complex) + Complex.I * t) /
            ((sigma : Complex) + Complex.I * t)
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hline]
  simp only [logDeriv_apply, neg_div]

/-- Corrected form of Eq. (6.16): the zeta Perron integral approximates the
weak Chebyshev sum minus its half-weight endpoint. -/
theorem norm_psi_sub_endpoint_sub_zetaPerronIntegral_le
    {x sigma T : Real} (hx : 0 < x) (hsigma : 1 < sigma)
    (hsigma2 : sigma <= 2) (hT : 0 < T) :
    ‖(((Chebyshev.psi x - vonMangoldtPerronEndpoint x : Real) : Complex) -
        zetaPerronIntegral x sigma T)‖ <=
      16 * (perronNearErrorSum
          (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) x T +
        ((4 : Real) ^ sigma + x ^ sigma) / T *
          perronCoefficientMass
            (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) sigma) := by
  rw [← truncatedPerronIntegral_vonMangoldt_eq_zetaPerronIntegral hsigma,
    ← starredPerronSum_vonMangoldt_eq_psi_sub_endpoint hx]
  apply norm_starredPerronSum_sub_truncatedPerronIntegral_le
  · simpa using ArithmeticFunction.LSeriesSummable_vonMangoldt
      (show 1 < ((sigma : Real) : Complex).re by simpa using hsigma)
  · exact hx
  · linarith
  · exact hsigma2
  · exact hT

/-- Weak-sum form of the corrected Perron estimate, with the omitted endpoint
kept as a separate nonnegative error. -/
theorem norm_psi_sub_zetaPerronIntegral_le
    {x sigma T : Real} (hx : 0 < x) (hsigma : 1 < sigma)
    (hsigma2 : sigma <= 2) (hT : 0 < T) :
    ‖(Chebyshev.psi x : Complex) - zetaPerronIntegral x sigma T‖ <=
      16 * (perronNearErrorSum
          (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) x T +
        ((4 : Real) ^ sigma + x ^ sigma) / T *
          perronCoefficientMass
            (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) sigma) +
        vonMangoldtPerronEndpoint x := by
  have hmain := norm_psi_sub_endpoint_sub_zetaPerronIntegral_le
    hx hsigma hsigma2 hT
  calc
    ‖(Chebyshev.psi x : Complex) - zetaPerronIntegral x sigma T‖ =
        ‖((((Chebyshev.psi x - vonMangoldtPerronEndpoint x : Real) : Complex) -
          zetaPerronIntegral x sigma T) +
            (vonMangoldtPerronEndpoint x : Complex))‖ := by
      push_cast
      ring_nf
    _ <= ‖(((Chebyshev.psi x - vonMangoldtPerronEndpoint x : Real) : Complex) -
          zetaPerronIntegral x sigma T)‖ +
        ‖(vonMangoldtPerronEndpoint x : Complex)‖ := norm_add_le _ _
    _ <= 16 * (perronNearErrorSum
          (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) x T +
        ((4 : Real) ^ sigma + x ^ sigma) / T *
          perronCoefficientMass
            (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) sigma) +
        vonMangoldtPerronEndpoint x := by
      have hendnorm : ‖(vonMangoldtPerronEndpoint x : Complex)‖ =
          vonMangoldtPerronEndpoint x := by
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (vonMangoldtPerronEndpoint_nonneg x)]
      rw [hendnorm]
      exact add_le_add hmain le_rfl

/-- The weak-sum endpoint error may be replaced by `log x / 2` above one. -/
theorem norm_psi_sub_zetaPerronIntegral_le_log
    {x sigma T : Real} (hx : 1 <= x) (hsigma : 1 < sigma)
    (hsigma2 : sigma <= 2) (hT : 0 < T) :
    ‖(Chebyshev.psi x : Complex) - zetaPerronIntegral x sigma T‖ <=
      16 * (perronNearErrorSum
          (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) x T +
        ((4 : Real) ^ sigma + x ^ sigma) / T *
          perronCoefficientMass
            (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) sigma) +
        Real.log x / 2 := by
  exact (norm_psi_sub_zetaPerronIntegral_le
    (zero_lt_one.trans_le hx) hsigma hsigma2 hT).trans
      (add_le_add_right (vonMangoldtPerronEndpoint_le_log hx) _)

end PrimesRestrictedDigits
