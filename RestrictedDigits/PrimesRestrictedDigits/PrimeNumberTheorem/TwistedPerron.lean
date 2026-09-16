import PrimesRestrictedDigits.PrimeNumberTheorem.PerronVonMangoldt
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Perron's formula for Dirichlet twists of von Mangoldt

This specializes the generic countable Perron theorem to the coefficients
`chi(n) * Lambda(n)`. On the half-plane of absolute convergence, their
L-series is the negative logarithmic derivative of the Dirichlet L-function.

Source architecture: `MONTGOMERY-VAUGHAN-MNT-I`, Theorem 5.2 and
Corollary 5.3, pp. 139--140, and the proof of Theorem 11.16, pp. 377--379.
The explicit half-weight endpoint is the project's correction of the
source's starred-to-weak-sum transition.
-/

open Complex MeasureTheory
open scoped Interval

namespace PrimesRestrictedDigits

open Finset

/-- The weak floor-indexed twisted von Mangoldt sum. -/
noncomputable def dirichletVonMangoldtSum
    {q : Nat} (chi : DirichletCharacter Complex q) (x : Real) : Complex :=
  ∑ n ∈ Ioc 0 ⌊x⌋₊,
    chi n * (ArithmeticFunction.vonMangoldt n : Complex)

/-- The half coefficient at an integral cutoff in the twisted Perron sum. -/
noncomputable def dirichletVonMangoldtPerronEndpoint
    {q : Nat} (chi : DirichletCharacter Complex q) (x : Real) : Complex :=
  if ((⌊x⌋₊ : Nat) : Real) = x then
    chi ⌊x⌋₊ * (ArithmeticFunction.vonMangoldt ⌊x⌋₊ : Complex) / 2
  else 0

/-- The starred Perron sum is the weak twisted sum minus its explicit
half-weight endpoint. -/
theorem starredPerronSum_twist_vonMangoldt_eq_sum_sub_endpoint
    {q : Nat} (chi : DirichletCharacter Complex q)
    {x : Real} (hx : 0 < x) :
    starredPerronSum
        (fun n => chi n *
          (ArithmeticFunction.vonMangoldt n : Complex)) x =
      dirichletVonMangoldtSum chi x -
        dirichletVonMangoldtPerronEndpoint chi x := by
  rw [starredPerronSum_eq_sum_Ioc_sub_endpoint _ hx]
  rfl

/-- The vertical Perron integral of the negative logarithmic derivative of a
Dirichlet L-function. -/
noncomputable def dirichletPerronIntegral
    {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
    (x sigma T : Real) : Complex :=
  ((1 / (2 * Real.pi) : Real) : Complex) *
    ∫ t in -T..T,
      (-logDeriv (DirichletCharacter.LFunction chi)
          ((sigma : Complex) + Complex.I * t)) *
        (x : Complex) ^ ((sigma : Complex) + Complex.I * t) /
          ((sigma : Complex) + Complex.I * t)

/-- On `Re s > 1`, the twisted von Mangoldt L-series Perron integral is the
Dirichlet logarithmic-derivative integral. -/
theorem truncatedPerronIntegral_twist_vonMangoldt_eq_dirichletPerronIntegral
    {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
    {x sigma T : Real} (hsigma : 1 < sigma) :
    truncatedPerronIntegral
        (fun n => chi n *
          (ArithmeticFunction.vonMangoldt n : Complex))
        x sigma T =
      dirichletPerronIntegral chi x sigma T := by
  rw [truncatedPerronIntegral, dirichletPerronIntegral]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have hline :
      1 < (((sigma : Complex) + Complex.I * t).re) := by
    simpa using hsigma
  change LSeries
      (fun n => chi n * (ArithmeticFunction.vonMangoldt n : Complex))
        ((sigma : Complex) + Complex.I * t) *
          (x : Complex) ^ ((sigma : Complex) + Complex.I * t) /
            ((sigma : Complex) + Complex.I * t) =
      (-logDeriv (DirichletCharacter.LFunction chi)
        ((sigma : Complex) + Complex.I * t)) *
          (x : Complex) ^ ((sigma : Complex) + Complex.I * t) /
            ((sigma : Complex) + Complex.I * t)
  have hseries :
      LSeries
          (fun n => chi n *
            (ArithmeticFunction.vonMangoldt n : Complex))
          ((sigma : Complex) + Complex.I * t) =
        -deriv (DirichletCharacter.LFunction chi)
            ((sigma : Complex) + Complex.I * t) /
          DirichletCharacter.LFunction chi
            ((sigma : Complex) + Complex.I * t) := by
    calc
      LSeries
          (fun n => chi n *
            (ArithmeticFunction.vonMangoldt n : Complex))
          ((sigma : Complex) + Complex.I * t) =
        LSeries
          ((fun n : Nat => chi n) *
            fun n => (ArithmeticFunction.vonMangoldt n : Complex))
          ((sigma : Complex) + Complex.I * t) := by
        apply LSeries_congr
        intro n hn
        rfl
      _ = -deriv (LSeries fun n : Nat => chi n)
            ((sigma : Complex) + Complex.I * t) /
          LSeries (fun n : Nat => chi n)
            ((sigma : Complex) + Complex.I * t) :=
        DirichletCharacter.LSeries_twist_vonMangoldt_eq chi hline
      _ = -deriv (DirichletCharacter.LFunction chi)
            ((sigma : Complex) + Complex.I * t) /
          DirichletCharacter.LFunction chi
            ((sigma : Complex) + Complex.I * t) := by
        rw [DirichletCharacter.deriv_LFunction_eq_deriv_LSeries chi hline,
          DirichletCharacter.LFunction_eq_LSeries chi hline]
  rw [hseries]
  rw [logDeriv_apply]
  ring

/-- The generic countable Perron theorem gives the corrected twisted sum with
its half-weight endpoint kept inside the left-hand side. -/
theorem norm_dirichletVonMangoldtSum_sub_endpoint_sub_integral_le
    {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
    {x sigma T : Real} (hx : 0 < x) (hsigma : 1 < sigma)
    (hsigma2 : sigma <= 2) (hT : 0 < T) :
    ‖(dirichletVonMangoldtSum chi x -
          dirichletVonMangoldtPerronEndpoint chi x) -
        dirichletPerronIntegral chi x sigma T‖ <=
      16 * (perronNearErrorSum
          (fun n => chi n *
            (ArithmeticFunction.vonMangoldt n : Complex)) x T +
        ((4 : Real) ^ sigma + x ^ sigma) / T *
          perronCoefficientMass
            (fun n => chi n *
              (ArithmeticFunction.vonMangoldt n : Complex)) sigma) := by
  rw [← truncatedPerronIntegral_twist_vonMangoldt_eq_dirichletPerronIntegral
      chi hsigma,
    ← starredPerronSum_twist_vonMangoldt_eq_sum_sub_endpoint chi hx]
  apply norm_starredPerronSum_sub_truncatedPerronIntegral_le
  · change LSeriesSummable
      ((fun n : Nat => chi n) *
        fun n => (ArithmeticFunction.vonMangoldt n : Complex))
      (sigma : Complex)
    exact DirichletCharacter.LSeriesSummable_twist_vonMangoldt chi
      (show 1 < ((sigma : Real) : Complex).re by simpa using hsigma)
  · exact hx
  · linarith
  · exact hsigma2
  · exact hT

/-- Weak-sum form of the twisted Perron estimate. The endpoint remains a
separate norm because it is generally complex. -/
theorem norm_dirichletVonMangoldtSum_sub_integral_le
    {q : Nat} [NeZero q] (chi : DirichletCharacter Complex q)
    {x sigma T : Real} (hx : 0 < x) (hsigma : 1 < sigma)
    (hsigma2 : sigma <= 2) (hT : 0 < T) :
    ‖dirichletVonMangoldtSum chi x -
        dirichletPerronIntegral chi x sigma T‖ <=
      16 * (perronNearErrorSum
          (fun n => chi n *
            (ArithmeticFunction.vonMangoldt n : Complex)) x T +
        ((4 : Real) ^ sigma + x ^ sigma) / T *
          perronCoefficientMass
            (fun n => chi n *
              (ArithmeticFunction.vonMangoldt n : Complex)) sigma) +
        ‖dirichletVonMangoldtPerronEndpoint chi x‖ := by
  have hmain :=
    norm_dirichletVonMangoldtSum_sub_endpoint_sub_integral_le
      chi hx hsigma hsigma2 hT
  calc
    ‖dirichletVonMangoldtSum chi x -
        dirichletPerronIntegral chi x sigma T‖ =
      ‖((dirichletVonMangoldtSum chi x -
          dirichletVonMangoldtPerronEndpoint chi x) -
            dirichletPerronIntegral chi x sigma T) +
        dirichletVonMangoldtPerronEndpoint chi x‖ := by ring_nf
    _ <= ‖(dirichletVonMangoldtSum chi x -
          dirichletVonMangoldtPerronEndpoint chi x) -
            dirichletPerronIntegral chi x sigma T‖ +
        ‖dirichletVonMangoldtPerronEndpoint chi x‖ := norm_add_le _ _
    _ <= 16 * (perronNearErrorSum
          (fun n => chi n *
            (ArithmeticFunction.vonMangoldt n : Complex)) x T +
        ((4 : Real) ^ sigma + x ^ sigma) / T *
          perronCoefficientMass
            (fun n => chi n *
              (ArithmeticFunction.vonMangoldt n : Complex)) sigma) +
        ‖dirichletVonMangoldtPerronEndpoint chi x‖ :=
      add_le_add hmain le_rfl

end PrimesRestrictedDigits
