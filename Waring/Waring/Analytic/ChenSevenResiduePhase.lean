import Waring.Analytic.ChenSevenMonotoneQuadrature
import Waring.Analytic.ChenSevenResidueIntegral

/-!
# Fifth-power phase input for Chen's monotone quadrature

This file verifies the derivative hypotheses of the generic right-endpoint
quadrature theorem for the affine residue phase `2*pi*z*(q*s+r)^5`.
-/

namespace Waring.Analytic

open Set

/-- The discrete perturbation phase agrees with the affine progression phase
at every natural parameter. -/
theorem fifthPerturbationPhase_progression
    (q r k : Nat) (z : Real) :
    fifthPerturbationPhase z (r + q * k) 0 =
      residueAffinePhase q z r k := by
  unfold fifthPerturbationPhase residueAffinePhase
  push_cast
  ring

/-- Derivative of the fifth-power phase along a residue progression. -/
theorem hasDerivAt_residueAffinePhase
    (q : Nat) (z : Real) (r : Nat) (x : Real) :
    HasDerivAt (residueAffinePhase q z r)
      (10 * Real.pi * z * q * ((q : Real) * x + r) ^ 4) x := by
  have hinner :
      HasDerivAt (fun s : Real => (q : Real) * s + r) q x := by
    simpa using
      ((hasDerivAt_id x).const_mul (q : Real)).const_add (r : Real)
  have hmul := (hinner.pow 5).const_mul (2 * Real.pi * z)
  have hmul' :
      HasDerivAt
        (fun s : Real => 2 * Real.pi * z * ((q : Real) * s + r) ^ 5)
        (2 * Real.pi * z * (5 * ((q : Real) * x + r) ^ 4 * q)) x := by
    simpa only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub] using hmul
  apply hmul'.congr_deriv
  ring

/-- The derivative of the affine fifth-power residue phase. -/
@[simp]
theorem deriv_residueAffinePhase
    (q : Nat) (z : Real) (r : Nat) (x : Real) :
    deriv (residueAffinePhase q z r) x =
      10 * Real.pi * z * q * ((q : Real) * x + r) ^ 4 :=
  (hasDerivAt_residueAffinePhase q z r x).deriv

/-- The affine fifth-power phase is continuously differentiable. -/
theorem contDiff_residueAffinePhase
    (q : Nat) (z : Real) (r : Nat) :
    ContDiff Real 1 (residueAffinePhase q z r) := by
  unfold residueAffinePhase
  fun_prop

/-- For a nonnegative coefficient, the phase derivative is monotone on the
nonnegative progression parameter. -/
theorem monotoneOn_deriv_residueAffinePhase
    (q : Nat) (z : Real) (r : Nat) (hz : 0 ≤ z) :
    MonotoneOn (deriv (residueAffinePhase q z r)) (Ici 0) := by
  intro x hx y _hy hxy
  rw [deriv_residueAffinePhase, deriv_residueAffinePhase]
  have hq0 : (0 : Real) ≤ q := by positivity
  have hbaseX : 0 ≤ (q : Real) * x + r :=
    add_nonneg (mul_nonneg hq0 hx) (Nat.cast_nonneg r)
  have hbase :
      (q : Real) * x + r ≤ (q : Real) * y + r := by
    gcongr
  have hpow := pow_le_pow_left₀ hbaseX hbase 4
  gcongr

/-- A positive coefficient and positive representative make the phase
derivative strictly positive on the nonnegative parameter ray. -/
theorem deriv_residueAffinePhase_pos
    (q : Nat) [NeZero q] (z : Real) (r : Nat)
    (hz : 0 < z) (hr : 0 < r) :
    ∀ x ∈ Ici (0 : Real),
      0 < deriv (residueAffinePhase q z r) x := by
  intro x hx
  rw [deriv_residueAffinePhase]
  have hq : (0 : Real) < q := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hrReal : (0 : Real) < r := by exact_mod_cast hr
  have hbase : 0 < (q : Real) * x + r :=
    add_pos_of_nonneg_of_pos (mul_nonneg hq.le hx) hrReal
  positivity

/-- Under Chen's Diophantine hypothesis, the phase derivative is at most
`pi` as long as the corresponding physical point does not exceed `P`. -/
theorem deriv_residueAffinePhase_le_pi
    (q : Nat) [NeZero q] (z : Real) (P r : Nat) (x : Real)
    (hz0 : 0 ≤ z) (hP : 0 < P) (hx : 0 ≤ x)
    (hphysical : (q : Real) * x + r ≤ P)
    (hz : z ≤ 1 / (10 * (q : Real) * (P : Real) ^ 4)) :
    deriv (residueAffinePhase q z r) x ≤ Real.pi := by
  rw [deriv_residueAffinePhase]
  have hq : (0 : Real) < q := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hPReal : (0 : Real) < P := by exact_mod_cast hP
  have hbase0 : 0 ≤ (q : Real) * x + r :=
    add_nonneg (mul_nonneg hq.le hx) (Nat.cast_nonneg r)
  have hpow :
      ((q : Real) * x + r) ^ 4 ≤ (P : Real) ^ 4 :=
    pow_le_pow_left₀ hbase0 hphysical 4
  have hden : 0 < 10 * (q : Real) * (P : Real) ^ 4 := by positivity
  have hzden : z * (10 * (q : Real) * (P : Real) ^ 4) ≤ 1 :=
    (le_div_iff₀ hden).mp (by simpa only [one_div] using hz)
  have hscaled :
      10 * z * (q : Real) * ((q : Real) * x + r) ^ 4 ≤ 1 := by
    calc
      _ ≤ 10 * z * (q : Real) * (P : Real) ^ 4 := by gcongr
      _ = z * (10 * (q : Real) * (P : Real) ^ 4) := by ring
      _ ≤ 1 := hzden
  calc
    10 * Real.pi * z * (q : Real) * ((q : Real) * x + r) ^ 4 =
        Real.pi *
          (10 * z * (q : Real) * ((q : Real) * x + r) ^ 4) := by
      ring
    _ ≤ Real.pi * 1 := by gcongr
    _ = Real.pi := mul_one _

end Waring.Analytic
