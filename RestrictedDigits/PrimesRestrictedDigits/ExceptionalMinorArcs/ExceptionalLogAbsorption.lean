import PrimesRestrictedDigits.ExceptionalMinorArcs.SplitPrimeSourceArityBound
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Logarithmic absorption for exceptional frequencies

This chooses the raw-major-arc logarithmic exponent and proves the two scalar absorptions left
by the arity-uniform source bound.
-/

open Filter Asymptotics

namespace PrimesRestrictedDigits

noncomputable section

/-- Logarithmic cutoff exponent after accounting for the requested saving and
all losses in the exceptional source estimate. -/
def exceptionalMinorArcLogCutoffExponent
    (A logLoss arity : Nat) : Nat :=
  Nat.ceil
    (((logLoss + 2 * arity + 5 + A + 1 : Nat) : Real) /
      (latticeSumSaving / 10))

theorem exceptionalMinorArcLogCutoffExponent_pos
    (A logLoss arity : Nat) :
    0 < exceptionalMinorArcLogCutoffExponent A logLoss arity := by
  rw [exceptionalMinorArcLogCutoffExponent, Nat.ceil_pos]
  exact div_pos (by positivity) (by positivity [latticeSumSaving_pos])

/-- The ceiling exponent covers the complete contour logarithm budget. -/
theorem exceptionalMinorArcLogCutoffExponent_spec
    (A logLoss arity : Nat) :
    ((logLoss + 2 * arity + 5 + A + 1 : Nat) : Real) ≤
      (exceptionalMinorArcLogCutoffExponent A logLoss arity : Real) *
        (latticeSumSaving / 10) := by
  have htheta : 0 < latticeSumSaving / 10 := by
    positivity [latticeSumSaving_pos]
  have hceil := Nat.le_ceil
    (((logLoss + 2 * arity + 5 + A + 1 : Nat) : Real) /
      (latticeSumSaving / 10))
  have hmul := (div_le_iff₀ htheta).mp hceil
  simpa only [exceptionalMinorArcLogCutoffExponent] using hmul

private theorem eventually_const_mul_log_pow_le_id
    (C : Real) (n : Nat) (hC : 0 ≤ C) :
    ∀ᶠ x : Real in atTop, C * Real.log x ^ n ≤ x := by
  have hbound :=
    ((isLittleO_log_rpow_rpow_atTop (n : Real) (by norm_num : (0 : Real) < 1)).const_mul_left C).bound
      zero_lt_one
  filter_upwards [hbound, eventually_ge_atTop (1 : Real)] with x hx hxOne
  have hleft : 0 ≤ C * Real.log x ^ n :=
    mul_nonneg hC (pow_nonneg (Real.log_nonneg hxOne) n)
  have hxNonneg : 0 ≤ x := zero_le_one.trans hxOne
  simpa only [Real.rpow_natCast, Real.rpow_one,
    Real.norm_of_nonneg hleft, Real.norm_of_nonneg hxNonneg, one_mul] using hx

/-- At all sufficiently large decimal lengths, both explicit terms in the
arity-uniform source estimate save the requested logarithmic power. -/
theorem exists_exceptionalMinorArcLogAbsorptionThreshold
    (A logLoss arity : Nat) (C G : Real)
    (_hC : 0 ≤ C) (_hG : 0 ≤ G) :
    ∃ length0 : Nat, ∀ length : Nat, length0 ≤ length →
      let X : Real := ((10 ^ length : Nat) : Real)
      let D := exceptionalMinorArcLogCutoffExponent A logLoss arity
      1 ≤ Real.log X ∧
        80 * G ^ 2 * Real.log X ^ (2 * arity + 2) / X ≤
          1 / Real.log X ^ A ∧
        960 * C * G ^ 2 *
              Real.log X ^ (logLoss + 2 * arity + 5) /
            (Real.log X ^ D) ^ (latticeSumSaving / 10) ≤
          1 / Real.log X ^ A := by
  let errorCoefficient : Real := 80 * G ^ 2
  let contourCoefficient : Real := 960 * C * G ^ 2
  have herrorCoefficient : 0 ≤ errorCoefficient := by
    dsimp only [errorCoefficient]
    positivity
  have herrorReal := eventually_const_mul_log_pow_le_id errorCoefficient
    (2 * arity + 2 + A) herrorCoefficient
  have hcontourReal :=
    Real.tendsto_log_atTop.eventually_ge_atTop contourCoefficient
  have hlogReal := Real.tendsto_log_atTop.eventually_ge_atTop (1 : Real)
  have hpow :
      Tendsto (fun length : Nat => (10 : Real) ^ length) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hpull := hpow.eventually (herrorReal.and (hcontourReal.and hlogReal))
  have hpull' : ∀ᶠ length : Nat in atTop,
      errorCoefficient *
          Real.log (((10 ^ length : Nat) : Real)) ^
            (2 * arity + 2 + A) ≤
        ((10 ^ length : Nat) : Real) ∧
      contourCoefficient ≤
          Real.log (((10 ^ length : Nat) : Real)) ∧
      1 ≤ Real.log (((10 ^ length : Nat) : Real)) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hpull
  apply eventually_atTop.mp
  filter_upwards [hpull'] with length hlarge
  dsimp only
  let X : Real := ((10 ^ length : Nat) : Real)
  let logX := Real.log X
  let D := exceptionalMinorArcLogCutoffExponent A logLoss arity
  have hXPos : 0 < X := by dsimp only [X]; positivity
  have hlogOne : 1 ≤ logX := by
    simpa only [X, logX] using hlarge.2.2
  have hlogPos : 0 < logX := zero_lt_one.trans_le hlogOne
  have hlogANonneg : 0 ≤ logX ^ A := by positivity
  have hlogAPos : 0 < logX ^ A := pow_pos hlogPos A
  have herror :
      80 * G ^ 2 * logX ^ (2 * arity + 2) / X ≤
        1 / logX ^ A := by
    apply (div_le_div_iff₀ hXPos hlogAPos).2
    have hlargeError :
        errorCoefficient * logX ^ (2 * arity + 2 + A) ≤ X := by
      simpa only [X, logX] using hlarge.1
    calc
      (80 * G ^ 2 * logX ^ (2 * arity + 2)) * logX ^ A =
          errorCoefficient * logX ^ (2 * arity + 2 + A) := by
        rw [pow_add]
        dsimp only [errorCoefficient]
        ring
      _ ≤ X := hlargeError
      _ = 1 * X := by ring
  have hcontourCoefficient : contourCoefficient ≤ logX := by
    simpa only [X, logX] using hlarge.2.1
  have hcoefficientPower :
      contourCoefficient * logX ^ (logLoss + 2 * arity + 5) *
          logX ^ A ≤
        logX ^ (logLoss + 2 * arity + 5 + A + 1) := by
    calc
      contourCoefficient * logX ^ (logLoss + 2 * arity + 5) *
          logX ^ A ≤
          logX * logX ^ (logLoss + 2 * arity + 5) * logX ^ A := by
        gcongr
      _ = (logX ^ (logLoss + 2 * arity + 5) * logX) *
          logX ^ A := by ring
      _ = logX ^ ((logLoss + 2 * arity + 5) + 1) * logX ^ A :=
        congrArg (fun z : Real => z * logX ^ A)
          (pow_succ logX (logLoss + 2 * arity + 5)).symm
      _ = logX ^ ((logLoss + 2 * arity + 5) + 1 + A) :=
        (pow_add logX (logLoss + 2 * arity + 5 + 1) A).symm
      _ = logX ^ (logLoss + 2 * arity + 5 + A + 1) := by
        congr 1
        omega
  have hexponent :
      ((logLoss + 2 * arity + 5 + A + 1 : Nat) : Real) ≤
        (D : Real) * (latticeSumSaving / 10) := by
    simpa only [D] using
      exceptionalMinorArcLogCutoffExponent_spec A logLoss arity
  have hpower :
      logX ^ (logLoss + 2 * arity + 5 + A + 1) ≤
        (logX ^ D) ^ (latticeSumSaving / 10) := by
    calc
      logX ^ (logLoss + 2 * arity + 5 + A + 1) =
          logX ^
            (((logLoss + 2 * arity + 5 + A + 1 : Nat) : Real)) := by
        rw [Real.rpow_natCast]
      _ ≤ logX ^ ((D : Real) * (latticeSumSaving / 10)) :=
        Real.rpow_le_rpow_of_exponent_le hlogOne hexponent
      _ = (logX ^ D) ^ (latticeSumSaving / 10) := by
        exact Real.rpow_natCast_mul (zero_le_one.trans hlogOne) D _
  have hcutoffPos :
      0 < (logX ^ D) ^ (latticeSumSaving / 10) := by
    exact Real.rpow_pos_of_pos (pow_pos hlogPos D) _
  have hcontour :
      960 * C * G ^ 2 *
            logX ^ (logLoss + 2 * arity + 5) /
          (logX ^ D) ^ (latticeSumSaving / 10) ≤
        1 / logX ^ A := by
    apply (div_le_div_iff₀ hcutoffPos hlogAPos).2
    calc
      (960 * C * G ^ 2 *
          logX ^ (logLoss + 2 * arity + 5)) * logX ^ A =
          contourCoefficient *
            logX ^ (logLoss + 2 * arity + 5) * logX ^ A := by
        dsimp only [contourCoefficient]
      _ ≤ logX ^ (logLoss + 2 * arity + 5 + A + 1) :=
        hcoefficientPower
      _ ≤ (logX ^ D) ^ (latticeSumSaving / 10) := hpower
      _ = 1 * (logX ^ D) ^ (latticeSumSaving / 10) := by ring
  exact ⟨hlogOne, herror, hcontour⟩

end

end PrimesRestrictedDigits
