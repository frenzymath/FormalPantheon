import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import BoundedGaps.BombieriVinogradov.Statement

/-!
# Prime-counting PNT sequence bridge

This module converts the standard real-variable asymptotic
`pi(floor x) ~ x / log x` to the exact natural-sequence PNT contract consumed
by the concrete Maynard limits. The analytic asymptotic remains an explicit
hypothesis; see SEM-408.
-/

noncomputable section

namespace BoundedGaps.Maynard

open Filter
open scoped Asymptotics

/-- The real-variable prime-counting asymptotic implies the cumulative
natural-endpoint PNT normalization used by SEM-402--SEM-407. -/
theorem tendsto_primeCountTotal_mul_log_div_of_isEquivalent
    (hpi : (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ)) ~[atTop]
      (fun x => x / Real.log x)) :
    Tendsto
      (fun n : ℕ =>
        (primeCountTotal n : ℝ) * Real.log (n : ℝ) / (n : ℝ))
      atTop (nhds 1) := by
  have hpiNat :
      (fun n : ℕ => (primeCountTotal n : ℝ)) ~[atTop]
        (fun n : ℕ => (n : ℝ) / Real.log (n : ℝ)) := by
    simpa [primeCountTotal, Function.comp_def, Nat.floor_natCast] using
      hpi.comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨φ, hφ, hEq⟩ := hpiNat.exists_eq_mul
  have htarget :
      (fun n : ℕ =>
        (primeCountTotal n : ℝ) * Real.log (n : ℝ) / (n : ℝ)) =ᶠ[atTop] φ := by
    filter_upwards [hEq, eventually_ge_atTop 2] with n hn hN
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast (show n ≠ 0 by omega)
    have hlog0 : Real.log (n : ℝ) ≠ 0 := by
      exact ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < n by omega)))
    rw [hn]
    simp only [Pi.mul_apply]
    field_simp [hn0, hlog0]
  exact hφ.congr' htarget.symm

end BoundedGaps.Maynard
