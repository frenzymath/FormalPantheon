import BoundedGaps.Maynard.ConcreteS2UniformBounds

/-!
# Eventual uniform concrete S2 envelope

This module discharges the endpoint bookkeeping around the fixed-witness,
support-free S2 error bound. It does not assert convergence of the envelope.
-/

namespace BoundedGaps.Maynard

open Filter

noncomputable def engelsmaMaynardS2ExplicitErrorEnvelope
    (alpha A C : ℝ) (N : ℕ) : ℝ :=
  ((engelsmaMaynardRadius alpha N : ℝ) * smallKCandidateBound *
    (1 + Real.log (engelsmaMaynardRadius alpha N)) ^
      (2 * Fintype.card BoundedGaps.engelsmaTuple)) ^ 2 *
    ((∑ h : BoundedGaps.engelsmaTuple,
      (engelsmaMaynardSupportCardLogEnvelope alpha N) ^ 2 *
        (BoundedGaps.engelsmaTuple.card : ℝ) *
        (C * ((2 * N + h.1 - 1 : ℕ) : ℝ) /
          Real.rpow (Real.log ((2 * N + h.1 - 1 : ℕ) : ℝ)) A)) +
    ∑ h : BoundedGaps.engelsmaTuple,
      (engelsmaMaynardSupportCardLogEnvelope alpha N) ^ 2 *
        (BoundedGaps.engelsmaTuple.card : ℝ) *
        (C * ((N + h.1 - 1 : ℕ) : ℝ) /
          Real.rpow (Real.log ((N + h.1 - 1 : ℕ) : ℝ)) A))

set_option maxRecDepth 3000 in
theorem exists_engelsmaMaynardS2Error_uniform_explicit_envelope
    {theta delta A : ℝ} (htheta : 0 ≤ theta) (hdelta : 0 < delta)
    (hlevel : hasPrimeLevel theta) (hA : 0 < A) :
    ∃ C : ℝ, ∃ X₀ : ℕ, PrimeLevelWitness theta A C X₀ ∧
      ∀ᶠ N : ℕ in atTop,
        |engelsmaMaynardS2Error (theta / 2 - delta) N| ≤
          engelsmaMaynardS2ExplicitErrorEnvelope
            (theta / 2 - delta) A C N := by
  obtain ⟨C, X₀, hw⟩ := hasPrimeLevel_exists_witness hlevel hA
  refine ⟨C, X₀, hw, ?_⟩
  filter_upwards [eventually_engelsmaMaynard_coverage,
    eventually_engelsmaMaynardS2_endpoint_thresholds X₀,
    eventually_engelsmaMaynardS2_endpoint_cutoffs htheta hdelta,
    eventually_ge_atTop 1] with N hcoverage hthresholds hcutoffs hN
  unfold engelsmaMaynardS2ExplicitErrorEnvelope
  exact hw.bound_abs_engelsmaMaynardS2Error_explicit N hcoverage
    (by omega)
    (fun h => (hthresholds h).2)
    (fun h => (hthresholds h).1)
    (fun h => (hcutoffs h).2)
    (fun h => (hcutoffs h).1)

end BoundedGaps.Maynard
