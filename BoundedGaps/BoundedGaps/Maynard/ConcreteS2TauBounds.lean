import BoundedGaps.Maynard.ConcreteS2Bounds
import BoundedGaps.Maynard.ImprovedGPY.S2TauShiftedAggregation

noncomputable section

/-!
# Concrete tau-weighted S2 error envelope

This module specializes the source-shaped tau endpoint estimate to the frozen
Engelsma family and the sharp logarithmic coefficient bound.
-/

namespace BoundedGaps.Maynard

open Filter

theorem squarefree_primorial (n : ℕ) : Squarefree (primorial n) := by
  unfold primorial
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    change IsRelPrime p q
    rw [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (Finset.mem_filter.mp hp).2
      (Finset.mem_filter.mp hq).2).mpr hpq
  · intro p hp
    exact (Finset.mem_filter.mp hp).2.prime.squarefree

theorem modulusCutoff_le_self
    {theta : ℝ} {x : ℕ} (hx : 1 ≤ x) (htheta : theta ≤ 1) :
    modulusCutoff theta x ≤ x := by
  have hreal : (modulusCutoff theta x : ℝ) ≤ (x : ℝ) :=
    (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg x) theta)).trans
      (Real.rpow_le_self_of_one_le (by exact_mod_cast hx) htheta)
  exact_mod_cast hreal

noncomputable def engelsmaMaynardSharpCoefficientEnvelope
    (alpha : ℝ) (N : ℕ) : ℝ :=
  smallKCandidateBound *
    (1 + Real.log (engelsmaMaynardRadius alpha N)) ^
      (2 * (Fintype.card BoundedGaps.engelsmaTuple) ^ 2)

noncomputable def engelsmaMaynardS2TauErrorEnvelope
    (alpha A C : ℝ) (N : ℕ) : ℝ :=
  (engelsmaMaynardSharpCoefficientEnvelope alpha N) ^ 2 *
    ((∑ h : BoundedGaps.engelsmaTuple,
      tauIndexedEndpointEnvelope BoundedGaps.engelsmaTuple
        (engelsmaMaynardModulus N * engelsmaMaynardRadius alpha N *
          engelsmaMaynardRadius alpha N) C A (2 * N + h.1 - 1)) +
    ∑ h : BoundedGaps.engelsmaTuple,
      tauIndexedEndpointEnvelope BoundedGaps.engelsmaTuple
        (engelsmaMaynardModulus N * engelsmaMaynardRadius alpha N *
          engelsmaMaynardRadius alpha N) C A (N + h.1 - 1))

set_option maxRecDepth 3000 in
theorem PrimeLevelWitness.bound_abs_engelsmaMaynardS2Error_tau
    {theta alpha A C : ℝ} {X₀ : ℕ}
    (hw : PrimeLevelWitness theta A C X₀) (htheta : theta ≤ 1)
    (N : ℕ)
    (hcoverage : CoversShiftDifferencePrimes BoundedGaps.engelsmaTuple
      (engelsmaMaynardModulus N))
    (hN : 0 < N)
    (hupper : ∀ h : BoundedGaps.engelsmaTuple,
      X₀ ≤ 2 * N + h.1 - 1)
    (hlower : ∀ h : BoundedGaps.engelsmaTuple,
      X₀ ≤ N + h.1 - 1)
    (hcutUpper : ∀ h : BoundedGaps.engelsmaTuple,
      engelsmaMaynardModulus N * engelsmaMaynardRadius alpha N *
          engelsmaMaynardRadius alpha N ≤
        modulusCutoff theta (2 * N + h.1 - 1))
    (hcutLower : ∀ h : BoundedGaps.engelsmaTuple,
      engelsmaMaynardModulus N * engelsmaMaynardRadius alpha N *
          engelsmaMaynardRadius alpha N ≤
        modulusCutoff theta (N + h.1 - 1)) :
    |engelsmaMaynardS2Error alpha N| ≤
      engelsmaMaynardS2TauErrorEnvelope alpha A C N := by
  classical
  let D := maynardSupportFamily BoundedGaps.engelsmaTuple
    (engelsmaMaynardRadius alpha) engelsmaMaynardModulus N
  let lambda := maynardCoefficientFamily BoundedGaps.engelsmaTuple
    (engelsmaMaynardRadius alpha) engelsmaMaynardModulus
    engelsmaSmallKCandidate N
  let L := engelsmaMaynardSharpCoefficientEnvelope alpha N
  have hH : BoundedGaps.engelsmaTuple.Nonempty := by
    apply Finset.card_pos.mp
    rw [BoundedGaps.engelsmaTuple_card]
    norm_num
  have hW : Squarefree (engelsmaMaynardModulus N) := by
    unfold engelsmaMaynardModulus
    exact squarefree_primorial _
  have hD : ∀ d ∈ D,
      IsMaynardDivisorTuple BoundedGaps.engelsmaTuple
        (engelsmaMaynardRadius alpha N) (engelsmaMaynardModulus N) d := by
    intro d hd
    exact engelsmaMaynardS2SupportProof alpha N d (by simpa [D] using hd)
  have hv : ∀ h ∈ BoundedGaps.engelsmaTuple,
      Nat.Coprime (engelsmaPreSieveResidue N + h)
        (engelsmaMaynardModulus N) := by
    intro h hh
    exact engelsmaPreSieveResidue_coprime N hh
  have hL : 0 ≤ L := by
    dsimp [L, engelsmaMaynardSharpCoefficientEnvelope]
    apply mul_nonneg smallKCandidateBound_nonneg
    rw [pow_mul]
    positivity
  have hbound : ∀ d ∈ D, |lambda d| ≤ L := by
    intro d hd
    exact abs_engelsmaMaynardCoefficient_le_sharp_log (alpha := alpha) N
      (by simpa [D, lambda, L, engelsmaMaynardSharpCoefficientEnvelope] using hd)
  have hsizeUpper : ∀ h : BoundedGaps.engelsmaTuple,
      engelsmaMaynardModulus N * engelsmaMaynardRadius alpha N *
          engelsmaMaynardRadius alpha N ≤ (2 * N + h.1 - 1) + 1 := by
    intro h
    have hthreshold := hupper h
    have hX₀ := hw.2.1
    exact (hcutUpper h).trans ((modulusCutoff_le_self
      (show 1 ≤ 2 * N + h.1 - 1 by omega) htheta).trans (Nat.le_succ _))
  have hsizeLower : ∀ h : BoundedGaps.engelsmaTuple,
      engelsmaMaynardModulus N * engelsmaMaynardRadius alpha N *
          engelsmaMaynardRadius alpha N ≤ (N + h.1 - 1) + 1 := by
    intro h
    have hthreshold := hlower h
    have hX₀ := hw.2.1
    exact (hcutLower h).trans ((modulusCutoff_le_self
      (show 1 ≤ N + h.1 - 1 by omega) htheta).trans (Nat.le_succ _))
  have herror := hw.bound_abs_compatiblePairRestrictedErrorOuter_tau
    hH hW hD hcoverage hv lambda L hN hL hbound hupper hlower
      hcutUpper hcutLower hsizeUpper hsizeLower
  simpa [engelsmaMaynardS2Error, engelsmaMaynardS2TauErrorEnvelope,
    D, lambda, L] using herror

theorem exists_engelsmaMaynardS2Error_tau_envelope
    {theta delta A : ℝ} (htheta : 0 ≤ theta) (hthetaHalf : theta < 1 / 2)
    (hdelta : 0 < delta) (hlevel : hasPrimeLevel theta) (hA : 0 < A) :
    ∃ C : ℝ, ∃ X₀ : ℕ, PrimeLevelWitness theta A C X₀ ∧
      ∀ᶠ N : ℕ in atTop,
        |engelsmaMaynardS2Error (theta / 2 - delta) N| ≤
          engelsmaMaynardS2TauErrorEnvelope
            (theta / 2 - delta) A C N := by
  obtain ⟨C, X₀, hw⟩ := hasPrimeLevel_exists_witness hlevel hA
  refine ⟨C, X₀, hw, ?_⟩
  filter_upwards [eventually_engelsmaMaynard_coverage,
    eventually_engelsmaMaynardS2_endpoint_thresholds X₀,
    eventually_engelsmaMaynardS2_endpoint_cutoffs htheta hdelta,
    eventually_ge_atTop 1] with N hcoverage hthresholds hcutoffs hN
  exact hw.bound_abs_engelsmaMaynardS2Error_tau (by linarith) N hcoverage
    (by omega)
    (fun h => (hthresholds h).2)
    (fun h => (hthresholds h).1)
    (fun h => (hcutoffs h).2)
    (fun h => (hcutoffs h).1)

end BoundedGaps.Maynard
