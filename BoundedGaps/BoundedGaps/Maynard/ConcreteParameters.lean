import BoundedGaps.Maynard.ImprovedGPY.PreSieve
import BoundedGaps.Maynard.PreSieveGrowth

/-!
# Concrete Maynard parameter families

This module freezes the shifted natural parameter convention used by the
endpoint distribution estimates. It follows Maynard2013v3, Section 4
(source lines 193--216), with `N - 1` used for the cutoff base so both
cumulative endpoints share one supported-modulus bound.
-/

namespace BoundedGaps.Maynard

open Filter

noncomputable def engelsmaMaynardModulus (N : ℕ) : ℕ :=
  primorial (tripleLogCutoff (N - 1))

noncomputable def engelsmaMaynardRadius (alpha : ℝ) (N : ℕ) : ℕ :=
  maynardDivisorCutoff alpha (N - 1)

noncomputable def engelsmaMaynardRealRadius (alpha : ℝ) (N : ℕ) : ℝ :=
  maynardRealCutoff alpha (N - 1)

noncomputable def engelsmaMaynardScale (alpha : ℝ) (N : ℕ) : ℝ :=
  maynardSieveScale 105 (engelsmaMaynardModulus N) N
    (engelsmaMaynardRealRadius alpha N)

noncomputable def engelsmaPreSieveResidue (N : ℕ) : ℕ :=
  Classical.choose (exists_preSieveResidueClass_primorial
    BoundedGaps.engelsmaTuple_admissible (tripleLogCutoff (N - 1)))

theorem engelsmaPreSieveResidue_spec (N : ℕ) :
    engelsmaPreSieveResidue N < engelsmaMaynardModulus N ∧
      ∀ h ∈ BoundedGaps.engelsmaTuple,
        Nat.Coprime (engelsmaPreSieveResidue N + h)
          (engelsmaMaynardModulus N) := by
  exact Classical.choose_spec (exists_preSieveResidueClass_primorial
    BoundedGaps.engelsmaTuple_admissible (tripleLogCutoff (N - 1)))

theorem engelsmaPreSieveResidue_lt (N : ℕ) :
    engelsmaPreSieveResidue N < engelsmaMaynardModulus N :=
  (engelsmaPreSieveResidue_spec N).1

theorem engelsmaPreSieveResidue_coprime (N : ℕ)
    {h : ℕ} (hh : h ∈ BoundedGaps.engelsmaTuple) :
    Nat.Coprime (engelsmaPreSieveResidue N + h)
      (engelsmaMaynardModulus N) :=
  (engelsmaPreSieveResidue_spec N).2 h hh

theorem eventually_engelsmaMaynardScale_pos
    {alpha : ℝ} (halpha : 0 < alpha) :
    ∀ᶠ N : ℕ in atTop, 0 < engelsmaMaynardScale alpha N := by
  filter_upwards [eventually_ge_atTop 3] with N hN
  apply maynardSieveScale_pos
  · exact primorial_pos _
  · omega
  · apply maynardRealCutoff_gt_one
    · omega
    · exact halpha

theorem eventually_engelsmaMaynard_coverage :
    ∀ᶠ N : ℕ in atTop,
      CoversShiftDifferencePrimes BoundedGaps.engelsmaTuple
        (engelsmaMaynardModulus N) := by
  obtain ⟨N₀, hN₀⟩ := eventually_engelsma_primorial_coverage
  have hbase : ∀ᶠ M : ℕ in atTop,
      CoversShiftDifferencePrimes BoundedGaps.engelsmaTuple
        (primorial (tripleLogCutoff M)) := by
    rw [eventually_atTop]
    exact ⟨N₀, hN₀⟩
  simpa [engelsmaMaynardModulus] using
    (tendsto_sub_atTop_nat 1).eventually hbase

theorem eventually_engelsmaMaynardRadius_le
    {theta delta : ℝ} (hthetaHalf : theta < 1 / 2)
    (hdelta : 0 < delta) (hdeltaTheta : delta < theta / 2) :
    ∀ᶠ N : ℕ in atTop,
      engelsmaMaynardRadius (theta / 2 - delta) N ≤ N := by
  simpa [engelsmaMaynardRadius] using
    eventually_maynard_radius_le hthetaHalf hdelta hdeltaTheta

theorem eventually_engelsmaMaynard_modulus_radius_cutoff
    {theta delta : ℝ} (htheta : 0 ≤ theta) (hdelta : 0 < delta) :
    ∀ᶠ N : ℕ in atTop, ∀ h : ℕ,
      engelsmaMaynardModulus N *
          engelsmaMaynardRadius (theta / 2 - delta) N *
          engelsmaMaynardRadius (theta / 2 - delta) N ≤
        modulusCutoff theta (N + h - 1) := by
  simpa [engelsmaMaynardModulus, engelsmaMaynardRadius] using
    eventually_shifted_tripleLogPrimorial_divisorCutoff htheta hdelta

end BoundedGaps.Maynard
