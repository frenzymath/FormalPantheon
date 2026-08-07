import BoundedGaps.Maynard.SmallKVariationalConclusion
import BoundedGaps.Maynard.Distribution

/-!
# Selecting the unconditional distribution level

Source: `Maynard2013v3`, printed Section 4, Propositions 4.2--4.3 and the
proof of Theorem 1.3, source lines 218--243. Semantic review: `SEM-095`.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

theorem exists_usable_level_of_bombieriVinogradov
    (hBV : bombieriVinogradov) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 / 2 ∧ hasPrimeLevel θ ∧
      1 < θ * maynardM 105 / 2 := by
  let θ : ℝ := (maynardM 105)⁻¹ + 1 / 4
  have hM := maynardM_105_gt_four
  have hMpos : 0 < maynardM 105 := by linarith
  have hinv : 0 < (maynardM 105)⁻¹ := inv_pos.mpr hMpos
  have hθpos : 0 < θ := by
    dsimp [θ]
    positivity
  have hθlt : θ < 1 / 2 := by
    dsimp [θ]
    have hinvlt : (maynardM 105)⁻¹ < (4 : ℝ)⁻¹ := by
      simpa [one_div] using
        one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 4) hM
    linarith
  have hlevel : hasPrimeLevel θ := hBV θ hθpos hθlt
  have hthreshold : 1 < θ * maynardM 105 / 2 := by
    dsimp [θ]
    field_simp [ne_of_gt hMpos]
    nlinarith
  exact ⟨θ, hθpos, hθlt, hlevel, hthreshold⟩

theorem exists_smallKCandidate_level_with_positive_mainTerm
    (hBV : bombieriVinogradov) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 / 2 ∧ hasPrimeLevel θ ∧
      0 < (θ / 2) * (∑ m : Fin 105, maynardJ 105 m smallKCandidate) -
        maynardI 105 smallKCandidate := by
  let Q := maynardRatio 105 smallKCandidate
  let θ : ℝ := Q⁻¹ + 1 / 4
  have hQ : (4 : ℝ) < Q := smallKCandidate_ratio_gt_four
  have hQpos : 0 < Q := by linarith
  have hθpos : 0 < θ := by
    dsimp [θ]
    positivity
  have hθlt : θ < 1 / 2 := by
    dsimp [θ]
    have hinvlt : Q⁻¹ < (4 : ℝ)⁻¹ := by
      simpa [one_div] using
        one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 4) hQ
    linarith
  have hlevel := hBV θ hθpos hθlt
  have hthreshold : 1 < θ * Q / 2 := by
    dsimp [θ]
    field_simp [ne_of_gt hQpos]
    nlinarith
  have hI : 0 < maynardI 105 smallKCandidate :=
    smallKCandidate_I_pos_of_denominator_identity
      maynardI_eq_smallKDenominator
  have hnum : (∑ m : Fin 105, maynardJ 105 m smallKCandidate) =
      Q * maynardI 105 smallKCandidate := by
    dsimp [Q]
    rw [maynardRatio]
    field_simp [ne_of_gt hI]
  refine ⟨θ, hθpos, hθlt, hlevel, ?_⟩
  rw [hnum]
  nlinarith [mul_pos (sub_pos.mpr hthreshold) hI]

theorem exists_smallKCandidate_level_delta_with_positive_mainTerm
    (hBV : bombieriVinogradov) :
    ∃ θ δ : ℝ, 0 < θ ∧ θ < 1 / 2 ∧ hasPrimeLevel θ ∧
      0 < δ ∧ δ < θ / 2 ∧
      0 < (θ / 2 - δ) *
          (∑ m : Fin 105, maynardJ 105 m smallKCandidate) -
        maynardI 105 smallKCandidate := by
  obtain ⟨θ, hθ0, hθhalf, hlevel, hgap⟩ :=
    exists_smallKCandidate_level_with_positive_mainTerm hBV
  let S := ∑ m : Fin 105, maynardJ 105 m smallKCandidate
  let I := maynardI 105 smallKCandidate
  have hI : 0 < I := by
    dsimp [I]
    exact smallKCandidate_I_pos_of_denominator_identity
      maynardI_eq_smallKDenominator
  have hS : 0 < S := by
    dsimp [S]
    rw [maynardNumerator_eq_smallKNumerator]
    have hnum : 0 < smallKNumerator := by
      rw [smallK_numerator_eq_certified]
      exact smallK_certified_numerator_pos
    exact_mod_cast hnum
  let gap := (θ / 2) * S - I
  let δ := gap / (2 * S)
  have hgap' : 0 < gap := hgap
  have hden : 0 < 2 * S := mul_pos (by norm_num) hS
  have hδ : 0 < δ := div_pos hgap' hden
  have hδlt : δ < θ / 2 := by
    dsimp [δ, gap]
    rw [div_lt_iff₀ hden]
    nlinarith
  refine ⟨θ, δ, hθ0, hθhalf, hlevel, hδ, hδlt, ?_⟩
  have heq : (θ / 2 - δ) * S - I = gap / 2 := by
    dsimp [δ]
    field_simp [ne_of_gt hS]
    ring
  rw [show (∑ m : Fin 105, maynardJ 105 m smallKCandidate) = S by rfl,
    show maynardI 105 smallKCandidate = I by rfl, heq]
  exact div_pos hgap' (by norm_num)

end BoundedGaps.Maynard
