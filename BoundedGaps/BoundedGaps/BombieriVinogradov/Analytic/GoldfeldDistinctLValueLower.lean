import BoundedGaps.BombieriVinogradov.Analytic.GoldfeldCrossLevelCharacters
import BoundedGaps.BombieriVinogradov.Analytic.GoldfeldLeftLineIntegral
import BoundedGaps.BombieriVinogradov.Analytic.GoldfeldQuantitativeResidue

/-!
# Goldfeld's distinct-character L-value lower bound

One global scale choice makes the complete left line smaller than one half.
Combining the resulting residue lower bound with its explicit upper bound
gives the pairwise quantitative L-value estimate used in the proof of
Koukoulopoulos Theorem 12.9.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, printed p. 126.
Semantic review: `SEM-560`.
-/

noncomputable section

open Complex

namespace BoundedGaps.Maynard

/-- Uniform project-derived norm analogue of Goldfeld's pairwise L-value
lower bound.  The witnesses are chosen before all character data. -/
theorem exists_goldfeldDistinctLValueLowerBound :
    ∃ A : ℕ, 58 ≤ A ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (q1 q : ℕ) [NeZero q1] [NeZero q],
        1 < q1 → q1 ≤ q →
        ∀ (chi1 : DirichletCharacter ℂ q1)
          (chi : DirichletCharacter ℂ q),
          chi1 ≠ 1 → chi ≠ 1 →
          chi1 ^ 2 = 1 → chi ^ 2 = 1 →
          goldfeldCharactersDistinct chi1 chi →
          ∀ beta : ℝ, 0 ≤ beta → beta < 1 →
            DirichletCharacter.LFunction chi1 (beta : ℂ) = 0 →
            c * (q : ℝ) ^ (-((A : ℝ) * (1 - beta))) /
                (Real.log (q : ℝ)) ^ 3 ≤
              ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ := by
  obtain ⟨E, hE, C, hC, hleft⟩ :=
    exists_norm_goldfeldVerticalIntegral_neg_one_le
  let D : ℝ := 2 * max 1 C
  let A : ℕ := E + 1
  let c : ℝ := (131072 * D)⁻¹
  have hDpos : 0 < D := by
    dsimp [D]
    positivity
  have hDone : 1 ≤ D := by
    dsimp [D]
    nlinarith [le_max_left (1 : ℝ) C]
  have hcpos : 0 < c := by
    dsimp [c]
    positivity
  refine ⟨A, ?_, c, hcpos, ?_⟩
  · dsimp [A]
    omega
  intro q1 q _ _ hq1 hq1q chi1 chi hchi1 hchi
    hsquare1 hsquare hdistinct beta hbeta0 hbeta1 hzero
  have hqOne : 1 < q := hq1.trans_le hq1q
  have hqPos : 0 < (q : ℝ) := by positivity
  have hqRealOne : (1 : ℝ) ≤ q := by exact_mod_cast hqOne.le
  have hlogqPos : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast hqOne)
  have hcross : DirichletCharacter.mul chi1 chi ≠ 1 :=
    goldfeldCrossLevelMul_ne_one chi1 chi hsquare1 hdistinct
  let x : ℝ := D * (q : ℝ) ^ E
  have hqPowPos : 0 < (q : ℝ) ^ E := pow_pos hqPos E
  have hqPowOne : (1 : ℝ) ≤ (q : ℝ) ^ E := one_le_pow₀ hqRealOne
  have hxOne : 1 ≤ x := by
    dsimp [x]
    exact one_le_mul_of_one_le_of_one_le hDone hqPowOne
  have hleftAtScale := hleft q1 q hq1 hq1q chi1 chi
    hchi1 hchi hcross beta x hbeta0 hbeta1.le hxOne
  have hscaleIdentity : C * (q : ℝ) ^ E / x = C / D := by
    dsimp [x]
    field_simp [hDpos.ne', hqPowPos.ne']
  have hCmax : C ≤ max 1 C := le_max_right 1 C
  have hCdiv : C / D ≤ (1 : ℝ) / 2 := by
    apply (div_le_iff₀ hDpos).2
    dsimp [D]
    nlinarith
  have hleftSmall :
      ‖goldfeldVerticalIntegral chi1 chi beta x (-1)‖ ≤ 1 / 2 :=
    hleftAtScale.trans (hscaleIdentity.trans_le hCdiv)
  have hresLower := half_le_norm_goldfeldContourResidue_of_leftLine
    hq1 hq1q chi1 chi hchi1 hchi hcross hsquare1 hsquare
    hbeta0 hbeta1 hxOne hzero hleftSmall
  have hresUpper := norm_goldfeldContourResidue_le
    hq1 hq1q chi1 chi hchi1 hcross hbeta0 hbeta1 hxOne hzero
  let delta : ℝ := 1 - beta
  have hdelta0 : 0 < delta := by dsimp [delta]; linarith
  have hdelta1 : delta ≤ 1 := by dsimp [delta]; linarith
  have hdeltaNonneg : 0 ≤ delta := hdelta0.le
  have hmaster :
      1 ≤ 131072 * x ^ delta * (q : ℝ) ^ (delta / 2) *
        (Real.log (q : ℝ)) ^ 3 *
        ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ := by
    calc
      (1 : ℝ) = 2 * (1 / 2 : ℝ) := by norm_num
      _ ≤ 2 * ‖goldfeldContourResidue chi1 chi beta x‖ :=
        mul_le_mul_of_nonneg_left hresLower (by norm_num)
      _ ≤ 2 * (65536 * x ^ (1 - beta) *
          (q : ℝ) ^ ((1 - beta) / 2) *
          (Real.log (q : ℝ)) ^ 3 *
          ‖DirichletCharacter.LFunction chi (1 : ℂ)‖) :=
        mul_le_mul_of_nonneg_left hresUpper (by norm_num)
      _ = 131072 * x ^ delta * (q : ℝ) ^ (delta / 2) *
          (Real.log (q : ℝ)) ^ 3 *
          ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ := by
        dsimp [delta]
        ring
  have hDpow : D ^ delta ≤ D := by
    simpa using Real.rpow_le_rpow_of_exponent_le hDone hdelta1
  have hexponent :
      (E : ℝ) * delta + delta / 2 ≤ (A : ℝ) * delta := by
    dsimp [A]
    push_cast
    nlinarith
  have hqExponent :
      (q : ℝ) ^ ((E : ℝ) * delta + delta / 2) ≤
        (q : ℝ) ^ ((A : ℝ) * delta) :=
    Real.rpow_le_rpow_of_exponent_le hqRealOne hexponent
  have hscalePower :
      x ^ delta * (q : ℝ) ^ (delta / 2) ≤
        D * (q : ℝ) ^ ((A : ℝ) * delta) := by
    calc
      x ^ delta * (q : ℝ) ^ (delta / 2) =
          (D ^ delta * (((q : ℝ) ^ E) ^ delta)) *
            (q : ℝ) ^ (delta / 2) := by
        dsimp [x]
        rw [Real.mul_rpow hDpos.le (pow_nonneg hqPos.le E)]
      _ = D ^ delta *
          (q : ℝ) ^ ((E : ℝ) * delta + delta / 2) := by
        rw [← Real.rpow_natCast_mul hqPos.le E delta,
          mul_assoc, ← Real.rpow_add hqPos]
      _ ≤ D * (q : ℝ) ^ ((E : ℝ) * delta + delta / 2) :=
        mul_le_mul_of_nonneg_right hDpow (Real.rpow_nonneg hqPos.le _)
      _ ≤ D * (q : ℝ) ^ ((A : ℝ) * delta) :=
        mul_le_mul_of_nonneg_left hqExponent hDpos.le
  have hmaster' :
      1 ≤ 131072 * D * (q : ℝ) ^ ((A : ℝ) * delta) *
        (Real.log (q : ℝ)) ^ 3 *
        ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ := by
    calc
      (1 : ℝ) ≤ 131072 *
          (x ^ delta * (q : ℝ) ^ (delta / 2)) *
          (Real.log (q : ℝ)) ^ 3 *
          ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ := by
        simpa [mul_assoc] using hmaster
      _ ≤ 131072 *
          (D * (q : ℝ) ^ ((A : ℝ) * delta)) *
          (Real.log (q : ℝ)) ^ 3 *
          ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ := by
        gcongr
      _ = 131072 * D * (q : ℝ) ^ ((A : ℝ) * delta) *
          (Real.log (q : ℝ)) ^ 3 *
          ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ := by ring
  have hdenPos :
      0 < 131072 * D * (q : ℝ) ^ ((A : ℝ) * delta) *
        (Real.log (q : ℝ)) ^ 3 := by
    positivity
  have hdivided :
      1 / (131072 * D * (q : ℝ) ^ ((A : ℝ) * delta) *
          (Real.log (q : ℝ)) ^ 3) ≤
        ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ := by
    apply (div_le_iff₀ hdenPos).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmaster'
  calc
    c * (q : ℝ) ^ (-((A : ℝ) * (1 - beta))) /
          (Real.log (q : ℝ)) ^ 3 =
        1 / (131072 * D * (q : ℝ) ^ ((A : ℝ) * delta) *
          (Real.log (q : ℝ)) ^ 3) := by
      dsimp [c, delta]
      rw [Real.rpow_neg hqPos.le]
      field_simp [hDpos.ne',
        (Real.rpow_pos_of_pos hqPos ((A : ℝ) * (1 - beta))).ne',
        hlogqPos.ne']
    _ ≤ ‖DirichletCharacter.LFunction chi (1 : ℂ)‖ := hdivided

end BoundedGaps.Maynard
