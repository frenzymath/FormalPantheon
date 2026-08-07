import BoundedGaps.BombieriVinogradov.Analytic.DirichletPrimitiveExplicitFormula
import BoundedGaps.BombieriVinogradov.Analytic.DirichletNontrivialZeroTransport
import BoundedGaps.BombieriVinogradov.Analytic.PrimePowerCorrectionBound

/-!
# Dirichlet explicit formula

This file completes the arbitrary-character natural-endpoint specialization
of `KoukoulopoulosDistributionPrimesPrelim2022`, Theorem 11.3. Equations
(11.6)--(11.7) reduce the arithmetic sum to the primitive inducer; SEM-524
transports the complete multiplicity-weighted nontrivial-zero sum. Semantic
review: `SEM-535`.
-/

namespace BoundedGaps.Maynard

open Complex

noncomputable section

private local instance conductorNeZero
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) :
    NeZero chi.conductor :=
  ⟨chi.conductor_ne_zero⟩

/-- Passage to the primitive inducer preserves the source's displayed
principal main term and grouped nontrivial-zero sum. -/
theorem dirichletExplicitFormulaMainZeroTerms_eq_inducingPrimitive
    {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (x T : ℝ) :
    dirichletExplicitFormulaMainZeroTerms chi x T =
      dirichletExplicitFormulaMainZeroTerms
        chi.primitiveCharacter x T := by
  classical
  have hprincipal : chi = 1 ↔ chi.primitiveCharacter = 1 := by
    constructor
    · intro hchi
      subst chi
      exact DirichletCharacter.primitiveCharacter_one
    · intro hprimitive
      rw [← chi.changeLevel_primitiveCharacter]
      exact (DirichletCharacter.changeLevel_eq_one_iff
        chi.conductor_dvd_level).2 hprimitive
  rw [dirichletExplicitFormulaMainZeroTerms,
    dirichletExplicitFormulaMainZeroTerms,
    dirichletNontrivialZeroKernelSum_eq_inducingPrimitive chi x T]
  congr 1
  exact if_congr hprincipal rfl rfl

/-- The natural-endpoint specialization of Koukoulopoulos Theorem 11.3 for
an arbitrary Dirichlet character. -/
theorem
    exists_nat_norm_twistedChebyshevSum_sub_dirichletExplicitFormulaMainZeroTerms_le :
    ∃ K : ℕ, 1 ≤ K ∧
      ∀ (q : ℕ) [NeZero q]
        (chi : DirichletCharacter ℂ q),
          ∀ T : ℝ, 2 ≤ T →
            ∀ x : ℕ, 4 ≤ x → T ≤ (x : ℝ) →
              ‖twistedChebyshevSum x q chi -
                  dirichletExplicitFormulaMainZeroTerms chi (x : ℝ) T‖ ≤
                (K : ℝ) *
                  dirichletExplicitFormulaErrorScale (x : ℝ) q T := by
  obtain ⟨P, hP, hprimitive⟩ :=
    exists_nat_norm_twistedChebyshevSum_sub_dirichletExplicitFormulaMainZeroTerms_le_of_isPrimitive
  let K : ℕ := P + 1
  refine ⟨K, by dsimp [K]; omega, ?_⟩
  intro q _ chi T hT x hx hTx
  have hTpos : 0 < T := zero_lt_two.trans_le hT
  have hxposNat : 0 < x := by omega
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hxposNat
  have hxone : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
  have hqoneNat : 1 ≤ q := NeZero.pos q
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hqoneNat
  have hdposNat : 0 < chi.conductor :=
    Nat.pos_of_ne_zero chi.conductor_ne_zero
  have hdone : (1 : ℝ) ≤ chi.conductor := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr chi.conductor_ne_zero)
  have hdqNat : chi.conductor ≤ q :=
    Nat.le_of_dvd (NeZero.pos q) chi.conductor_dvd_level
  have hdq : (chi.conductor : ℝ) ≤ q := by exact_mod_cast hdqNat
  have hproduct :
      (x : ℝ) * chi.conductor ≤ (x : ℝ) * q :=
    mul_le_mul_of_nonneg_left hdq hxpos.le
  have hlogProduct :
      Real.log ((x : ℝ) * chi.conductor) ≤
        Real.log ((x : ℝ) * q) :=
    Real.log_le_log
      (mul_pos hxpos (by exact_mod_cast hdposNat)) hproduct
  have hlogConductor :
      0 ≤ Real.log ((x : ℝ) * chi.conductor) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le hxone hdone)
  have hlogLevel : 0 ≤ Real.log ((x : ℝ) * q) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le hxone hqone)
  have hlogSquare :
      Real.log ((x : ℝ) * chi.conductor) ^ 2 ≤
        Real.log ((x : ℝ) * q) ^ 2 :=
    (sq_le_sq₀ hlogConductor hlogLevel).2 hlogProduct
  have hscale :
      dirichletExplicitFormulaErrorScale (x : ℝ) chi.conductor T ≤
        dirichletExplicitFormulaErrorScale (x : ℝ) q T := by
    rw [dirichletExplicitFormulaErrorScale,
      dirichletExplicitFormulaErrorScale]
    apply (div_le_div_iff_of_pos_right hTpos).2
    exact mul_le_mul_of_nonneg_left hlogSquare hxpos.le
  have hxdiv : (1 : ℝ) ≤ (x : ℝ) / T :=
    (le_div_iff₀ hTpos).2 (by simpa using hTx)
  have hcorrectionScale :
      Real.log ((q * x : ℕ) : ℝ) ^ 2 ≤
        dirichletExplicitFormulaErrorScale (x : ℝ) q T := by
    calc
      Real.log ((q * x : ℕ) : ℝ) ^ 2 =
          Real.log ((x : ℝ) * q) ^ 2 := by
        rw [Nat.cast_mul, mul_comm]
      _ ≤ Real.log ((x : ℝ) * q) ^ 2 * ((x : ℝ) / T) := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hxdiv
            (sq_nonneg (Real.log ((x : ℝ) * q)))
      _ = dirichletExplicitFormulaErrorScale (x : ℝ) q T := by
        rw [dirichletExplicitFormulaErrorScale]
        ring
  have hcorrection :
      ‖twistedChebyshevSum x q chi -
          twistedChebyshevSum x chi.conductor chi.primitiveCharacter‖ ≤
        Real.log ((q * x : ℕ) : ℝ) ^ 2 := by
    simpa only [norm_sub_rev] using
      norm_primitiveTwistedChebyshevSum_sub_le_log_mul_sq
        (x := x) chi (by omega) hqoneNat
  have hprimitiveBound :=
    hprimitive chi.conductor chi.primitiveCharacter
      chi.primitiveCharacter_isPrimitive T hT x hx hTx
  have hmain :=
    dirichletExplicitFormulaMainZeroTerms_eq_inducingPrimitive
      chi (x : ℝ) T
  calc
    ‖twistedChebyshevSum x q chi -
          dirichletExplicitFormulaMainZeroTerms chi (x : ℝ) T‖ =
        ‖(twistedChebyshevSum x q chi -
            twistedChebyshevSum x chi.conductor chi.primitiveCharacter) +
          (twistedChebyshevSum x chi.conductor chi.primitiveCharacter -
            dirichletExplicitFormulaMainZeroTerms
              chi.primitiveCharacter (x : ℝ) T)‖ := by
      rw [hmain]
      congr 1
      ring
    _ ≤ ‖twistedChebyshevSum x q chi -
            twistedChebyshevSum x chi.conductor chi.primitiveCharacter‖ +
          ‖twistedChebyshevSum x chi.conductor chi.primitiveCharacter -
            dirichletExplicitFormulaMainZeroTerms
              chi.primitiveCharacter (x : ℝ) T‖ :=
      norm_add_le _ _
    _ ≤ Real.log ((q * x : ℕ) : ℝ) ^ 2 +
          (P : ℝ) *
            dirichletExplicitFormulaErrorScale
              (x : ℝ) chi.conductor T :=
      add_le_add hcorrection hprimitiveBound
    _ ≤ dirichletExplicitFormulaErrorScale (x : ℝ) q T +
          (P : ℝ) * dirichletExplicitFormulaErrorScale (x : ℝ) q T :=
      add_le_add hcorrectionScale
        (mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg P))
    _ = (K : ℝ) *
        dirichletExplicitFormulaErrorScale (x : ℝ) q T := by
      dsimp [K]
      push_cast
      ring

end

end BoundedGaps.Maynard
