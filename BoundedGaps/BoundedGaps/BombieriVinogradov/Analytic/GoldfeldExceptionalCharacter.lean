import BoundedGaps.BombieriVinogradov.Analytic.GoldfeldDistinctLValueLower
import BoundedGaps.BombieriVinogradov.Analytic.GoldfeldLValueUpper
import Mathlib.Data.Set.Subsingleton

/-!
# Goldfeld's global exceptional character

Primitive real nonprincipal characters at varying moduli are packaged in one
dependent type.  The quantitative pairwise bounds from SEM-550 and SEM-560
then show that, for each positive exponent, at most one such character has a
zero in the corresponding near-one region.

Source: `KoukoulopoulosDistributionPrimesPrelim2022`, Theorem 12.9, printed
pp. 125--127. Semantic review: `SEM-561`.
-/

noncomputable section

open Complex Set

namespace BoundedGaps.Maynard

/-- A primitive real nonprincipal Dirichlet character, with its modulus, as
one global label across all character levels. -/
structure GoldfeldPrimitiveRealCharacter where
  modulus : ℕ
  modulus_gt_one : 1 < modulus
  character : DirichletCharacter ℂ modulus
  isPrimitive : character.IsPrimitive
  ne_one : character ≠ 1
  sq_eq_one : character ^ 2 = 1

instance (psi : GoldfeldPrimitiveRealCharacter) : NeZero psi.modulus :=
  ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt psi.modulus_gt_one)⟩

/-- The character has a real zero strictly inside the requested near-one
region. -/
def goldfeldPrimitiveNearOneZero
    (epsilon c : ℝ) (psi : GoldfeldPrimitiveRealCharacter) : Prop :=
  ∃ beta : ℝ,
    1 - c * (psi.modulus : ℝ) ^ (-epsilon) < beta ∧
      beta < 1 ∧
        DirichletCharacter.LFunction psi.character (beta : ℂ) = 0

/-- The source's real-axis zero-free conclusion for one primitive character. -/
def goldfeldPrimitiveZeroFree
    (epsilon c : ℝ) (psi : GoldfeldPrimitiveRealCharacter) : Prop :=
  ∀ sigma : ℝ,
    1 - c * (psi.modulus : ℝ) ^ (-epsilon) < sigma →
      DirichletCharacter.LFunction psi.character (sigma : ℂ) ≠ 0

/-- Global-label inequality is exactly canonical LCM-level character
distinctness. -/
theorem goldfeldPrimitiveRealCharacter_distinct_iff_ne
    (psi1 psi2 : GoldfeldPrimitiveRealCharacter) :
    goldfeldCharactersDistinct psi1.character psi2.character ↔
      psi1 ≠ psi2 := by
  constructor
  · intro hdistinct heq
    subst psi2
    exact (goldfeldCharactersDistinct_same_level_iff _ _).mp hdistinct rfl
  · intro hne
    by_cases hmodulus : psi1.modulus = psi2.modulus
    · cases psi1 with
      | mk q hq chi hprimitive hchi hsquare =>
        cases psi2 with
        | mk q' hq' chi' hprimitive' hchi' hsquare' =>
          dsimp at hmodulus
          subst q'
          letI : NeZero q :=
            ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt hq)⟩
          rw [goldfeldCharactersDistinct_same_level_iff]
          intro hcharacters
          apply hne
          cases hcharacters
          rfl
    · exact goldfeldCharactersDistinct_of_modulus_ne
        psi1.character psi2.character psi1.isPrimitive psi2.isPrimitive
        hmodulus

/-- Having a near-one zero is exactly failure of the real-axis zero-free
predicate. -/
theorem goldfeldPrimitiveNearOneZero_iff_not_zeroFree
    (epsilon c : ℝ) (psi : GoldfeldPrimitiveRealCharacter) :
    goldfeldPrimitiveNearOneZero epsilon c psi ↔
      ¬ goldfeldPrimitiveZeroFree epsilon c psi := by
  constructor
  · rintro ⟨beta, hbetaLower, _, hzero⟩ hzeroFree
    exact hzeroFree beta hbetaLower hzero
  · intro hnotZeroFree
    classical
    simp only [goldfeldPrimitiveZeroFree, not_forall,
      not_ne_iff] at hnotZeroFree
    obtain ⟨sigma, hsigmaLower, hzero⟩ := hnotZeroFree
    refine ⟨sigma, hsigmaLower, ?_, hzero⟩
    by_contra hsigmaOne
    have hone : 1 ≤ sigma := le_of_not_gt hsigmaOne
    exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re
      psi.character (.inl psi.ne_one) (by simpa using hone)) hzero

/-- For every positive exponent, the primitive real characters with a zero
in one common near-one region form a subsingleton across all moduli. -/
theorem exists_goldfeldPrimitiveNearOneZero_subsingleton :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ c : ℝ, 0 < c ∧
        Set.Subsingleton
          {psi : GoldfeldPrimitiveRealCharacter |
            goldfeldPrimitiveNearOneZero epsilon c psi} := by
  intro epsilon hepsilon
  obtain ⟨A, hA, c0, hc0, hLValueLower⟩ :=
    exists_goldfeldDistinctLValueLowerBound
  let r : ℝ := epsilon / 20
  let c : ℝ := min (1 / 2) (min
    (epsilon / (2 * (A : ℝ))) (c0 * r ^ 5 / 1024))
  have hAOne : (1 : ℝ) ≤ A := by exact_mod_cast (by omega : 1 ≤ A)
  have hAPos : (0 : ℝ) < A := zero_lt_one.trans_le hAOne
  have hrPos : 0 < r := by dsimp [r]; positivity
  have hcPos : 0 < c := by
    dsimp [c]
    exact lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hcHalf : c ≤ 1 / 2 := by
    dsimp [c]
    exact min_le_left _ _
  have hcExponent : c ≤ epsilon / (2 * (A : ℝ)) := by
    dsimp [c]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hcLog : c ≤ c0 * r ^ 5 / 1024 := by
    dsimp [c]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hordered :
      ∀ (psi1 psi : GoldfeldPrimitiveRealCharacter),
        psi1.modulus ≤ psi.modulus →
          goldfeldPrimitiveNearOneZero epsilon c psi1 →
            goldfeldPrimitiveNearOneZero epsilon c psi →
              goldfeldCharactersDistinct psi1.character psi.character →
                False := by
    intro psi1 psi hmoduli hnear1 hnear hdistinct
    obtain ⟨beta1, hbeta1Lower, hbeta1One, hzero1⟩ := hnear1
    obtain ⟨beta, hbetaLower, hbetaOne, hzero⟩ := hnear
    let Q : ℝ := psi.modulus
    let L : ℝ := Real.log Q
    let delta1 : ℝ := 1 - beta1
    let delta : ℝ := 1 - beta
    have hQOne : 1 ≤ Q := by
      dsimp [Q]
      exact_mod_cast psi.modulus_gt_one.le
    have hQPos : 0 < Q := zero_lt_one.trans_le hQOne
    have hLPos : 0 < L := by
      dsimp [L, Q]
      exact Real.log_pos (by exact_mod_cast psi.modulus_gt_one)
    have hq1PowLeOne :
        (psi1.modulus : ℝ) ^ (-epsilon) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos
        (by exact_mod_cast psi1.modulus_gt_one.le) (by linarith)
    have hqPowLeOne : Q ^ (-epsilon) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hQOne (by linarith)
    have hdelta1Near :
        delta1 < c * (psi1.modulus : ℝ) ^ (-epsilon) := by
      dsimp [delta1]
      linarith
    have hdeltaNear : delta < c * Q ^ (-epsilon) := by
      dsimp [delta, Q] at hbetaLower ⊢
      linarith
    have hdelta1LtC : delta1 < c :=
      hdelta1Near.trans_le (mul_le_of_le_one_right hcPos.le hq1PowLeOne)
    have hdeltaLtC : delta < c :=
      hdeltaNear.trans_le (mul_le_of_le_one_right hcPos.le hqPowLeOne)
    have hbeta1Half : 1 / 2 < beta1 := by
      have hbase : 1 - c ≤
          1 - c * (psi1.modulus : ℝ) ^ (-epsilon) := by
        linarith [mul_le_of_le_one_right hcPos.le hq1PowLeOne]
      linarith
    have hbetaHalf : 1 / 2 < beta := by
      have hbase : 1 - c ≤ 1 - c * Q ^ (-epsilon) := by
        linarith [mul_le_of_le_one_right hcPos.le hqPowLeOne]
      dsimp [Q] at hbase hbetaLower
      linarith
    have hLower := hLValueLower psi1.modulus psi.modulus
      psi1.modulus_gt_one hmoduli psi1.character psi.character
      psi1.ne_one psi.ne_one psi1.sq_eq_one psi.sq_eq_one hdistinct
      beta1 (by linarith) hbeta1One hzero1
    have hUpper := norm_LFunction_one_of_real_zero_le
      psi.modulus_gt_one psi.character psi.ne_one hbetaOne.le hzero
    have hLThreePos : 0 < L ^ 3 := pow_pos hLPos 3
    have hcomparison :
        c0 * Q ^ (-((A : ℝ) * delta1)) ≤
          512 * delta * Q ^ (delta / 2) * L ^ 5 := by
      calc
        c0 * Q ^ (-((A : ℝ) * delta1)) ≤
            ‖DirichletCharacter.LFunction psi.character (1 : ℂ)‖ *
              L ^ 3 := by
          apply (div_le_iff₀ hLThreePos).mp
          simpa [Q, L, delta1] using hLower
        _ ≤ (512 * delta * Q ^ (delta / 2) * L ^ 2) * L ^ 3 :=
          mul_le_mul_of_nonneg_right (by simpa [Q, L, delta] using hUpper)
            hLThreePos.le
        _ = 512 * delta * Q ^ (delta / 2) * L ^ 5 := by ring
    have hdelta1Exponent :
        (A : ℝ) * delta1 < epsilon / 2 := by
      have hdelta1Bound :
          delta1 < epsilon / (2 * (A : ℝ)) :=
        hdelta1LtC.trans_le hcExponent
      calc
        (A : ℝ) * delta1 <
            (A : ℝ) * (epsilon / (2 * (A : ℝ))) :=
          mul_lt_mul_of_pos_left hdelta1Bound hAPos
        _ = epsilon / 2 := by field_simp [hAPos.ne']
    have hleftFloor :
        c0 * Q ^ (-epsilon / 2) ≤
          c0 * Q ^ (-((A : ℝ) * delta1)) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hQOne (by linarith)) hc0.le
    have hcScaled : c * (2 * (A : ℝ)) ≤ epsilon :=
      (le_div_iff₀ (by positivity : 0 < 2 * (A : ℝ))).mp hcExponent
    have hcEpsilonHalf : c ≤ epsilon / 2 := by
      have htwoC : 2 * c ≤ c * (2 * (A : ℝ)) := by
        calc
          2 * c = c * (2 * 1) := by ring
          _ ≤ c * (2 * (A : ℝ)) := by gcongr
      linarith
    have hdeltaQuarter : delta / 2 ≤ epsilon / 4 := by
      linarith
    have hdeltaPower : Q ^ (delta / 2) ≤ Q ^ (epsilon / 4) :=
      Real.rpow_le_rpow_of_exponent_le hQOne hdeltaQuarter
    have hlogBase : L ≤ Q ^ r / r := by
      simpa [L, Q] using
        Real.log_natCast_le_rpow_div psi.modulus hrPos
    have hlogPow : L ^ 5 ≤ Q ^ (epsilon / 4) / r ^ 5 := by
      calc
        L ^ 5 ≤ (Q ^ r / r) ^ 5 :=
          pow_le_pow_left₀ hLPos.le hlogBase 5
        _ = Q ^ (epsilon / 4) / r ^ 5 := by
          rw [div_pow, ← Real.rpow_mul_natCast hQPos.le]
          congr 2
          dsimp [r]
          ring
    have hpowThreeQuarter :
        Q ^ (-epsilon) * Q ^ (epsilon / 4) =
          Q ^ (-3 * epsilon / 4) := by
      rw [← Real.rpow_add hQPos]
      congr 1
      ring
    have hpowHalf :
        Q ^ (-3 * epsilon / 4) * Q ^ (epsilon / 4) =
          Q ^ (-epsilon / 2) := by
      rw [← Real.rpow_add hQPos]
      congr 1
      ring
    have hupperStrict :
        512 * delta * Q ^ (delta / 2) * L ^ 5 <
          c0 * Q ^ (-epsilon / 2) := by
      calc
        512 * delta * Q ^ (delta / 2) * L ^ 5 <
            512 * (c * Q ^ (-epsilon)) * Q ^ (delta / 2) *
              L ^ 5 := by gcongr
        _ ≤ 512 * (c * Q ^ (-epsilon)) * Q ^ (epsilon / 4) *
              L ^ 5 := by gcongr
        _ = 512 * c * Q ^ (-3 * epsilon / 4) * L ^ 5 := by
          rw [show 512 * (c * Q ^ (-epsilon)) * Q ^ (epsilon / 4) *
              L ^ 5 = 512 * c *
                (Q ^ (-epsilon) * Q ^ (epsilon / 4)) * L ^ 5 by ring,
            hpowThreeQuarter]
        _ ≤ 512 * (c0 * r ^ 5 / 1024) *
              Q ^ (-3 * epsilon / 4) *
                (Q ^ (epsilon / 4) / r ^ 5) := by gcongr
        _ = (c0 / 2) * Q ^ (-epsilon / 2) := by
          calc
            512 * (c0 * r ^ 5 / 1024) * Q ^ (-3 * epsilon / 4) *
                (Q ^ (epsilon / 4) / r ^ 5) =
                (c0 / 2) *
                  (Q ^ (-3 * epsilon / 4) * Q ^ (epsilon / 4)) := by
              field_simp [hrPos.ne']; ring
            _ = (c0 / 2) * Q ^ (-epsilon / 2) := by rw [hpowHalf]
        _ < c0 * Q ^ (-epsilon / 2) := by
          have hproductPos : 0 < c0 * Q ^ (-epsilon / 2) :=
            mul_pos hc0 (Real.rpow_pos_of_pos hQPos _)
          nlinarith
    exact (not_lt_of_ge (hleftFloor.trans hcomparison)) hupperStrict
  refine ⟨c, hcPos, ?_⟩
  intro psi1 hnear1 psi2 hnear2
  by_contra hne
  rcases le_total psi1.modulus psi2.modulus with hle | hle
  · exact hordered psi1 psi2 hle hnear1 hnear2
      ((goldfeldPrimitiveRealCharacter_distinct_iff_ne _ _).2 hne)
  · exact hordered psi2 psi1 hle hnear2 hnear1
      ((goldfeldPrimitiveRealCharacter_distinct_iff_ne _ _).2 (Ne.symm hne))

/-- Source-facing Theorem 12.9: after fixing the exponent, every primitive
real nonprincipal character except one optional global label is zero-free. -/
theorem exists_goldfeldPrimitiveExceptionalCharacter :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ c : ℝ, 0 < c ∧
        ∃ exception : Option GoldfeldPrimitiveRealCharacter,
          ∀ psi : GoldfeldPrimitiveRealCharacter,
            some psi ≠ exception →
              goldfeldPrimitiveZeroFree epsilon c psi := by
  intro epsilon hepsilon
  obtain ⟨c, hc, hsubsingleton⟩ :=
    exists_goldfeldPrimitiveNearOneZero_subsingleton epsilon hepsilon
  refine ⟨c, hc, ?_⟩
  classical
  by_cases hnonempty :
      Set.Nonempty
        {psi : GoldfeldPrimitiveRealCharacter |
          goldfeldPrimitiveNearOneZero epsilon c psi}
  · obtain ⟨exception, hexception⟩ := hnonempty
    refine ⟨some exception, ?_⟩
    intro psi hpsi
    by_contra hnotZeroFree
    have hnear :=
      (goldfeldPrimitiveNearOneZero_iff_not_zeroFree _ _ _).2
        hnotZeroFree
    have heq : psi = exception := hsubsingleton hnear hexception
    exact hpsi (congrArg some heq)
  · refine ⟨none, ?_⟩
    intro psi _
    by_contra hnotZeroFree
    exact hnonempty ⟨psi,
      (goldfeldPrimitiveNearOneZero_iff_not_zeroFree _ _ _).2
        hnotZeroFree⟩

end BoundedGaps.Maynard
