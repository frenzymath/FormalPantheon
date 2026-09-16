import PrimesRestrictedDigits.BasicEstimates.PrimeDistribution
import PrimesRestrictedDigits.MajorArcs.ResiduePhaseSum
import PrimesRestrictedDigits.MajorArcs.Subdivision
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Totient

/-!
# Positive-block prime-log transfer

This performs the prime-power and endpoint conversions suppressed in the application of Eq.
(5.1) on published pp. 187--188. The PNT estimate remains an explicit theorem hypothesis.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

open ArithmeticFunction

/-- The closed-interval von Mangoldt sum to which Eq. (5.1) applies. -/
noncomputable def majorArcClosedVonMangoldtResidueSum
    (X : ℝ) (J m j q r : ℕ) : ℝ :=
  ∑ n ∈ (naturalClosedInterval
      (majorArcBlockLower X J m j) (majorArcBlockUpper X J m j)).filter
        (fun n => n ≡ r [MOD q]), vonMangoldt n

/-- The half-open prime-log sum occurring in the Section 11 block. -/
noncomputable def majorArcPrimeLogResidueSum
    (X : ℝ) (J m j q r : ℕ) : ℝ :=
  ∑ p ∈ ((majorArcBlock X J m j).filter
      (fun n => n ≡ r [MOD q])).filter Nat.Prime, Real.log (p : ℝ)

/-- The prime-distribution main term on one block. -/
noncomputable def majorArcPositiveBlockMainTerm
    (X : ℝ) (J m q : ℕ) : ℝ :=
  majorArcBlockLength X J m / (Nat.totient q : ℝ)

/-- The strengthened local error scale used on published p. 187. -/
noncomputable def majorArcPositiveBlockErrorScale
    (X : ℝ) (J m q : ℕ) : ℝ :=
  majorArcSubdivisionWidth J * majorArcBlockLength X J m /
    (Nat.totient q : ℝ)

theorem majorArcPositiveBlockMainTerm_eq_relative
    (X : ℝ) {J m j q : ℕ} (hj : 0 < j) :
    (j : ℝ)⁻¹ * majorArcBlockLower X J m j / (Nat.totient q : ℝ) =
      majorArcPositiveBlockMainTerm X J m q := by
  unfold majorArcBlockLower majorArcPositiveBlockMainTerm
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
  field_simp

theorem majorArcPositiveBlockErrorScale_eq
    (X : ℝ) {J m q : ℕ} (hJ : 0 < J) (hm : 0 < m) (hq : 0 < q) :
    majorArcPositiveBlockErrorScale X J m q =
      X / (((J * J * m * Nat.totient q : ℕ) : ℝ)) := by
  have hJ0 : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hphi : 0 < Nat.totient q := Nat.totient_pos.mpr hq
  have hphi0 : (Nat.totient q : ℝ) ≠ 0 := by exact_mod_cast hphi.ne'
  rw [majorArcPositiveBlockErrorScale, majorArcSubdivisionWidth,
    majorArcBlockLength]
  push_cast
  field_simp

theorem majorArcPositiveBlock_primeLog_error_le
    {X : ℝ} {J m j q r : ℕ} {E : ℝ}
    (hX : 0 < X) (hJ : 0 < J) (hm : 0 < m) (hj : 0 < j)
    (_hq : 0 < q) (hupper : 1 ≤ majorArcBlockUpper X J m j)
    (hPNT : |majorArcClosedVonMangoldtResidueSum X J m j q r -
      majorArcPositiveBlockMainTerm X J m q| ≤ E) :
    |majorArcPrimeLogResidueSum X J m j q r -
      majorArcPositiveBlockMainTerm X J m q| ≤
        E + 2 * Real.sqrt (majorArcBlockUpper X J m j) *
          Real.log (majorArcBlockUpper X J m j) +
        Real.log (majorArcBlockUpper X J m j) := by
  let lower := majorArcBlockLower X J m j
  let upper := majorArcBlockUpper X J m j
  let P := fun n : ℕ => n ≡ r [MOD q]
  let s := (majorArcBlock X J m j).filter P
  let A := majorArcPrimeLogResidueSum X J m j q r
  let B := ∑ n ∈ s, vonMangoldt n
  let C := majorArcClosedVonMangoldtResidueSum X J m j q r
  let M := majorArcPositiveBlockMainTerm X J m q
  have hlower : 0 < lower := by
    dsimp [lower, majorArcBlockLower]
    have hw : 0 < majorArcBlockLength X J m := by
      rw [majorArcBlockLength]
      positivity
    positivity
  have hupper0 : 0 ≤ upper := by
    dsimp [upper]
    linarith
  have hs : s ⊆ Finset.Ioc 0 ⌊upper⌋₊ := by
    intro n hn
    have hnblock := mem_naturalLeftClosedRightOpenInterval.mp
      (Finset.mem_filter.mp hn).1
    rw [Finset.mem_Ioc]
    constructor
    · have hnreal : (0 : ℝ) < n := hlower.trans_le hnblock.1
      exact_mod_cast hnreal
    · apply Nat.le_floor
      exact hnblock.2.le
  have hAB : |A - B| ≤ 2 * Real.sqrt upper * Real.log upper := by
    have hremove := abs_sum_vonMangoldt_sub_sum_prime_log_le hupper s hs
    rw [abs_sub_comm] at hremove
    simpa [A, B, majorArcPrimeLogResidueSum, s, P, upper] using hremove
  have hBC : |B - C| ≤ Real.log upper := by
    have hendpoint :=
      abs_sum_vonMangoldt_naturalClosedInterval_sub_halfOpen_le_log
        P lower hupper
    rw [abs_sub_comm] at hendpoint
    simpa [B, C, majorArcClosedVonMangoldtResidueSum, s, P, lower, upper,
      majorArcBlock] using hendpoint
  have hCM : |C - M| ≤ E := by
    simpa [C, M] using hPNT
  calc
    |A - M| ≤ |A - B| + |B - M| := abs_sub_le A B M
    _ ≤ 2 * Real.sqrt upper * Real.log upper +
        (|B - C| + |C - M|) := add_le_add hAB (abs_sub_le B C M)
    _ ≤ 2 * Real.sqrt upper * Real.log upper + (Real.log upper + E) := by
      gcongr
    _ = E + 2 * Real.sqrt (majorArcBlockUpper X J m j) *
          Real.log (majorArcBlockUpper X J m j) +
        Real.log (majorArcBlockUpper X J m j) := by
      dsimp [upper]
      ring

theorem majorArcPositiveBlock_primeLog_error_le_mul_scale
    {X K : ℝ} {J m j q r : ℕ}
    (hX : 0 < X) (hJ : 0 < J) (hm : 0 < m) (hj : 0 < j)
    (hq : 0 < q) (hupper : 1 ≤ majorArcBlockUpper X J m j)
    (_hK : 0 ≤ K)
    (hPNT : |majorArcClosedVonMangoldtResidueSum X J m j q r -
      majorArcPositiveBlockMainTerm X J m q| ≤
        K * majorArcPositiveBlockErrorScale X J m q)
    (hprimePower : 2 * Real.sqrt (majorArcBlockUpper X J m j) *
      Real.log (majorArcBlockUpper X J m j) ≤
        majorArcPositiveBlockErrorScale X J m q) :
    |majorArcPrimeLogResidueSum X J m j q r -
      majorArcPositiveBlockMainTerm X J m q| ≤
        (K + 2) * majorArcPositiveBlockErrorScale X J m q := by
  let upper := majorArcBlockUpper X J m j
  let T := majorArcPositiveBlockErrorScale X J m q
  have hlog : 0 ≤ Real.log upper := Real.log_nonneg hupper
  have hsqrt : 1 ≤ Real.sqrt upper := Real.one_le_sqrt.mpr hupper
  have hendpoint : Real.log upper ≤ T := by
    calc
      Real.log upper = 1 * Real.log upper := by ring
      _ ≤ (2 * Real.sqrt upper) * Real.log upper := by gcongr; linarith
      _ = 2 * Real.sqrt upper * Real.log upper := by ring
      _ ≤ T := hprimePower
  have htransfer := majorArcPositiveBlock_primeLog_error_le
    hX hJ hm hj hq hupper hPNT
  dsimp [upper, T] at hlog hsqrt hendpoint ⊢
  linarith

theorem sum_majorArcPositiveBlock_errors_le
    {X K : ℝ} {J m q : ℕ} (hX : 0 ≤ X) (hK : 0 ≤ K)
    (hJ : 1 < J) (hm : 0 < m) (hq : 0 < q)
    (F : ℕ → ℕ → ℝ)
    (hF : ∀ j ∈ Finset.Ico 1 J, ∀ r ∈ majorArcReducedResidues q,
      |F j r| ≤ K * majorArcPositiveBlockErrorScale X J m q) :
    (∑ j ∈ Finset.Ico 1 J,
      ∑ r ∈ majorArcReducedResidues q, |F j r|) ≤
        K * majorArcBlockLength X J m := by
  have hJpos : 0 < J := Nat.zero_lt_of_lt hJ
  have hphi : 0 < Nat.totient q := Nat.totient_pos.mpr hq
  have hJreal : (0 : ℝ) < J := by exact_mod_cast hJpos
  have hphireal : (0 : ℝ) < Nat.totient q := by exact_mod_cast hphi
  have hlength : 0 ≤ majorArcBlockLength X J m := by
    rw [majorArcBlockLength]
    positivity
  have hratio : (((J - 1 : ℕ) : ℝ) * (J : ℝ)⁻¹) ≤ 1 := by
    rw [mul_inv_le_iff₀ hJreal]
    norm_num
  calc
    (∑ j ∈ Finset.Ico 1 J,
      ∑ r ∈ majorArcReducedResidues q, |F j r|) ≤
        ∑ j ∈ Finset.Ico 1 J,
          ∑ r ∈ majorArcReducedResidues q,
            K * majorArcPositiveBlockErrorScale X J m q := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro r hr
      exact hF j hj r hr
    _ = ((J - 1 : ℕ) : ℝ) * (Nat.totient q : ℝ) *
        (K * majorArcPositiveBlockErrorScale X J m q) := by
      rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul,
        Nat.card_Ico, card_majorArcReducedResidues]
      ring
    _ = K * ((((J - 1 : ℕ) : ℝ) * (J : ℝ)⁻¹) *
        majorArcBlockLength X J m) := by
      rw [majorArcPositiveBlockErrorScale, majorArcSubdivisionWidth]
      field_simp
    _ ≤ K * (1 * majorArcBlockLength X J m) := by
      gcongr
    _ = K * majorArcBlockLength X J m := by ring

end PrimesRestrictedDigits
