import PrimesRestrictedDigits.MajorArcs.PositiveBlock

/-!
# Positive-block PNT and prime-power error scales

This proves the elementary logarithmic-budget and prime-power comparisons suppressed in the
positive-block application of Eq. (5.1) on published pp. 186--188. The PNT estimate itself
remains an explicit hypothesis.
-/

namespace PrimesRestrictedDigits

/-- A single `J^2*q` budget supplies the displayed relative-width and modulus
conditions in the positive-block application of Eq. (5.1). -/
theorem majorArcPositiveBlock_pnt_parameter_bounds
    {X : ℝ} {J m j q A : ℕ}
    (_hX : 0 < X) (hJ : 0 < J) (_hm : 0 < m)
    (hj : 0 < j) (hjJ : j < J) (hq : 0 < q) (_hA : 0 < A)
    (_hY : 1 < majorArcBlockLower X J m j)
    (hbudget : (J : ℝ) ^ 2 * (q : ℝ) ≤
      Real.log (majorArcBlockLower X J m j) ^ A) :
    (Real.log (majorArcBlockLower X J m j) ^ A)⁻¹ ≤
        (j : ℝ)⁻¹ ∧
      0 < (j : ℝ)⁻¹ ∧
      (j : ℝ)⁻¹ ≤ 1 ∧
      (q : ℝ) ≤ Real.log (majorArcBlockLower X J m j) ^ A := by
  let H := Real.log (majorArcBlockLower X J m j) ^ A
  have hJone : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hjleJ : (j : ℝ) ≤ J := by exact_mod_cast Nat.le_of_lt hjJ
  have hJsqone : (1 : ℝ) ≤ (J : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((J : ℝ) - 1)]
  have hJbudget : (J : ℝ) ≤ H := by
    calc
      (J : ℝ) = J * 1 := by ring
      _ ≤ J * J := mul_le_mul_of_nonneg_left hJone (by positivity)
      _ = J ^ 2 * 1 := by ring
      _ ≤ J ^ 2 * q := mul_le_mul_of_nonneg_left hqone (sq_nonneg _)
      _ ≤ H := by simpa [H] using hbudget
  have hqbudget : (q : ℝ) ≤ H := by
    calc
      (q : ℝ) = 1 * q := by ring
      _ ≤ J ^ 2 * q :=
        mul_le_mul_of_nonneg_right hJsqone (by positivity)
      _ ≤ H := by simpa [H] using hbudget
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj
  have hjone : (1 : ℝ) ≤ j := by exact_mod_cast hj
  refine ⟨inv_anti₀ hjpos (hjleJ.trans hJbudget), inv_pos.mpr hjpos, ?_, ?_⟩
  · rw [← inv_one]
    exact inv_anti₀ one_pos hjone
  · exact hqbudget

/-- The raw error in Eq. (5.1) fits the strengthened Section 11 local scale
under the common `J^2*q` logarithmic budget. -/
theorem majorArcPositiveBlock_rawError_le_scale_of_budget
    {X : ℝ} {J m j q A : ℕ}
    (hX : 0 < X) (hJ : 0 < J) (hm : 0 < m)
    (_hj : 0 < j) (hjJ : j < J) (hq : 0 < q) (_hA : 0 < A)
    (hY : 1 < majorArcBlockLower X J m j)
    (hbudget : (J : ℝ) ^ 2 * (q : ℝ) ≤
      Real.log (majorArcBlockLower X J m j) ^ A) :
    majorArcBlockLower X J m j /
        Real.log (majorArcBlockLower X J m j) ^ A ≤
      majorArcPositiveBlockErrorScale X J m q := by
  let Y := majorArcBlockLower X J m j
  let T := majorArcPositiveBlockErrorScale X J m q
  let P := Nat.totient q
  have hpow : 0 < Real.log Y ^ A := pow_pos (Real.log_pos hY) A
  have hjleJ : (j : ℝ) ≤ J := by exact_mod_cast Nat.le_of_lt hjJ
  have hPpos : 0 < P := Nat.totient_pos.mpr hq
  have hPleq : (P : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hsmall : (j : ℝ) * (J : ℝ) * (P : ℝ) ≤ Real.log Y ^ A := by
    calc
      (j : ℝ) * (J : ℝ) * (P : ℝ) ≤ (J : ℝ) ^ 2 * (q : ℝ) := by
        rw [pow_two]
        gcongr
      _ ≤ Real.log Y ^ A := by simpa [Y] using hbudget
  have hYeq : Y = (j : ℝ) * X / ((J : ℝ) * (m : ℝ)) := by
    simp [Y, majorArcBlockLower, majorArcBlockLength]
    ring
  have hTeq : T = X / ((J : ℝ) ^ 2 * (m : ℝ) * (P : ℝ)) := by
    dsimp [T]
    rw [majorArcPositiveBlockErrorScale_eq X hJ hm hq]
    simp only [Nat.cast_mul]
    ring
  have hden : 0 < (J : ℝ) ^ 2 * (m : ℝ) * (P : ℝ) := by positivity
  have hratio : Y / Real.log Y ^ A ≤ T := by
    rw [hTeq]
    apply (div_le_div_iff₀ hpow hden).2
    nth_rewrite 1 [hYeq]
    field_simp
    nlinarith [hsmall]
  simpa [Y, T] using hratio

/-- A pointwise upper-endpoint size condition absorbs the prime-power error
into the strengthened local scale. -/
theorem majorArcPositiveBlock_primePower_le_scale_of_size
    {X : ℝ} {J m j q : ℕ}
    (hX : 0 < X) (hJ : 0 < J) (hm : 0 < m)
    (_hj : 0 < j) (hjJ : j < J) (hq : 0 < q)
    (hupper : 1 ≤ majorArcBlockUpper X J m j)
    (hsize : 2 * (J : ℝ) ^ 2 * (q : ℝ) *
      Real.log (majorArcBlockUpper X J m j) ≤
        Real.sqrt (majorArcBlockUpper X J m j)) :
    2 * Real.sqrt (majorArcBlockUpper X J m j) *
        Real.log (majorArcBlockUpper X J m j) ≤
      majorArcPositiveBlockErrorScale X J m q := by
  let U := majorArcBlockUpper X J m j
  let L := majorArcBlockLength X J m
  let P := Nat.totient q
  have hU : 0 ≤ U := by linarith
  have hlog : 0 ≤ Real.log U := Real.log_nonneg hupper
  have hPpos : 0 < P := Nat.totient_pos.mpr hq
  have hPleq : (P : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have hsizeP :
      2 * (J : ℝ) ^ 2 * (P : ℝ) * Real.log U ≤ Real.sqrt U := by
    calc
      2 * (J : ℝ) ^ 2 * (P : ℝ) * Real.log U ≤
          2 * (J : ℝ) ^ 2 * (q : ℝ) * Real.log U := by gcongr
      _ ≤ Real.sqrt U := by simpa [U] using hsize
  have hden : 0 < (J : ℝ) ^ 2 * (P : ℝ) := by positivity
  have hfirst :
      2 * Real.sqrt U * Real.log U ≤ U / ((J : ℝ) ^ 2 * (P : ℝ)) := by
    apply (le_div_iff₀ hden).2
    calc
      2 * Real.sqrt U * Real.log U * ((J : ℝ) ^ 2 * (P : ℝ)) =
          (2 * (J : ℝ) ^ 2 * (P : ℝ) * Real.log U) * Real.sqrt U := by
            ring
      _ ≤ Real.sqrt U * Real.sqrt U := by gcongr
      _ = U := Real.mul_self_sqrt hU
  have hL : 0 < L := by
    dsimp [L, majorArcBlockLength]
    positivity
  have hUL : U ≤ (J : ℝ) * L := by
    dsimp [U, majorArcBlockUpper]
    apply mul_le_mul_of_nonneg_right _ hL.le
    exact_mod_cast Nat.succ_le_iff.mpr hjJ
  have hJreal : 0 < (J : ℝ) := by exact_mod_cast hJ
  have hsecond :
      U / ((J : ℝ) ^ 2 * (P : ℝ)) ≤ L / ((J : ℝ) * (P : ℝ)) := by
    apply (div_le_div_iff₀ hden (mul_pos hJreal (by exact_mod_cast hPpos))).2
    calc
      U * ((J : ℝ) * (P : ℝ)) ≤
          ((J : ℝ) * L) * ((J : ℝ) * (P : ℝ)) := by gcongr
      _ = L * ((J : ℝ) ^ 2 * (P : ℝ)) := by ring
  have hscale : majorArcPositiveBlockErrorScale X J m q =
      L / ((J : ℝ) * (P : ℝ)) := by
    dsimp [L, P]
    rw [majorArcPositiveBlockErrorScale, majorArcSubdivisionWidth]
    have hJ0 : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
    field_simp
  rw [hscale]
  exact hfirst.trans hsecond

/--
A raw Eq. (5.1) estimate yields the transferred prime-log bound once the two elementary
budgets have been checked.
-/
theorem majorArcPositiveBlock_primeLog_error_le_mul_scale_of_raw
    {X K : ℝ} {J m j q r A : ℕ}
    (hX : 0 < X) (hJ : 0 < J) (hm : 0 < m)
    (hj : 0 < j) (hjJ : j < J) (hq : 0 < q)
    (hA : 0 < A) (hK : 0 ≤ K)
    (hY : 1 < majorArcBlockLower X J m j)
    (hbudget : (J : ℝ) ^ 2 * (q : ℝ) ≤
      Real.log (majorArcBlockLower X J m j) ^ A)
    (hsize : 2 * (J : ℝ) ^ 2 * (q : ℝ) *
      Real.log (majorArcBlockUpper X J m j) ≤
        Real.sqrt (majorArcBlockUpper X J m j))
    (hPNT : |majorArcClosedVonMangoldtResidueSum X J m j q r -
      majorArcPositiveBlockMainTerm X J m q| ≤
        K * (majorArcBlockLower X J m j /
          Real.log (majorArcBlockLower X J m j) ^ A)) :
    |majorArcPrimeLogResidueSum X J m j q r -
      majorArcPositiveBlockMainTerm X J m q| ≤
        (K + 2) * majorArcPositiveBlockErrorScale X J m q := by
  have hL : 0 < majorArcBlockLength X J m := by
    rw [majorArcBlockLength]
    positivity
  have hlowerUpper : majorArcBlockLower X J m j <
      majorArcBlockUpper X J m j := by
    unfold majorArcBlockLower majorArcBlockUpper
    push_cast
    nlinarith
  have hupper : 1 ≤ majorArcBlockUpper X J m j :=
    hY.le.trans hlowerUpper.le
  have hraw := majorArcPositiveBlock_rawError_le_scale_of_budget
    hX hJ hm hj hjJ hq hA hY hbudget
  have hPNTscale : |majorArcClosedVonMangoldtResidueSum X J m j q r -
      majorArcPositiveBlockMainTerm X J m q| ≤
        K * majorArcPositiveBlockErrorScale X J m q :=
    hPNT.trans (mul_le_mul_of_nonneg_left hraw hK)
  have hprimePower := majorArcPositiveBlock_primePower_le_scale_of_size
    hX hJ hm hj hjJ hq hupper hsize
  exact majorArcPositiveBlock_primeLog_error_le_mul_scale
    hX hJ hm hj hq hupper hK hPNTscale hprimePower

end PrimesRestrictedDigits
