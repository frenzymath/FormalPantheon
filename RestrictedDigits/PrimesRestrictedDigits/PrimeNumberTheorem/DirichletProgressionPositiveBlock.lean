import PrimesRestrictedDigits.MajorArcs.PositiveBlockGrowth
import PrimesRestrictedDigits.PrimeNumberTheorem.DirichletProgressionShortInterval

/-!
# Prime-log distribution on positive major-arc blocks

This composes the repaired closed short-interval progression theorem with the
finite and scale transfers used on `MAYNARD-PRD-PUBLISHED`, pp. 187--188.
-/

namespace PrimesRestrictedDigits

/-- A fixed positive log exponent gives one coefficient and lower-endpoint
threshold for every eligible positive block. -/
theorem exists_majorArcPositiveBlock_primeLog_error_le
    (A : Nat) (hA : 0 < A) :
    ∃ E Y0 : Real,
      0 < E ∧ 4 <= Y0 ∧
      ∀ X : Real, 0 < X ->
        ∀ J m j q r : Nat,
          0 < J -> 0 < m -> 0 < j -> j < J -> 0 < q ->
          IsDecimalSmooth q -> Nat.Coprime r q ->
          Y0 <= majorArcBlockLower X J m j ->
          (J : Real) ^ 2 * (q : Real) <=
            Real.log (majorArcBlockLower X J m j) ^ A ->
          2 * (J : Real) ^ 2 * (q : Real) *
            Real.log (majorArcBlockUpper X J m j) <=
              Real.sqrt (majorArcBlockUpper X J m j) ->
          abs (majorArcPrimeLogResidueSum X J m j q r -
            majorArcPositiveBlockMainTerm X J m q) <=
              E * majorArcPositiveBlockErrorScale X J m q := by
  obtain ⟨C0, Y0, hC0, hY0, hShort⟩ :=
    exists_abs_vonMangoldtClosedProgressionSum_sub_main_log_pow_le A hA
  refine ⟨C0 + 2, Y0, by positivity, hY0, ?_⟩
  intro X hX J m j q r hJ hm hj hjJ hq hSmooth hr hY0local hbudget hsize
  let Y := majorArcBlockLower X J m j
  let U := majorArcBlockUpper X J m j
  let Delta : Real := (j : Real)⁻¹
  have hYgt : 1 < Y := by
    dsimp [Y]
    linarith
  have hparameters := majorArcPositiveBlock_pnt_parameter_bounds
    hX hJ hm hj hjJ hq hA hYgt hbudget
  have hUpper : Y + Delta * Y = U := by
    dsimp [Y, U, Delta, majorArcBlockLower, majorArcBlockUpper]
    push_cast
    have hj0 : (j : Real) ≠ 0 := by exact_mod_cast hj.ne'
    field_simp [hj0]
  have hClosed := hShort Y (by simpa [Y] using hY0local) Delta
    hparameters.2.1 hparameters.2.2.1 hparameters.1 q hq hSmooth r hr
    hparameters.2.2.2
  rw [hUpper] at hClosed
  have hMain := majorArcPositiveBlockMainTerm_eq_relative X
    (J := J) (m := m) (j := j) (q := q) hj
  have hPNT :
      abs (majorArcClosedVonMangoldtResidueSum X J m j q r -
        majorArcPositiveBlockMainTerm X J m q) <=
          C0 * (majorArcBlockLower X J m j /
            Real.log (majorArcBlockLower X J m j) ^ A) := by
    have hPNT' :
        abs (majorArcClosedVonMangoldtResidueSum X J m j q r -
          majorArcPositiveBlockMainTerm X J m q) <=
            C0 * majorArcBlockLower X J m j /
              Real.log (majorArcBlockLower X J m j) ^ A := by
      simpa [vonMangoldtClosedProgressionSum,
        majorArcClosedVonMangoldtResidueSum, Y, U, Delta, hMain] using hClosed
    calc
      _ <= C0 * majorArcBlockLower X J m j /
          Real.log (majorArcBlockLower X J m j) ^ A := hPNT'
      _ = C0 * (majorArcBlockLower X J m j /
          Real.log (majorArcBlockLower X J m j) ^ A) := by ring
  exact majorArcPositiveBlock_primeLog_error_le_mul_scale_of_raw
    hX hJ hm hj hjJ hq hA hC0.le hYgt hbudget hsize hPNT

/-- At the source logarithmic subdivision, one coefficient and natural cutoff
work uniformly over every actual arity, supported product, positive block,
decimal-smooth modulus, and coprime residue. -/
theorem exists_majorArcPositiveBlockSource_primeLog_error_le
    (D ellMax : Nat) {eta : Real} (heta : 0 < eta) :
    ∃ E : Real, 0 < E ∧
      ∃ X0 : Nat, ∀ X ell m j q r : Nat,
        X0 <= X ->
        0 < ell -> ell <= ellMax -> (ell : Real) <= 2 / eta ->
        0 < m -> (m : Real) < (X : Real) ^ (1 - eta / 3) ->
        0 < j -> j < majorArcLogSubdivisionCount X D ell ->
        0 < q -> IsDecimalSmooth q ->
        (q : Real) <= Real.log (X : Real) ^ D ->
        Nat.Coprime r q ->
        abs (majorArcPrimeLogResidueSum (X : Real)
          (majorArcLogSubdivisionCount X D ell) m j q r -
            majorArcPositiveBlockMainTerm (X : Real)
              (majorArcLogSubdivisionCount X D ell) m q) <=
          E * majorArcPositiveBlockErrorScale (X : Real)
            (majorArcLogSubdivisionCount X D ell) m q := by
  let A := majorArcPositiveBlockPNTExponent D ellMax
  have hA : 0 < A := majorArcPositiveBlockPNTExponent_pos D ellMax
  obtain ⟨E, Y0, hE, hY0, hBlock⟩ :=
    exists_majorArcPositiveBlock_primeLog_error_le A hA
  obtain ⟨Xbase, hXbase⟩ :=
    exists_majorArcPositiveBlockSourceBudgetThreshold D ellMax heta (by linarith)
  let X0 : Nat := max Xbase 1
  refine ⟨E, hE, X0, ?_⟩
  intro X ell m j q r hX hell hellMax hellEta hm hmsupport hj hjJ hq
    hSmooth hqlog hr
  have hBaseX : Xbase <= X := (le_max_left Xbase 1).trans hX
  have hOneX : 1 <= X := (le_max_right Xbase 1).trans hX
  have hXreal : (0 : Real) < X := by
    exact_mod_cast (Nat.zero_lt_one.trans_le hOneX)
  obtain ⟨hY0local, _hYone, hbudget, hsize⟩ :=
    hXbase X ell m j q hBaseX hell hellMax hellEta hm hmsupport hj hjJ hq hqlog
  exact hBlock (X : Real) hXreal
    (majorArcLogSubdivisionCount X D ell) m j q r
    (hj.trans hjJ) hm hj hjJ hq hSmooth hr hY0local.le hbudget hsize

end PrimesRestrictedDigits
