import PrimesRestrictedDigits.SieveDecomposition.RoughSmoothFactorization
import PrimesRestrictedDigits.PrimeNumberTheorem.MaynardBuchstab
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

/-!
# Monotonicity bridges for the repaired large-delta reduction

These are finite order arguments used after fixing `epsilon` in the repaired large branch of
Lemma 7.4.
-/

namespace PrimesRestrictedDigits

/- The strict predicate is antitone in its real threshold. -/
theorem strictSiftedCarrier_threshold_subset
    (C : Finset Nat) {z0 z1 : Real} (hz : z0 ≤ z1) :
    strictSiftedCarrier C z1 ⊆ strictSiftedCarrier C z0 := by
  intro n hn
  rw [mem_strictSiftedCarrier] at hn ⊢
  exact ⟨hn.1, strictRoughPredicate_antitone_threshold hz hn.2⟩

/- The corresponding cardinal comparison is kept in natural numbers. -/
theorem card_strictSiftedCarrier_threshold_le
    (C : Finset Nat) {z0 z1 : Real} (hz : z0 ≤ z1) :
    (strictSiftedCarrier C z1).card ≤
      (strictSiftedCarrier C z0).card := by
  exact Finset.card_le_card (strictSiftedCarrier_threshold_subset C hz)

/- The real-cast form avoids repeating cast monotonicity in aggregate proofs. -/
theorem card_strictSiftedCarrier_threshold_le_real
    (C : Finset Nat) {z0 z1 : Real} (hz : z0 ≤ z1) :
    ((strictSiftedCarrier C z1).card : Real) ≤
      ((strictSiftedCarrier C z0).card : Real) := by
  exact_mod_cast card_strictSiftedCarrier_threshold_le C hz

theorem strictSiftedCarrier_sieveDilation_threshold_subset
    (C : Finset Nat) (d : PNat) {z0 z1 : Real} (hz : z0 ≤ z1) :
    strictSiftedCarrier (sieveDilation C d) z1 ⊆
      strictSiftedCarrier (sieveDilation C d) z0 := by
  exact strictSiftedCarrier_threshold_subset (sieveDilation C d) hz

theorem card_strictSiftedCarrier_sieveDilation_threshold_le
    (C : Finset Nat) (d : PNat) {z0 z1 : Real} (hz : z0 ≤ z1) :
    ((strictSiftedCarrier (sieveDilation C d) z1).card : Real) ≤
      ((strictSiftedCarrier (sieveDilation C d) z0).card : Real) := by
  exact card_strictSiftedCarrier_threshold_le_real (sieveDilation C d) hz

/- The positive Maynard outer carrier is antitone in its rough threshold. -/
theorem maynardStrictRoughCarrier_threshold_subset
    {Y y0 y1 : Real} (hy : y0 ≤ y1) :
    maynardStrictRoughCarrier Y y1 ⊆
      maynardStrictRoughCarrier Y y0 := by
  intro n hn
  rw [mem_maynardStrictRoughCarrier] at hn ⊢
  refine ⟨hn.1, hn.2.1, ?_⟩
  intro p hp hpn
  exact hy.trans_lt (hn.2.2 p hp hpn)

/- At a fixed base `X>1`, increasing the delta parameter shrinks the outer
   strict-rough carrier.  The positivity premise makes the endpoint split
   explicit even though real-power monotonicity itself only needs `X>=1`. -/
theorem largeDelta_outer_carrier_subset
    {X alpha delta0 delta : Real}
    (hX : 1 < X) (hdelta0 : 0 < delta0) (hdelta : delta0 ≤ delta) :
    maynardStrictRoughCarrier (X ^ alpha) (X ^ delta) ⊆
      maynardStrictRoughCarrier (X ^ alpha) (X ^ delta0) := by
  have hdeltaPos : 0 < delta := hdelta0.trans_le hdelta
  have hpower : X ^ delta0 ≤ X ^ delta :=
    Real.rpow_le_rpow_of_exponent_le hX.le hdelta
  have _ : 0 < X ^ delta := Real.rpow_pos_of_pos (lt_trans zero_lt_one hX) delta
  exact maynardStrictRoughCarrier_threshold_subset hpower

/- Alias with the parameterized name used by some reduction drafts. -/
theorem maynardStrictRoughCarrier_rpow_subset
    {X alpha delta0 delta : Real}
    (hX : 1 < X) (hdelta0 : 0 < delta0) (hdelta : delta0 ≤ delta) :
    maynardStrictRoughCarrier (X ^ alpha) (X ^ delta) ⊆
      maynardStrictRoughCarrier (X ^ alpha) (X ^ delta0) :=
  largeDelta_outer_carrier_subset hX hdelta0 hdelta

/- Sign-safe pointwise comparison.  The second term is deliberately
   `lambda*b0`; a triangle estimate on the residual would not establish the
   one-sided source reduction. -/
theorem largeDelta_pointwise_abs_le
    {a0 ad b0 bd lambda : Real}
    (_ha0 : 0 ≤ a0) (had : 0 ≤ ad)
    (hb0 : 0 ≤ b0) (hbd : 0 ≤ bd)
    (had_le : ad ≤ a0) (hbd_le : bd ≤ b0)
    (hlambda : 0 ≤ lambda) :
    |ad - lambda * bd| ≤ |a0 - lambda * b0| + lambda * b0 := by
  have hprodD : 0 ≤ lambda * bd := mul_nonneg hlambda hbd
  have hprod0 : 0 ≤ lambda * b0 := mul_nonneg hlambda hb0
  have hprod_le : lambda * bd ≤ lambda * b0 :=
    mul_le_mul_of_nonneg_left hbd_le hlambda
  have hres : a0 - lambda * b0 ≤ |a0 - lambda * b0| :=
    le_abs_self _
  have hupper0 : a0 ≤ |a0 - lambda * b0| + lambda * b0 := by
    linarith
  have hupper : ad - lambda * bd ≤
      |a0 - lambda * b0| + lambda * b0 := by
    linarith
  have habs_nonneg : 0 ≤ |a0 - lambda * b0| := abs_nonneg _
  have hlower : -( |a0 - lambda * b0| + lambda * b0) ≤
      ad - lambda * bd := by
    linarith
  exact abs_le.mpr ⟨hlower, hupper⟩

/- The rapid exponential factor is monotone in the large-delta direction. -/
theorem largeDelta_rapid_factor_le
    {delta0 delta : Real} (hdelta0 : 0 < delta0)
    (hdelta : delta0 ≤ delta) :
    Real.exp (-(delta0 ^ (-(2 / 3 : Real)))) ≤
      Real.exp (-(delta ^ (-(2 / 3 : Real)))) := by
  have hdeltaPos : 0 < delta := hdelta0.trans_le hdelta
  have hpow : delta ^ (-(2 / 3 : Real)) ≤
      delta0 ^ (-(2 / 3 : Real)) := by
    exact Real.rpow_le_rpow_of_nonpos hdelta0 hdelta (by norm_num)
  apply Real.exp_le_exp.mpr
  exact neg_le_neg hpow

/- Division by the positive logarithm preserves the same comparison. -/
theorem largeDelta_rapid_factor_div_log_le
    {X delta0 delta : Real} (hX : 1 < X)
    (hdelta0 : 0 < delta0) (hdelta : delta0 ≤ delta) :
    Real.exp (-(delta0 ^ (-(2 / 3 : Real)))) / Real.log X ≤
      Real.exp (-(delta ^ (-(2 / 3 : Real)))) / Real.log X := by
  apply (div_le_div_iff_of_pos_right (Real.log_pos hX)).mpr
  exact largeDelta_rapid_factor_le hdelta0 hdelta

end PrimesRestrictedDigits
