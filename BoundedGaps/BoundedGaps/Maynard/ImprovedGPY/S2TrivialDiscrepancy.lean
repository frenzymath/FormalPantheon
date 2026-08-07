import BoundedGaps.Maynard.ImprovedGPY.S2WeightedDistribution

noncomputable section

/-!
# A trivial pointwise progression-discrepancy bound

Maynard2013v3, in the Cauchy--Schwarz estimate for the error in
`lmm:S2Expression1` (source line 368), uses `E(N,q) << N / phi(q)`.  This file
proves an explicit cumulative-endpoint version with constant three.
-/

namespace BoundedGaps.Maynard

open scoped ArithmeticFunction.omega BigOperators

theorem primeCountUpTo_le_modEqCard (x q a : ℕ) :
    primeCountUpTo x q a ≤
      ((Finset.range (x + 1)).filter (fun n => n ≡ a [MOD q])).card := by
  unfold primeCountUpTo
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, hn.2.2⟩

theorem cast_primeCountUpTo_le_div_add_one
    (x q a : ℕ) (hq : 0 < q) :
    (primeCountUpTo x q a : ℝ) ≤
      ((x + 1 : ℕ) : ℝ) / q + 1 := by
  have hcount := primeCountUpTo_le_modEqCard x q a
  have hcountR : (primeCountUpTo x q a : ℝ) ≤
      ((((Finset.range (x + 1)).filter
        (fun n => n ≡ a [MOD q])).card : ℕ) : ℝ) := by
    exact_mod_cast hcount
  have hdecomp := intervalModEq_card_eq_length_div_add_error
    0 (x + 1) q a
  have herr := intervalModEqCardError_abs_le_one
    0 (x + 1) q a (by omega) hq
  have herrUpper := (abs_le.mp herr).2
  calc
    (primeCountUpTo x q a : ℝ) ≤
        ((((Finset.range (x + 1)).filter
          (fun n => n ≡ a [MOD q])).card : ℕ) : ℝ) := hcountR
    _ = (((x + 1 : ℕ) : ℝ) - 0) / q +
        intervalModEqCardError 0 (x + 1) q a := by
      simpa [Nat.Ico_zero_eq_range] using hdecomp
    _ ≤ ((x + 1 : ℕ) : ℝ) / q + 1 := by
      norm_num
      linarith

theorem primeCountTotal_le_succ (x : ℕ) :
    primeCountTotal x ≤ x + 1 := by
  unfold primeCountTotal Nat.primeCounting Nat.primeCounting'
  exact Nat.count_le Nat.Prime

theorem progressionDiscrepancy_le_three_mul_div
    {x q a : ℕ} (hq : 0 < q) (hqx : q ≤ x + 1) :
    progressionDiscrepancy x q a ≤
      3 * ((x + 1 : ℕ) : ℝ) / (Nat.totient q : ℝ) := by
  have hφposNat : 0 < Nat.totient q := Nat.totient_pos.mpr hq
  have hφpos : (0 : ℝ) < Nat.totient q := by exact_mod_cast hφposNat
  have hφqNat : Nat.totient q ≤ q := Nat.totient_le q
  have hφq : (Nat.totient q : ℝ) ≤ q := by exact_mod_cast hφqNat
  have hφx : (Nat.totient q : ℝ) ≤ ((x + 1 : ℕ) : ℝ) := by
    exact_mod_cast hφqNat.trans hqx
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hbase : (0 : ℝ) ≤ ((x + 1 : ℕ) : ℝ) := by positivity
  have hdiv : ((x + 1 : ℕ) : ℝ) / q ≤
      ((x + 1 : ℕ) : ℝ) / (Nat.totient q : ℝ) := by
    exact div_le_div₀ hbase le_rfl hφpos hφq
  have hone : (1 : ℝ) ≤
      ((x + 1 : ℕ) : ℝ) / (Nat.totient q : ℝ) :=
    (one_le_div₀ hφpos).mpr hφx
  have hprogress := cast_primeCountUpTo_le_div_add_one x q a hq
  have htotalNat := primeCountTotal_le_succ x
  have htotal : (primeCountTotal x : ℝ) / (Nat.totient q : ℝ) ≤
      ((x + 1 : ℕ) : ℝ) / (Nat.totient q : ℝ) := by
    apply (div_le_div_iff₀ hφpos hφpos).mpr
    nlinarith [show (primeCountTotal x : ℝ) ≤ ((x + 1 : ℕ) : ℝ) by
      exact_mod_cast htotalNat]
  have hprogress_nonneg : (0 : ℝ) ≤ primeCountUpTo x q a := by positivity
  have htotal_nonneg : (0 : ℝ) ≤
      (primeCountTotal x : ℝ) / (Nat.totient q : ℝ) := by positivity
  have hthree : 3 * ((x + 1 : ℕ) : ℝ) / (Nat.totient q : ℝ) =
      3 * (((x + 1 : ℕ) : ℝ) / (Nat.totient q : ℝ)) := by ring
  unfold progressionDiscrepancy
  rw [hthree, abs_sub_le_iff]
  constructor <;> nlinarith

theorem maxProgressionDiscrepancy_le_three_mul_div
    {x q : ℕ} (hq : 0 < q) (hqx : q ≤ x + 1) :
    maxProgressionDiscrepancy x q ≤
      3 * ((x + 1 : ℕ) : ℝ) / (Nat.totient q : ℝ) := by
  unfold maxProgressionDiscrepancy
  simp only [dif_pos hq]
  apply Finset.sup'_le
  intro a ha
  exact progressionDiscrepancy_le_three_mul_div hq hqx

theorem PrimeLevelWitness.sum_tauPow_mul_maxProgressionDiscrepancy_explicit
    {θ A C : ℝ} {X₀ x d Q : ℕ}
    (hw : PrimeLevelWitness θ A C X₀) (hx : X₀ ≤ x)
    (S : Finset ℕ)
    (hSQ : S ⊆ Finset.Icc 1 Q)
    (hsq : ∀ q ∈ S, Squarefree q)
    (hQx : Q ≤ x + 1)
    (hcut : S ⊆ Finset.Icc 1 (modulusCutoff θ x)) :
    (∑ q ∈ S,
        ((d ^ ω q : ℕ) : ℝ) * maxProgressionDiscrepancy x q) ≤
      Real.sqrt
          ((3 : ℝ) * ((x + 1 : ℕ) : ℝ) *
            (1 + Real.log Q) ^ (2 * d ^ 2)) *
        Real.sqrt
          (C * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) A) := by
  apply hw.sum_tauPow_mul_maxProgressionDiscrepancy hx
    (X := (3 : ℝ) * ((x + 1 : ℕ) : ℝ)) (S := S)
  · positivity
  · exact hSQ
  · exact hsq
  · exact hcut
  · intro q hq
    have hqData := Finset.mem_Icc.mp (hSQ hq)
    have hqpos : 0 < q := zero_lt_one.trans_le hqData.1
    have hqx : q ≤ x + 1 := hqData.2.trans hQx
    exact maxProgressionDiscrepancy_le_three_mul_div hqpos hqx

end BoundedGaps.Maynard
