import Waring.Dickson.Basic

/-!
# Dickson's finite interval ascent

This file proves an inclusive-interval form of Dickson's Theorem 10
[DICKSON1933, pp. 709-710].  Its essential arithmetic input is the
monotonicity of the gaps between consecutive positive-exponent powers.
-/

namespace Waring

open scoped BigOperators
open Statement

/-- For a positive exponent, the gaps between consecutive natural powers are
nondecreasing as the base increases. -/
theorem pow_succ_sub_pow_mono {k a b : Nat} (hk : 0 < k) (hab : a ≤ b) :
    (a + 1) ^ k - a ^ k ≤ (b + 1) ^ k - b ^ k := by
  cases k with
  | zero => simp at hk
  | succ k =>
      have expand (n : Nat) :
          (n + 1) ^ (k + 1) - n ^ (k + 1) =
            ∑ i ∈ Finset.range (k + 1), n ^ i * (k + 1).choose i := by
        have hpow :
            (n + 1) ^ (k + 1) =
              (∑ i ∈ Finset.range (k + 1), n ^ i * (k + 1).choose i) +
                n ^ (k + 1) := by
          rw [add_pow, Finset.sum_range_succ]
          simp
        omega
      rw [expand a, expand b]
      exact Finset.sum_le_sum fun i _ ↦
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hab i)

/-- Inclusive-interval form of Dickson's Theorem 10: if `[lower, upper]`
is represented with `slots` powers and the final consecutive-power gap is
shorter than that interval, one more power covers through
`upper + (m + 1) ^ k`.

The hypotheses expose the strict endpoint order and the source's strict gap
condition.  Existing targets are padded with the appended base zero, while
the extension is covered by the overlapping translates by `j ^ k` for
`j = 1, ..., m + 1`.
-/
theorem representsOn_succ_of_powerGap {k slots lower upper m : Nat}
    (hk : 0 < k) (hlowerUpper : lower < upper)
    (hbase : RepresentsOn k slots lower upper)
    (hgap : (m + 1) ^ k - m ^ k < upper - lower) :
    RepresentsOn k (slots + 1) lower (upper + (m + 1) ^ k) := by
  have hcover : ∀ j : Nat, j ≤ m + 1 →
      RepresentsOn k (slots + 1) lower (upper + j ^ k) := by
    intro j hj
    induction j with
    | zero =>
        intro n hnLower hnUpper
        have hnUpper' : n ≤ upper := by simpa [hk] using hnUpper
        simpa [hk] using HasPowerSumRepresentation.addPower
          (hbase n hnLower hnUpper') 0
    | succ j ih =>
        have hjm : j ≤ m := by omega
        have hprevious :
            RepresentsOn k (slots + 1) lower (upper + j ^ k) :=
          ih (by omega)
        intro n hnLower hnUpper
        by_cases hnPrevious : n ≤ upper + j ^ k
        · exact hprevious n hnLower hnPrevious
        · have hpowMono : j ^ k ≤ (j + 1) ^ k :=
            Nat.pow_le_pow_left (Nat.le_succ j) k
          have hgapAtJ : (j + 1) ^ k - j ^ k < upper - lower :=
            (pow_succ_sub_pow_mono hk hjm).trans_lt hgap
          have hoverlap : lower + (j + 1) ^ k ≤ upper + j ^ k := by
            omega
          have hstart : lower + (j + 1) ^ k ≤ n :=
            hoverlap.trans (Nat.le_of_lt (Nat.lt_of_not_ge hnPrevious))
          have hpowerLe : (j + 1) ^ k ≤ n :=
            (Nat.le_add_left ((j + 1) ^ k) lower).trans hstart
          have hremLower : lower ≤ n - (j + 1) ^ k :=
            Nat.le_sub_of_add_le hstart
          have hremUpper : n - (j + 1) ^ k ≤ upper := by
            rw [Nat.sub_le_iff_le_add]
            simpa [Nat.add_comm] using hnUpper
          have hremRep :
              HasPowerSumRepresentation k slots (n - (j + 1) ^ k) :=
            hbase (n - (j + 1) ^ k) hremLower hremUpper
          simpa [Nat.sub_add_cancel hpowerLe] using
            HasPowerSumRepresentation.addPower hremRep (j + 1)
  exact hcover (m + 1) le_rfl

end Waring
