import PrimesRestrictedDigits.Fourier.LInfLocal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log

/-!
# Rational orbits and repaired decimal blocks

This file supplies the arithmetic part of the repaired proof of
`MAYNARD-PRD-PUBLISHED`, Lemma 10.1, pp. 169--170.  Natural index blocks
replace the source's false literal claim about arbitrary real intervals.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- Enough consecutive decimal shifts to exceed a positive denominator. -/
def lInfBlockLength (q : Nat) : Nat :=
  Nat.log 10 q + 2

/-- The number of disjoint full blocks available among indices through `k/3`. -/
def lInfBlockCount (k q : Nat) : Nat :=
  (k / 3 + 1) / lInfBlockLength q

private theorem nearestIntegerDistance_nat_div_lower
    {m q : Nat} (hq : 0 < q) (hnot : ¬q ∣ m) :
    1 / (q : Real) ≤ nearestIntegerDistance ((m : Real) / q) := by
  have hmodPos : 0 < m % q :=
    Nat.pos_of_ne_zero fun hzero => hnot (Nat.dvd_of_mod_eq_zero hzero)
  have hmodLt : m % q < q := Nat.mod_lt m hq
  have hmin : 1 ≤ min (m % q) (q - m % q) := by omega
  have hnorm := AddCircle.norm_div_natCast (p := (1 : Real))
    (m := m) (n := q)
  rw [nearestIntegerDistance_eq_norm_unitAddCircle]
  simp only [mul_one, one_mul] at hnorm
  rw [hnorm]
  exact (div_le_div_iff_of_pos_right (show (0 : Real) < q by exact_mod_cast hq)).2
    (by exact_mod_cast hmin)

/-- Powers of ten cannot cancel the nontrivial denominator factor coprime to
ten, even for a signed numerator. -/
theorem nearestIntegerDistance_ten_pow_rational_lower
    {q q1 q2 i : Nat} {a : Int}
    (hq : q = q1 * q2) (hq2 : 0 < q2) (hq1 : 1 < q1)
    (hq10 : Nat.Coprime q1 10) (haq : Nat.Coprime a.natAbs q) :
    1 / (q : Real) ≤
      nearestIntegerDistance ((10 : Real) ^ i * (a : Real) / q) := by
  have hq1dvd : q1 ∣ q := by
    rw [hq]
    exact dvd_mul_right _ _
  have hq1a : Nat.Coprime q1 a.natAbs :=
    (haq.of_dvd_right hq1dvd).symm
  have hq1pow : Nat.Coprime q1 (10 ^ i) := hq10.pow_right i
  have hq1prod : Nat.Coprime q1 (10 ^ i * a.natAbs) :=
    hq1pow.mul_right hq1a
  have hnot : ¬q ∣ 10 ^ i * a.natAbs := by
    intro hqdiv
    have hq1div : q1 ∣ 10 ^ i * a.natAbs := hq1dvd.trans hqdiv
    exact (Nat.ne_of_gt hq1) (hq1prod.eq_one_of_dvd hq1div)
  have hqpos : 0 < q := by
    have hq1pos : 0 < q1 := lt_trans Nat.zero_lt_one hq1
    simp [hq, hq1pos, hq2]
  have hlower := nearestIntegerDistance_nat_div_lower hqpos hnot
  rcases Int.natAbs_eq a with ha | ha
  · rw [ha]
    simpa [Nat.cast_mul] using hlower
  · rw [ha, Int.cast_neg, Int.cast_natCast]
    have hphase :
        (10 : Real) ^ i * -(a.natAbs : Real) / q =
          -(((10 ^ i * a.natAbs : Nat) : Real) / q) := by
      push_cast
      ring
    rw [hphase, nearestIntegerDistance_neg]
    simpa [Nat.cast_mul] using hlower

private theorem ten_pow_le_cubeRoot {i k : Nat} (hi : 3 * i ≤ k) :
    (10 : Real) ^ i ≤
      (((10 ^ k : Nat) : Real) ^ (1 / 3 : Real)) := by
  rw [show (1 / 3 : Real) = (3 : Real)⁻¹ by norm_num]
  rw [Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity) (by norm_num)]
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  calc
    ((10 : Real) ^ i) ^ (3 : Real) = ((10 : Real) ^ i) ^ (3 : Nat) :=
      Real.rpow_natCast _ _
    _ = (10 : Real) ^ (i * 3) := (pow_mul _ _ _).symm
    _ ≤ (10 : Real) ^ k := pow_le_pow_right₀ (by norm_num) (by omega)

private theorem perturbation_scale
    {k q i : Nat} {eta : Real} (hi : 3 * i ≤ k) (hq : 0 < q)
    (hqY : (q : Real) <
      (((10 ^ k : Nat) : Real) ^ (1 / 3 : Real)))
    (heta : |eta| <
      (((10 ^ k : Nat) : Real) ^ (-2 / 3 : Real)) / 2) :
    |(10 : Real) ^ i * eta| < 1 / (2 * (q : Real)) := by
  let Y : Real := ((10 ^ k : Nat) : Real)
  let R : Real := Y ^ (1 / 3 : Real)
  have hY : 0 < Y := by positivity
  have hR : 0 < R := Real.rpow_pos_of_pos hY _
  have hqReal : 0 < (q : Real) := by exact_mod_cast hq
  have hqR : (q : Real) < R := by simpa [Y, R] using hqY
  have hpow : (10 : Real) ^ i ≤ R := by
    simpa [Y, R] using ten_pow_le_cubeRoot hi
  have hidentity : R * Y ^ (-2 / 3 : Real) = 1 / R := by
    calc
      R * Y ^ (-2 / 3 : Real) =
          Y ^ ((1 / 3 : Real) + (-2 / 3 : Real)) := by
        dsimp [R]
        exact (Real.rpow_add hY _ _).symm
      _ = Y ^ (-(1 / 3 : Real)) := by ring_nf
      _ = (Y ^ (1 / 3 : Real))⁻¹ := Real.rpow_neg hY.le _
      _ = 1 / R := by dsimp [R]; simp [one_div]
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (10 : Real) ^ i)]
  calc
    (10 : Real) ^ i * |eta| <
        (10 : Real) ^ i * (Y ^ (-2 / 3 : Real) / 2) := by
      exact mul_lt_mul_of_pos_left (by simpa [Y] using heta) (by positivity)
    _ ≤ R * (Y ^ (-2 / 3 : Real) / 2) := by
      exact mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = (1 / R) / 2 := by rw [← hidentity]; ring
    _ < (1 / (q : Real)) / 2 := by
      exact (div_lt_div_iff_of_pos_right (by norm_num : (0 : Real) < 2)).2
        (one_div_lt_one_div_of_lt hqReal hqR)
    _ = 1 / (2 * (q : Real)) := by ring

/-- The source scale hypotheses leave a strict `1/(2q)` nearest-integer
margin at every index through `k/3`. -/
theorem nearestIntegerDistance_perturbed_rational_lower
    {k q q1 q2 i : Nat} {a : Int} {eta : Real}
    (hi : 3 * i ≤ k) (hq : q = q1 * q2) (hq2 : 0 < q2)
    (hq1 : 1 < q1) (hq10 : Nat.Coprime q1 10)
    (haq : Nat.Coprime a.natAbs q)
    (hqY : (q : Real) <
      (((10 ^ k : Nat) : Real) ^ (1 / 3 : Real)))
    (heta : |eta| <
      (((10 ^ k : Nat) : Real) ^ (-2 / 3 : Real)) / 2) :
    1 / (2 * (q : Real)) <
      nearestIntegerDistance
        ((10 : Real) ^ i * ((a : Real) / q + eta)) := by
  have hrational := nearestIntegerDistance_ten_pow_rational_lower
    hq hq2 hq1 hq10 haq (i := i)
  have hqNat : 0 < q := by
    have hq1pos : 0 < q1 := lt_trans Nat.zero_lt_one hq1
    simp [hq, hq1pos, hq2]
  have herror := perturbation_scale hi hqNat hqY heta
  have hperturb := nearestIntegerDistance_perturbation_lower
    ((10 : Real) ^ i * (a : Real) / q) ((10 : Real) ^ i * eta)
  rw [show (10 : Real) ^ i * (a : Real) / q + (10 : Real) ^ i * eta =
      (10 : Real) ^ i * ((a : Real) / q + eta) by ring] at hperturb
  have hqReal : 0 < (q : Real) := by exact_mod_cast hqNat
  calc
    1 / (2 * (q : Real)) < 1 / (q : Real) - |(10 : Real) ^ i * eta| := by
      rw [show 1 / (q : Real) = 2 * (1 / (2 * (q : Real))) by field_simp]
      linarith
    _ ≤ nearestIntegerDistance ((10 : Real) ^ i * (a : Real) / q) -
        |(10 : Real) ^ i * eta| := sub_le_sub_right hrational _
    _ ≤ nearestIntegerDistance
        ((10 : Real) ^ i * ((a : Real) / q + eta)) := hperturb

private theorem block_index_lt_countedRange {k q j r : Nat}
    (hj : j < lInfBlockCount k q) (hr : r < lInfBlockLength q) :
    j * lInfBlockLength q + r < k / 3 + 1 := by
  have hjle : j + 1 ≤ lInfBlockCount k q := by omega
  have hmul : (j + 1) * lInfBlockLength q ≤
      lInfBlockCount k q * lInfBlockLength q :=
    Nat.mul_le_mul_right _ hjle
  have hdiv : lInfBlockCount k q * lInfBlockLength q ≤ k / 3 + 1 :=
    Nat.div_mul_le_self _ _
  have hrange : j * lInfBlockLength q + r <
      (j + 1) * lInfBlockLength q := by
    calc
      j * lInfBlockLength q + r <
          j * lInfBlockLength q + lInfBlockLength q := Nat.add_lt_add_left hr _
      _ = (j + 1) * lInfBlockLength q := by rw [Nat.add_mul]; simp
  omega

private theorem block_index_le_third {k q j r : Nat}
    (hj : j < lInfBlockCount k q) (hr : r < lInfBlockLength q) :
    j * lInfBlockLength q + r ≤ k / 3 := by
  have := block_index_lt_countedRange hj hr
  omega

private theorem exists_large_in_block
    (u : Nat → Real) {k q j : Nat} (hq : 0 < q)
    (hj : j < lInfBlockCount k q)
    (hstep : ∀ i : Nat, u i < 1 / 20 → u (i + 1) = 10 * u i)
    (hlower : ∀ i : Nat, i ≤ k / 3 → 1 / (2 * (q : Real)) < u i) :
    ∃ r : Nat, r < lInfBlockLength q ∧
      1 / 200 < u (j * lInfBlockLength q + r) := by
  by_contra! hall
  have hpower : ∀ r : Nat, r < lInfBlockLength q →
      u (j * lInfBlockLength q + r) =
        (10 : Real) ^ r * u (j * lInfBlockLength q) := by
    intro r hr
    induction r with
    | zero => simp
    | succ r ih =>
        have hrB : r < lInfBlockLength q := lt_trans (Nat.lt_succ_self r) hr
        have hsmall : u (j * lInfBlockLength q + r) < 1 / 20 :=
          (hall r hrB).trans_lt (by norm_num)
        calc
          u (j * lInfBlockLength q + (r + 1)) =
              u ((j * lInfBlockLength q + r) + 1) := by congr 1
          _ = 10 * u (j * lInfBlockLength q + r) := hstep _ hsmall
          _ = 10 * ((10 : Real) ^ r * u (j * lInfBlockLength q)) := by
            rw [ih hrB]
          _ = (10 : Real) ^ (r + 1) * u (j * lInfBlockLength q) := by
            rw [pow_succ']; ring
  have hBpos : 0 < lInfBlockLength q := by simp [lInfBlockLength]
  have hstartLower : 1 / (2 * (q : Real)) <
      u (j * lInfBlockLength q) := by
    simpa using hlower _ (block_index_le_third hj hBpos)
  have hqpowNat : q < 10 ^ (Nat.log 10 q + 1) := by
    simpa only [Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self (by norm_num : 1 < 10) q
  have hqpow : (q : Real) < (10 : Real) ^ (Nat.log 10 q + 1) := by
    exact_mod_cast hqpowNat
  have hqReal : (0 : Real) < q := by exact_mod_cast hq
  have hpowPos : (0 : Real) < (10 : Real) ^ (Nat.log 10 q + 1) := by
    positivity
  have hmulLower :
      (10 : Real) ^ (Nat.log 10 q + 1) / (2 * (q : Real)) <
        (10 : Real) ^ (Nat.log 10 q + 1) *
          u (j * lInfBlockLength q) := by
    calc
      (10 : Real) ^ (Nat.log 10 q + 1) / (2 * (q : Real)) =
          (10 : Real) ^ (Nat.log 10 q + 1) * (1 / (2 * (q : Real))) := by
        simp [div_eq_mul_inv]
      _ < _ := mul_lt_mul_of_pos_left hstartLower hpowPos
  have hhalf :
      (1 : Real) / 2 <
        (10 : Real) ^ (Nat.log 10 q + 1) / (2 * (q : Real)) := by
    apply (div_lt_div_iff₀ (by norm_num : (0 : Real) < 2)
      (by positivity : (0 : Real) < 2 * (q : Real))).2
    nlinarith
  have hfinalLarge :
      1 / 2 < u (j * lInfBlockLength q + (Nat.log 10 q + 1)) := by
    rw [hpower _ (by simp [lInfBlockLength])]
    exact hhalf.trans hmulLower
  have hfinalSmall := hall (Nat.log 10 q + 1) (by simp [lInfBlockLength])
  linarith

/-- One selected spike per disjoint block gives a lower bound for the full
squared orbit sum. -/
theorem lInfBlockCount_div_le_sum_sq
    (u : Nat → Real) {k q : Nat} (hq : 0 < q)
    (hstep : ∀ i : Nat, u i < 1 / 20 → u (i + 1) = 10 * u i)
    (hlower : ∀ i : Nat, i ≤ k / 3 → 1 / (2 * (q : Real)) < u i) :
    (lInfBlockCount k q : Real) / 40000 ≤ ∑ i : Fin k, u i ^ 2 := by
  choose offset hoffset hlarge using fun j : Fin (lInfBlockCount k q) =>
    exists_large_in_block u hq j.isLt hstep hlower
  have hselected_lt (j : Fin (lInfBlockCount k q)) :
      j.val * lInfBlockLength q + offset j < k := by
    have hthird : j.val * lInfBlockLength q + offset j ≤ k / 3 :=
      block_index_le_third j.isLt (hoffset j)
    have hcountPos : 0 < lInfBlockCount k q := Nat.zero_lt_of_lt j.isLt
    have hone : 1 ≤ lInfBlockCount k q := hcountPos
    have hBpos : 0 < lInfBlockLength q := by simp [lInfBlockLength]
    have hBle : lInfBlockLength q ≤ k / 3 + 1 := by
      have hmul := (Nat.le_div_iff_mul_le hBpos).1 hone
      simpa [lInfBlockCount] using hmul
    have hBtwo : 2 ≤ lInfBlockLength q := by simp [lInfBlockLength]
    have hkpos : 0 < k := by omega
    have hthirdlt : k / 3 < k := Nat.div_lt_self hkpos (by norm_num)
    exact hthird.trans_lt hthirdlt
  let selected : Fin (lInfBlockCount k q) → Fin k := fun j =>
    ⟨j.val * lInfBlockLength q + offset j, hselected_lt j⟩
  have hquotient (j : Fin (lInfBlockCount k q)) :
      (selected j).val / lInfBlockLength q = j.val := by
    change (j.val * lInfBlockLength q + offset j) / lInfBlockLength q = j.val
    calc
      (j.val * lInfBlockLength q + offset j) / lInfBlockLength q =
          (offset j + lInfBlockLength q * j.val) / lInfBlockLength q := by
        simp [Nat.mul_comm, Nat.add_comm]
      _ = offset j / lInfBlockLength q + j.val :=
        Nat.add_mul_div_left _ _ (by simp [lInfBlockLength])
      _ = j.val := by rw [Nat.div_eq_of_lt (hoffset j)]; simp
  have hselectedInjective : Function.Injective selected := by
    intro a b hab
    apply Fin.ext
    calc
      a.val = (selected a).val / lInfBlockLength q := (hquotient a).symm
      _ = (selected b).val / lInfBlockLength q := by rw [hab]
      _ = b.val := hquotient b
  have hpoint (j : Fin (lInfBlockCount k q)) :
      (1 : Real) / 40000 ≤ u (selected j).val ^ 2 := by
    have hjlarge : (1 : Real) / 200 < u (selected j).val := by
      simpa [selected] using hlarge j
    nlinarith [sq_nonneg (u (selected j).val - 1 / 200)]
  calc
    (lInfBlockCount k q : Real) / 40000 =
        ∑ _j : Fin (lInfBlockCount k q), (1 : Real) / 40000 := by
      simp [div_eq_mul_inv]
    _ ≤ ∑ j : Fin (lInfBlockCount k q), u (selected j).val ^ 2 := by
      exact Finset.sum_le_sum fun j _ => hpoint j
    _ = ∑ i ∈ Finset.univ.image selected, u i.val ^ 2 := by
      rw [Finset.sum_image hselectedInjective.injOn]
    _ ≤ ∑ i : Fin k, u i.val ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro i _ _
      positivity

end PrimesRestrictedDigits
