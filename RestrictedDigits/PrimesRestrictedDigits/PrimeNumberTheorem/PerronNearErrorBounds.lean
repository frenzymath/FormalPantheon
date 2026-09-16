import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.Bounds
import PrimesRestrictedDigits.PrimeNumberTheorem.PerronSummableSupport

/-!
# Bounds for the near-diagonal Perron error

This proves the discrete near-diagonal estimate used after Eq. (6.16) in
`MONTGOMERY-VAUGHAN-MNT-I`, Chapter 6, pp. 180--181. The proof makes the
source's nearest-integer argument precise by retaining both indices adjacent
to the floor of the real cutoff.
-/

namespace PrimesRestrictedDigits

private theorem perronNearError_nonneg
    {x T : Real} (hx : 0 < x) (hT : 0 < T) (n : Nat) :
    0 <= perronNearError x T n := by
  rw [perronNearError]
  split_ifs with h
  · apply le_min (by norm_num)
    have hdiff : 0 < |x - (n : Real)| :=
      abs_pos.mpr (sub_ne_zero.mpr h.2.2)
    positivity
  · exact le_rfl

private theorem perronNearError_le_one (x T : Real) (n : Nat) :
    perronNearError x T n <= 1 := by
  rw [perronNearError]
  split_ifs
  · exact min_le_left _ _
  · norm_num

private theorem perronNearError_hasFiniteSupport (x T : Real) :
    Function.HasFiniteSupport (perronNearError x T) := by
  apply (Set.finite_lt_nat (Nat.ceil (2 * x))).subset
  intro n hn
  change perronNearError x T n ≠ 0 at hn
  change n < Nat.ceil (2 * x)
  by_contra hnbound
  have hn_ge : Nat.ceil (2 * x) <= n := Nat.le_of_not_gt hnbound
  have hx_le_n : 2 * x <= (n : Real) :=
    (Nat.le_ceil (2 * x)).trans (by exact_mod_cast hn_ge)
  apply hn
  rw [perronNearError, if_neg]
  intro h
  exact (not_lt_of_ge hx_le_n) h.2.1

private theorem perronNearError_below_floor_le
    {x T : Real} (hx : 0 < x) (hT : 0 < T) {n : Nat}
    (hn : n < Nat.floor x) :
    perronNearError x T n <=
      (x / T) * (((Nat.floor x - n : Nat) : Real)⁻¹) := by
  have hfloor : ((Nat.floor x : Nat) : Real) <= x := Nat.floor_le hx.le
  have hnle : n <= Nat.floor x := hn.le
  have hnFloor : (n : Real) <= (Nat.floor x : Real) := by
    exact_mod_cast hnle
  have hkNat : 0 < Nat.floor x - n := Nat.sub_pos_of_lt hn
  have hk : (0 : Real) < (Nat.floor x - n : Nat) := by
    exact_mod_cast hkNat
  have hcast : ((Nat.floor x - n : Nat) : Real) =
      (Nat.floor x : Real) - (n : Real) := by
    rw [Nat.cast_sub hnle]
  have hdiffNonneg : 0 <= x - (n : Real) :=
    sub_nonneg.mpr (hnFloor.trans hfloor)
  have habs : |x - (n : Real)| = x - (n : Real) :=
    abs_of_nonneg hdiffNonneg
  have hdiff : ((Nat.floor x - n : Nat) : Real) <=
      |x - (n : Real)| := by
    rw [hcast, habs]
    linarith
  rw [perronNearError]
  split_ifs
  · calc
      min 1 (x / (T * |x - (n : Real)|)) <=
          x / (T * |x - (n : Real)|) := min_le_right _ _
      _ <= x / (T * ((Nat.floor x - n : Nat) : Real)) := by
        exact div_le_div_of_nonneg_left hx.le (mul_pos hT hk)
          (mul_le_mul_of_nonneg_left hdiff hT.le)
      _ = (x / T) * (((Nat.floor x - n : Nat) : Real)⁻¹) := by
        field_simp
  · positivity

private theorem perronNearError_above_floor_succ_le
    {x T : Real} (hx : 0 < x) (hT : 0 < T) {n : Nat}
    (hn : Nat.floor x + 1 < n) :
    perronNearError x T n <=
      (x / T) * (((n - (Nat.floor x + 1) : Nat) : Real)⁻¹) := by
  have hxlt : x < (Nat.floor x : Real) + 1 := Nat.lt_floor_add_one x
  have hnle : Nat.floor x + 1 <= n := hn.le
  have hkNat : 0 < n - (Nat.floor x + 1) := Nat.sub_pos_of_lt hn
  have hk : (0 : Real) < (n - (Nat.floor x + 1) : Nat) := by
    exact_mod_cast hkNat
  have hcast : ((n - (Nat.floor x + 1) : Nat) : Real) =
      (n : Real) - ((Nat.floor x + 1 : Nat) : Real) := by
    rw [Nat.cast_sub hnle]
  have hdiffNonpos : x - (n : Real) <= 0 := by
    have hmn : (Nat.floor x : Real) + 1 <= (n : Real) := by
      exact_mod_cast hnle
    linarith
  have habs : |x - (n : Real)| = (n : Real) - x := by
    rw [abs_of_nonpos hdiffNonpos]
    ring
  have hdiff : ((n - (Nat.floor x + 1) : Nat) : Real) <=
      |x - (n : Real)| := by
    rw [hcast, habs]
    norm_num at hxlt ⊢
    linarith
  rw [perronNearError]
  split_ifs
  · calc
      min 1 (x / (T * |x - (n : Real)|)) <=
          x / (T * |x - (n : Real)|) := min_le_right _ _
      _ <= x / (T * ((n - (Nat.floor x + 1) : Nat) : Real)) := by
        exact div_le_div_of_nonneg_left hx.le (mul_pos hT hk)
          (mul_le_mul_of_nonneg_left hdiff hT.le)
      _ = (x / T) * (((n - (Nat.floor x + 1) : Nat) : Real)⁻¹) := by
        field_simp
  · positivity

private theorem sum_range_inv_floor_sub (m : Nat) :
    (∑ n ∈ Finset.range m, (((m - n : Nat) : Real)⁻¹)) =
      (harmonic m : Real) := by
  have hreflect := Finset.sum_Ico_reflect
    (fun k : Nat => ((k : Real)⁻¹)) 0 (m := m) (n := m)
    (Nat.le_succ m)
  simp only [Nat.Ico_zero_eq_range, Nat.add_sub_cancel_left,
    Nat.sub_zero] at hreflect
  rw [Finset.Ico_add_one_right_eq_Icc] at hreflect
  simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast]
  exact hreflect

private theorem sum_Ico_inv_sub_floor_succ (m N : Nat) :
    (∑ n ∈ Finset.Ico (m + 2) N,
      (((n - (m + 1) : Nat) : Real)⁻¹)) =
      (harmonic (N - (m + 2)) : Real) := by
  rw [Finset.sum_Ico_eq_sum_range]
  simp_rw [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  apply Finset.sum_congr rfl
  intro k _
  congr 2
  omega

private theorem harmonic_mono_cast {r N : Nat} (h : r <= N) :
    (harmonic r : Real) <= (harmonic N : Real) := by
  simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    rw [Finset.mem_Icc] at hk ⊢
    exact ⟨hk.1, hk.2.trans h⟩
  · intro k _ _
    positivity

/-- The scalar strict near-diagonal Perron error has the explicit harmonic
bound used after `MONTGOMERY-VAUGHAN-MNT-I`, Eq. (6.16), pp. 180--181. -/
theorem tsum_perronNearError_le
    {x T : Real} (hx : 4 <= x) (hT : 0 < T) (hTx : T <= x) :
    tsum (fun n : Nat => perronNearError x T n) <=
      8 * x * Real.log x / T := by
  let f : Nat -> Real := perronNearError x T
  let m : Nat := Nat.floor x
  let N : Nat := Nat.ceil (2 * x)
  have hxPos : 0 < x := by linarith
  have hFloor : (m : Real) <= x := by
    simpa [m] using Nat.floor_le hxPos.le
  have hCeil : 2 * x <= (N : Real) := by
    simpa [N] using Nat.le_ceil (2 * x)
  have hm2N : m + 2 <= N := by
    have hcast : (m : Real) + 2 <= (N : Real) := by nlinarith
    exact_mod_cast hcast
  have hmN : m <= N := (Nat.le_add_right m 2).trans hm2N
  have hSupport : ∀ n : Nat, n ∉ Finset.range N -> f n = 0 := by
    intro n hn
    have hnN : N <= n := Nat.le_of_not_gt (by simpa using hn)
    have hnCast : (N : Real) <= (n : Real) := by exact_mod_cast hnN
    dsimp [f]
    rw [perronNearError, if_neg]
    intro hrange
    linarith [hrange.2.1]
  rw [tsum_eq_sum hSupport]
  have hSplit :
      (∑ n ∈ Finset.range N, f n) =
        (∑ n ∈ Finset.range m, f n) +
          ((∑ n ∈ Finset.Ico m (m + 2), f n) +
            ∑ n ∈ Finset.Ico (m + 2) N, f n) := by
    calc
      (∑ n ∈ Finset.range N, f n) =
          (∑ n ∈ Finset.range m, f n) +
            ∑ n ∈ Finset.Ico m N, f n :=
        (Finset.sum_range_add_sum_Ico f hmN).symm
      _ = _ := by
        rw [← Finset.sum_Ico_consecutive f (Nat.le_add_right m 2) hm2N]
  have hqNonneg : 0 <= x / T := div_nonneg hxPos.le hT.le
  have hLow :
      (∑ n ∈ Finset.range m, f n) <=
        (x / T) * (harmonic N : Real) := by
    calc
      (∑ n ∈ Finset.range m, f n) <=
          ∑ n ∈ Finset.range m,
            (x / T) * (((m - n : Nat) : Real)⁻¹) := by
        apply Finset.sum_le_sum
        intro n hn
        apply perronNearError_below_floor_le hxPos hT
        simpa [m] using hn
      _ = (x / T) * (harmonic m : Real) := by
        rw [← sum_range_inv_floor_sub m, Finset.mul_sum]
      _ <= (x / T) * (harmonic N : Real) :=
        mul_le_mul_of_nonneg_left (harmonic_mono_cast hmN) hqNonneg
  have hMiddle :
      (∑ n ∈ Finset.Ico m (m + 2), f n) <= 2 := by
    calc
      (∑ n ∈ Finset.Ico m (m + 2), f n) <=
          ∑ _n ∈ Finset.Ico m (m + 2), (1 : Real) := by
        apply Finset.sum_le_sum
        intro n _
        exact perronNearError_le_one x T n
      _ = 2 := by simp
  have hUpper :
      (∑ n ∈ Finset.Ico (m + 2) N, f n) <=
        (x / T) * (harmonic N : Real) := by
    calc
      (∑ n ∈ Finset.Ico (m + 2) N, f n) <=
          ∑ n ∈ Finset.Ico (m + 2) N,
            (x / T) * (((n - (m + 1) : Nat) : Real)⁻¹) := by
        apply Finset.sum_le_sum
        intro n hn
        apply perronNearError_above_floor_succ_le hxPos hT
        rw [Finset.mem_Ico] at hn
        omega
      _ = (x / T) * (harmonic (N - (m + 2)) : Real) := by
        rw [← sum_Ico_inv_sub_floor_succ m N, Finset.mul_sum]
      _ <= (x / T) * (harmonic N : Real) :=
        mul_le_mul_of_nonneg_left
          (harmonic_mono_cast (Nat.sub_le N (m + 2))) hqNonneg
  have hFinite :
      (∑ n ∈ Finset.range N, f n) <=
        2 + 2 * (x / T) * (harmonic N : Real) := by
    rw [hSplit]
    calc
      (∑ n ∈ Finset.range m, f n) +
          ((∑ n ∈ Finset.Ico m (m + 2), f n) +
            ∑ n ∈ Finset.Ico (m + 2) N, f n) <=
        (x / T) * (harmonic N : Real) +
          (2 + (x / T) * (harmonic N : Real)) :=
        add_le_add hLow (add_le_add hMiddle hUpper)
      _ = 2 + 2 * (x / T) * (harmonic N : Real) := by ring
  have hNPos : (0 : Real) < N := by
    exact_mod_cast (Nat.ceil_pos.mpr (by positivity : 0 < 2 * x))
  have hNLt : (N : Real) < 4 * x := by
    have hceil := Nat.ceil_lt_add_one (by positivity : 0 <= 2 * x)
    change (N : Real) < 2 * x + 1 at hceil
    nlinarith
  have hLogN : Real.log (N : Real) <= 2 * Real.log x := by
    have hLogNLe : Real.log (N : Real) <= Real.log (4 * x) :=
      Real.log_le_log hNPos hNLt.le
    rw [Real.log_mul (by norm_num) hxPos.ne'] at hLogNLe
    have hLogFourLe : Real.log 4 <= Real.log x :=
      Real.log_le_log (by norm_num) hx
    linarith
  have hLogOne : 1 <= Real.log x := by
    have hLogFour : 1 < Real.log 4 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      exact Real.exp_one_lt_three.trans (by norm_num)
    exact (hLogFour.trans_le (Real.log_le_log (by norm_num) hx)).le
  have hHarmonic : (harmonic N : Real) <= 3 * Real.log x :=
    (harmonic_le_one_add_log N).trans (by linarith)
  have hqOne : 1 <= x / T := (one_le_div hT).2 hTx
  calc
    (∑ n ∈ Finset.range N, f n) <=
        2 + 2 * (x / T) * (harmonic N : Real) := hFinite
    _ <= 2 + 2 * (x / T) * (3 * Real.log x) := by
      gcongr
    _ <= 8 * x * Real.log x / T := by
      rw [show 8 * x * Real.log x / T =
        8 * (x / T) * Real.log x by ring]
      have : 2 <= 2 * (x / T) * Real.log x := by nlinarith
      nlinarith

/-- In the strict near-diagonal Perron error, inserting von Mangoldt weights
costs at most `3 * log x / 2`; together with the scalar estimate this gives
the explicit constant twelve used after Eq. (6.16). -/
theorem perronNearErrorSum_vonMangoldt_le
    {x T : Real} (hx : 4 <= x) (hT : 0 < T) (hTx : T <= x) :
    perronNearErrorSum
        (fun n => (ArithmeticFunction.vonMangoldt n : Complex)) x T <=
      12 * x * Real.log x ^ 2 / T := by
  let a : Nat -> Complex := fun n => ArithmeticFunction.vonMangoldt n
  let K : Real := 3 * Real.log x / 2
  have hxPos : 0 < x := by linarith
  have hLogPos : 0 < Real.log x := Real.log_pos (by linarith)
  have hKNonneg : 0 <= K := by
    dsimp [K]
    positivity
  have hLogTwoLe : Real.log 2 <= Real.log x / 2 := by
    have hLogFourLe : Real.log 4 <= Real.log x :=
      Real.log_le_log (by norm_num) hx
    have hLogFour : Real.log 4 = Real.log 2 + Real.log 2 := by
      rw [show (4 : Real) = 2 * 2 by norm_num,
        Real.log_mul (by norm_num) (by norm_num)]
    rw [hLogFour] at hLogFourLe
    linarith
  have hTerm (n : Nat) :
      perronNearErrorTerm a x T n <= K * perronNearError x T n := by
    have hNearNonneg := perronNearError_nonneg hxPos hT n
    by_cases hn : n = 0
    · subst n
      rw [perronNearErrorTerm, if_pos rfl]
      exact mul_nonneg hKNonneg hNearNonneg
    rw [perronNearErrorTerm, if_neg hn]
    by_cases hnear : perronNearError x T n = 0
    · simp [hnear]
    have hrange :
        x / 2 < (n : Real) ∧ (n : Real) < 2 * x ∧ x ≠ (n : Real) := by
      rw [perronNearError] at hnear
      split_ifs at hnear with h
      · exact h
      · exact (hnear rfl).elim
    have hnPos : (0 : Real) < n := by
      exact_mod_cast Nat.pos_of_ne_zero hn
    have hLogN : Real.log (n : Real) <= Real.log (2 * x) :=
      Real.log_le_log hnPos hrange.2.1.le
    have hLogTwoX : Real.log (2 * x) <= K := by
      rw [Real.log_mul (by norm_num) hxPos.ne'] at hLogN ⊢
      dsimp [K]
      linarith
    have hLambda : ArithmeticFunction.vonMangoldt n <= K :=
      ArithmeticFunction.vonMangoldt_le_log.trans (hLogN.trans hLogTwoX)
    have hNorm : ‖a n‖ = ArithmeticFunction.vonMangoldt n := by
      dsimp [a]
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    rw [hNorm]
    exact mul_le_mul_of_nonneg_right hLambda hNearNonneg
  have hNearSummable : Summable (perronNearError x T) :=
    summable_of_hasFiniteSupport (perronNearError_hasFiniteSupport x T)
  have hWeightedSummable : Summable (perronNearErrorTerm a x T) :=
    summable_perronNearErrorTerm a x T
  have hBoundSummable : Summable (fun n => K * perronNearError x T n) :=
    hNearSummable.mul_left K
  rw [perronNearErrorSum]
  calc
    (∑' n, perronNearErrorTerm a x T n) <=
        ∑' n, K * perronNearError x T n :=
      hWeightedSummable.tsum_le_tsum hTerm hBoundSummable
    _ = K * ∑' n, perronNearError x T n := by rw [tsum_mul_left]
    _ <= K * (8 * x * Real.log x / T) :=
      mul_le_mul_of_nonneg_left (tsum_perronNearError_le hx hT hTx) hKNonneg
    _ = 12 * x * Real.log x ^ 2 / T := by
      dsimp [K]
      ring

end PrimesRestrictedDigits
