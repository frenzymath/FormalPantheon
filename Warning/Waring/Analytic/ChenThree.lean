import Waring.Analytic.Basic

/-!
# Chen's Lemma 3

This file formalizes the exact prime-power cancellation in
[CHEN1964-EN, p. 1548; CHEN1964-ZH, p. 716].
-/

namespace Waring.Analytic

open scoped BigOperators

/-- `ZMod.finEquiv` sends a finite index to its natural residue class. -/
@[simp] theorem zmod_finEquiv_apply {n : Nat} [NeZero n] (x : Fin n) :
    ZMod.finEquiv n x = ((x : Nat) : ZMod n) := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
      apply Fin.ext
      change x.val = x.val % (n + 1)
      exact (Nat.mod_eq_of_lt x.isLt).symm

/-- The additive map from residues modulo `n` to residues modulo `n*m` that
sends `x` to `m*x`. -/
def zmodScale (n m : Nat) : ZMod n →+ ZMod (n * m) :=
  ZMod.lift n
    ⟨(AddMonoidHom.mulLeft (m : ZMod (n * m))).comp
        (Int.castAddHom (ZMod (n * m))), by
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft,
        Int.coe_castAddHom]
      simpa only [Int.cast_natCast, Nat.cast_mul, mul_comm] using
        ZMod.natCast_self (n * m)⟩

@[simp] theorem zmodScale_intCast (n m : Nat) (x : Int) :
    zmodScale n m (x : ZMod n) = (m : ZMod (n * m)) * x := by
  simp [zmodScale]

/-- Scaling a residue by the complementary modulus preserves the standard
additive character. -/
theorem stdAddChar_zmodScale (n m : Nat) [NeZero n] [NeZero m] (x : ZMod n) :
    ZMod.stdAddChar (zmodScale n m x) = ZMod.stdAddChar x := by
  obtain ⟨j, rfl⟩ := ZMod.intCast_surjective x
  rw [zmodScale_intCast]
  rw [← Int.cast_natCast, ← Int.cast_mul, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  have hn : (n : Complex) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hm : (m : Complex) ≠ 0 := by exact_mod_cast NeZero.ne m
  field_simp [hn, hm]

/-- Orthogonality after embedding a complete residue system into a larger
modulus by complementary scaling. -/
theorem sum_fin_stdAddChar_zmodScale (n m : Nat) [NeZero n] [NeZero m]
    (c : ZMod n) :
    ∑ x : Fin n,
        ZMod.stdAddChar (zmodScale n m ((ZMod.finEquiv n).toEquiv x * c)) =
      if c = 0 then n else 0 := by
  calc
    ∑ x : Fin n,
        ZMod.stdAddChar (zmodScale n m (ZMod.finEquiv n x * c)) =
        ∑ x : ZMod n, ZMod.stdAddChar (zmodScale n m (x * c)) :=
      by
        exact Fintype.sum_equiv (ZMod.finEquiv n).toEquiv _ _ (fun _ ↦ rfl)
    _ = ∑ x : ZMod n, ZMod.stdAddChar (x * c) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [stdAddChar_zmodScale]
    _ = if c = 0 then n else 0 := sum_stdAddChar_mul c

/-- The binomial congruence in Chen's Lemma 3, with `m=5*t` and modulus
`25*m`. -/
theorem fifthPower_add_fiveScale (t : Nat) (eta xi : ZMod (25 * (5 * t))) :
    (eta + (5 * t : Nat) * xi) ^ 5 =
      eta ^ 5 + (25 * t : Nat) * eta ^ 4 * xi := by
  have hmod : (125 * t : Nat) = (0 : ZMod (25 * (5 * t))) := by
    simpa only [show 25 * (5 * t) = 125 * t by omega] using
      ZMod.natCast_self (25 * (5 * t))
  calc
    (eta + (5 * t : Nat) * xi) ^ 5 =
        eta ^ 5 + (25 * t : Nat) * eta ^ 4 * xi +
          (125 * t : Nat) *
            (2 * t * eta ^ 3 * xi ^ 2 +
              10 * t ^ 2 * eta ^ 2 * xi ^ 3 +
              25 * t ^ 3 * eta * xi ^ 4 + 25 * t ^ 4 * xi ^ 5) := by
      push_cast
      ring
    _ = eta ^ 5 + (25 * t : Nat) * eta ^ 4 * xi := by rw [hmod, zero_mul, add_zero]

/-- Reindex the complete fifth-power sum into Chen's `25` by `5*t`
residue blocks and apply the binomial congruence. -/
theorem completePowerSum_fifth_reindex (t : Nat) [NeZero t]
    (a : ZMod (25 * (5 * t))) :
    completePowerSum 5 a =
      ∑ eta : Fin (5 * t), ∑ xi : Fin 25,
        ZMod.stdAddChar
          (a * (((eta : Nat) : ZMod (25 * (5 * t))) ^ 5 +
            ((25 * t : Nat) : ZMod (25 * (5 * t))) *
              ((eta : Nat) : ZMod (25 * (5 * t))) ^ 4 *
              ((xi : Nat) : ZMod (25 * (5 * t))))) := by
  rw [completePowerSum, powerSum]
  rw [← (ZMod.finEquiv (25 * (5 * t))).toEquiv.sum_comp]
  rw [← (finProdFinEquiv : Fin 25 × Fin (5 * t) ≃ Fin (25 * (5 * t))).sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro eta _
  apply Finset.sum_congr rfl
  intro xi _
  rw [show (ZMod.finEquiv (25 * (5 * t))).toEquiv (finProdFinEquiv (xi, eta)) =
      ((eta : Nat) : ZMod (25 * (5 * t))) +
        (5 * t : Nat) * ((xi : Nat) : ZMod (25 * (5 * t))) by
        change ZMod.finEquiv (25 * (5 * t)) (finProdFinEquiv (xi, eta)) = _
        rw [zmod_finEquiv_apply]
        change ((eta.val + (5 * t) * xi.val : Nat) : ZMod (25 * (5 * t))) = _
        push_cast
        ring]
  rw [fifthPower_add_fiveScale]

/-- The 25-term inner character sum in Chen's block decomposition. -/
theorem chen_three_inner_sum (t : Nat) [NeZero t] (a eta : Nat) :
    ∑ xi : Fin 25,
        ZMod.stdAddChar
          (((a : Nat) : ZMod (25 * (5 * t))) *
            ((25 * t : Nat) : ZMod (25 * (5 * t))) *
              ((eta : Nat) : ZMod (25 * (5 * t))) ^ 4 *
                ((xi : Nat) : ZMod (25 * (5 * t)))) =
      if ((5 * a * eta ^ 4 : Nat) : ZMod 25) = 0 then 25 else 0 := by
  let c : ZMod 25 := (5 * a * eta ^ 4 : Nat)
  calc
    ∑ xi : Fin 25,
        ZMod.stdAddChar
          (((a : Nat) : ZMod (25 * (5 * t))) *
            ((25 * t : Nat) : ZMod (25 * (5 * t))) *
              ((eta : Nat) : ZMod (25 * (5 * t))) ^ 4 *
                ((xi : Nat) : ZMod (25 * (5 * t)))) =
        ∑ xi : Fin 25,
          ZMod.stdAddChar
            (zmodScale 25 (5 * t) ((ZMod.finEquiv 25).toEquiv xi * c)) := by
      apply Finset.sum_congr rfl
      intro xi _
      apply congrArg ZMod.stdAddChar
      rw [show (ZMod.finEquiv 25).toEquiv xi = ((xi : Nat) : ZMod 25) by
        change ZMod.finEquiv 25 xi = _
        exact zmod_finEquiv_apply xi]
      dsimp [c]
      rw [show ((xi : Nat) : ZMod 25) * ((5 * a * eta ^ 4 : Nat) : ZMod 25) =
          ((xi.val * (5 * a * eta ^ 4) : Nat) : ZMod 25) by push_cast; rfl]
      rw [show zmodScale 25 (5 * t)
          ((xi.val * (5 * a * eta ^ 4) : Nat) : ZMod 25) =
          ((5 * t : Nat) : ZMod (25 * (5 * t))) *
            ((xi.val * (5 * a * eta ^ 4) : Nat) : ZMod (25 * (5 * t))) by
        simpa only [Int.cast_natCast] using
          zmodScale_intCast 25 (5 * t)
            ((xi.val * (5 * a * eta ^ 4) : Nat) : Int)]
      push_cast
      ring
    _ = if c = 0 then 25 else 0 := by
      simpa using sum_fin_stdAddChar_zmodScale 25 (5 * t) c
    _ = if ((5 * a * eta ^ 4 : Nat) : ZMod 25) = 0 then 25 else 0 := rfl

/-- Multiplication by five identifies the zero class modulo 25 exactly when
the remaining factor is zero modulo five. -/
theorem five_mul_eq_zero_zmod_twentyFive_iff (b : Nat) :
    ((5 * b : Nat) : ZMod 25) = 0 ↔ 5 ∣ b := by
  rw [ZMod.natCast_eq_zero_iff]
  change 5 * 5 ∣ 5 * b ↔ 5 ∣ b
  exact mul_dvd_mul_iff_left (by norm_num : (5 : Nat) ≠ 0)

/-- Under Chen's coprimality hypothesis, an inner block survives precisely
when its `eta` coordinate is divisible by five. -/
theorem chen_three_coefficient_eq_zero_iff {a eta : Nat} (ha : a.Coprime 5) :
    ((5 * a * eta ^ 4 : Nat) : ZMod 25) = 0 ↔ 5 ∣ eta := by
  rw [show 5 * a * eta ^ 4 = 5 * (a * eta ^ 4) by ring]
  rw [five_mul_eq_zero_zmod_twentyFive_iff]
  constructor
  · intro hdiv
    rcases Nat.prime_five.dvd_or_dvd hdiv with haDiv | hetaPow
    · exact (Nat.prime_five.coprime_iff_not_dvd.mp ha.symm haDiv).elim
    · exact Nat.prime_five.dvd_of_dvd_pow hetaPow
  · rintro ⟨k, rfl⟩
    refine ⟨a * 5 ^ 3 * k ^ 4, ?_⟩
    ring

/-- The zero-based block decomposition `eta = 5*k+r`. -/
def finFiveBlocks (t : Nat) : Fin t × Fin 5 ≃ Fin (5 * t) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm t 5))

@[simp] theorem finFiveBlocks_val (t : Nat) (x : Fin t × Fin 5) :
    (finFiveBlocks t x).val = x.2.val + 5 * x.1.val := by
  rfl

/-- Exactly `t` indices in `Fin (5*t)` are divisible by five. -/
theorem sum_fin_five_dvd (t : Nat) :
    ∑ eta : Fin (5 * t), (if 5 ∣ eta.val then (25 : Complex) else 0) = 25 * t := by
  rw [← (finFiveBlocks t).sum_comp]
  rw [Fintype.sum_prod_type]
  calc
    ∑ k : Fin t, ∑ r : Fin 5,
        (if 5 ∣ (finFiveBlocks t (k, r)).val then (25 : Complex) else 0) =
        ∑ _k : Fin t, (25 : Complex) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Fin.sum_univ_five]
      have h1 : ¬5 ∣ 1 + 5 * k.val := by omega
      have h2 : ¬5 ∣ 2 + 5 * k.val := by omega
      have h3 : ¬5 ∣ 3 + 5 * k.val := by omega
      have h4 : ¬5 ∣ 4 + 5 * k.val := by omega
      simp [finFiveBlocks_val, h1, h2, h3, h4]
    _ = 25 * t := by simp [mul_comm]

/-- Chen's block cancellation leaves only the indices divisible by five. -/
theorem completePowerSum_fifth_eq_survivors (t : Nat) [NeZero t]
    (a : Nat) (ha : a.Coprime 5) :
    completePowerSum 5 ((a : Nat) : ZMod (25 * (5 * t))) =
      ∑ eta : Fin (5 * t),
        (if 5 ∣ eta.val then
          (25 : Complex) * ZMod.stdAddChar
            (((a : Nat) : ZMod (25 * (5 * t))) *
              ((eta.val : Nat) : ZMod (25 * (5 * t))) ^ 5)
        else 0) := by
  rw [completePowerSum_fifth_reindex]
  apply Finset.sum_congr rfl
  intro eta _
  calc
    ∑ xi : Fin 25,
        ZMod.stdAddChar
          (((a : Nat) : ZMod (25 * (5 * t))) *
            (((eta : Nat) : ZMod (25 * (5 * t))) ^ 5 +
              ((25 * t : Nat) : ZMod (25 * (5 * t))) *
                ((eta : Nat) : ZMod (25 * (5 * t))) ^ 4 *
                  ((xi : Nat) : ZMod (25 * (5 * t))))) =
        ZMod.stdAddChar
            (((a : Nat) : ZMod (25 * (5 * t))) *
              ((eta.val : Nat) : ZMod (25 * (5 * t))) ^ 5) *
          ∑ xi : Fin 25,
            ZMod.stdAddChar
              (((a : Nat) : ZMod (25 * (5 * t))) *
                ((25 * t : Nat) : ZMod (25 * (5 * t))) *
                  ((eta.val : Nat) : ZMod (25 * (5 * t))) ^ 4 *
                    ((xi : Nat) : ZMod (25 * (5 * t)))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro xi _
      rw [mul_add, AddChar.map_add_eq_mul]
      ring_nf
    _ = _ := by
      rw [chen_three_inner_sum t a eta.val]
      rw [if_congr (chen_three_coefficient_eq_zero_iff ha) rfl rfl]
      split_ifs <;> simp_all [mul_comm]

/-- If `t` divides 25, every phase surviving the block cancellation is one. -/
theorem fifthPower_phase_eq_zero (t : Nat) (ht : t ∣ 25) (eta : Fin (5 * t))
    (heta : 5 ∣ eta.val) :
    ((eta.val ^ 5 : Nat) : ZMod (25 * (5 * t))) = 0 := by
  rw [ZMod.natCast_eq_zero_iff]
  rcases ht with ⟨d, hd⟩
  rcases heta with ⟨k, hk⟩
  refine ⟨d * k ^ 5, ?_⟩
  rw [hk]
  calc
    (5 * k) ^ 5 = 125 * 25 * k ^ 5 := by ring
    _ = 125 * (t * d) * k ^ 5 := by rw [hd]
    _ = 25 * (5 * t) * (d * k ^ 5) := by ring

/-- Exact form of the prime-power part of Chen's Lemma 3, parametrized by
`5^(alpha-3)=t`. -/
theorem completePowerSum_fifth_eq (t : Nat) [NeZero t] (ht : t ∣ 25)
    (a : Nat) (ha : a.Coprime 5) :
    completePowerSum 5 ((a : Nat) : ZMod (25 * (5 * t))) = 25 * t := by
  rw [completePowerSum_fifth_eq_survivors t a ha]
  calc
    ∑ eta : Fin (5 * t),
        (if 5 ∣ eta.val then
          (25 : Complex) * ZMod.stdAddChar
            (((a : Nat) : ZMod (25 * (5 * t))) *
              ((eta.val : Nat) : ZMod (25 * (5 * t))) ^ 5)
        else 0) =
        ∑ eta : Fin (5 * t),
          (if 5 ∣ eta.val then (25 : Complex) else 0) := by
      apply Finset.sum_congr rfl
      intro eta _
      split_ifs with heta
      · rw [← Nat.cast_pow, fifthPower_phase_eq_zero t ht eta heta]
        simp
      · rfl
    _ = 25 * t := sum_fin_five_dvd t

/-- Chen's exact identity modulo `5^3`. -/
theorem completePowerSum_fifth_125 (a : Nat) (ha : a.Coprime 5) :
    completePowerSum 5 ((a : Nat) : ZMod 125) = 25 := by
  simpa using completePowerSum_fifth_eq 1 (by norm_num) a ha

/-- Chen's exact identity modulo `5^4`. -/
theorem completePowerSum_fifth_625 (a : Nat) (ha : a.Coprime 5) :
    completePowerSum 5 ((a : Nat) : ZMod 625) = 125 := by
  have h := completePowerSum_fifth_eq 5 (by norm_num) a ha
  norm_num at h ⊢
  exact h

/-- Chen's exact identity modulo `5^5`. -/
theorem completePowerSum_fifth_3125 (a : Nat) (ha : a.Coprime 5) :
    completePowerSum 5 ((a : Nat) : ZMod 3125) = 625 := by
  have h := completePowerSum_fifth_eq 25 (by norm_num) a ha
  norm_num at h ⊢
  exact h

/-- The complete fifth-power sum modulo five vanishes for a primitive
coefficient, as stated separately in Chen's Lemma 3. -/
theorem completePowerSum_fifth_five (a : Nat) (ha : a.Coprime 5) :
    completePowerSum 5 ((a : Nat) : ZMod 5) = 0 := by
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hpow (x : ZMod 5) : x ^ 5 = x := ZMod.pow_card x
  have haNonzero : ((a : Nat) : ZMod 5) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact Nat.prime_five.coprime_iff_not_dvd.mp ha.symm
  simpa [completePowerSum, powerSum, hpow, mul_comm, haNonzero] using
    sum_stdAddChar_mul ((a : Nat) : ZMod 5)

/-- Exact equality proved in the first part of Chen's Lemma 3. -/
theorem completePowerSum_five_pow_eq {alpha : Nat} (hLower : 2 < alpha)
    (hUpper : alpha ≤ 5) (a : Nat) (ha : a.Coprime 5) :
    completePowerSum 5 ((a : Nat) : ZMod (5 ^ alpha)) =
      ((5 ^ (alpha - 1) : Nat) : Complex) := by
  interval_cases alpha
  · simpa using completePowerSum_fifth_125 a ha
  · simpa using completePowerSum_fifth_625 a ha
  · simpa using completePowerSum_fifth_3125 a ha

/-- The first inequality in Chen's Lemma 3. The proof establishes equality
before taking the complex norm. -/
theorem chen_three_primePower {alpha : Nat} (hLower : 2 < alpha)
    (hUpper : alpha ≤ 5) (a : Nat) (ha : a.Coprime 5) :
    ‖completePowerSum 5 ((a : Nat) : ZMod (5 ^ alpha))‖ ≤ 5 ^ (alpha - 1) := by
  rw [completePowerSum_five_pow_eq hLower hUpper a ha]
  simp

end Waring.Analytic
