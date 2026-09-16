import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Subpolynomial divisor bounds

This proves the pointwise divisor estimate used in `MAYNARD-PRD-PUBLISHED`,
Lemma 15.2, pp. 210--214. The constant is uniform in the integer being
factored, including Mathlib's empty divisor convention at zero.
-/

open Asymptotics Filter

namespace PrimesRestrictedDigits

private theorem eventually_succ_le_two_rpow_pow
    (rho : Real) (hrho : 0 < rho) :
    Filter.Eventually
      (fun e : Nat =>
        ((e + 1 : Nat) : Real) <= ((2 : Real) ^ rho) ^ e)
      atTop := by
  have hbase : 1 < (2 : Real) ^ rho := by
    rw [Real.one_lt_rpow_iff_of_pos (by norm_num : (0 : Real) < 2)]
    exact Or.inl (And.intro (by norm_num) hrho)
  have hdomination :=
    (isLittleO_coe_const_pow_of_one_lt (R := Real) hbase).def
      (by norm_num : (0 : Real) < 1 / 2)
  filter_upwards [hdomination, eventually_ge_atTop 1] with e he he_one
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg e),
    Real.norm_eq_abs,
    abs_of_nonneg
      (pow_nonneg (by positivity : (0 : Real) <= (2 : Real) ^ rho) _)] at he
  norm_num at he
  have he_one_real : (1 : Real) <= e := by
    exact_mod_cast he_one
  norm_num
  linarith

/-- The number of positive divisors is bounded by a fixed multiple of every
positive real power. At zero this uses Mathlib's empty divisor convention. -/
theorem card_divisors_le_const_mul_rpow
    (rho : Real) (hrho : 0 < rho) :
    Exists fun C : Real => And (0 < C) (forall n : Nat,
      (n.divisors.card : Real) <= C * (n : Real) ^ rho) := by
  have h_exponent_threshold :=
    eventually_atTop.mp (eventually_succ_le_two_rpow_pow rho hrho)
  let N0 := h_exponent_threshold.choose
  have hN0 := h_exponent_threshold.choose_spec
  let N := max N0 1
  have hN : 1 <= N := le_max_right _ _
  have hlargeExponent (e : Nat) (he : N <= e) :
      ((e + 1 : Nat) : Real) <= ((2 : Real) ^ rho) ^ e :=
    hN0 e ((le_max_left _ _).trans he)
  have h_prime_threshold :
      Exists fun P : Nat => forall p : Nat, P <= p ->
        (N : Real) <= (p : Real) ^ rho := by
    have htendsto :=
      (tendsto_rpow_atTop hrho).comp tendsto_natCast_atTop_atTop
    exact eventually_atTop.mp (htendsto.eventually_ge_atTop (N : Real))
  let P := h_prime_threshold.choose
  have hP := h_prime_threshold.choose_spec
  refine Exists.intro ((N : Real) ^ P) (And.intro (by positivity) ?_)
  intro n
  by_cases hn : n = 0
  case pos => simp [hn, hrho.ne']
  case neg =>
    have hfactor (p : Nat)
        (hp : Membership.mem n.primeFactors p) :
        (((n.factorization p + 1 : Nat) : Real)) <=
          (if p < P then (N : Real) else 1) *
            (((p : Real) ^ n.factorization p) ^ rho) := by
      have hp_prime := Nat.prime_of_mem_primeFactors hp
      have hp_two : (2 : Real) <= p := by
        exact_mod_cast hp_prime.two_le
      have he_pos : 0 < n.factorization p :=
        hp_prime.factorization_pos_of_dvd hn
          (Nat.dvd_of_mem_primeFactors hp)
      have hp_pos_nat : 0 < p := hp_prime.pos
      have hp_power_one :
          (1 : Real) <= (p : Real) ^ n.factorization p := by
        exact_mod_cast Nat.one_le_pow (n.factorization p) p hp_pos_nat
      have hpower_one :
          1 <= (((p : Real) ^ n.factorization p) ^ rho) :=
        Real.one_le_rpow hp_power_one hrho.le
      by_cases hpP : p < P
      case pos =>
        rw [if_pos hpP]
        by_cases heN : N <= n.factorization p
        case pos =>
          have hlocal := hlargeExponent _ heN
          have hbase : (2 : Real) ^ rho <= (p : Real) ^ rho :=
            Real.rpow_le_rpow (by norm_num) hp_two hrho.le
          have hpower :
              ((2 : Real) ^ rho) ^ n.factorization p <=
                ((p : Real) ^ rho) ^ n.factorization p := by
            gcongr
          rw [Real.rpow_pow_comm (Nat.cast_nonneg p) rho] at hpower
          exact hlocal.trans
            (hpower.trans (by
              nlinarith [show (1 : Real) <= N by exact_mod_cast hN]))
        case neg =>
          have heN' : n.factorization p + 1 <= N :=
            Nat.succ_le_iff.mpr (lt_of_not_ge heN)
          have heN_real :
              (((n.factorization p + 1 : Nat) : Real)) <= N := by
            exact_mod_cast heN'
          nlinarith [show (0 : Real) <= N by positivity]
      case neg =>
        rw [if_neg hpP, one_mul]
        by_cases heN : N <= n.factorization p
        case pos =>
          have hlocal := hlargeExponent _ heN
          have hbase : (2 : Real) ^ rho <= (p : Real) ^ rho :=
            Real.rpow_le_rpow (by norm_num) hp_two hrho.le
          have hpower :
              ((2 : Real) ^ rho) ^ n.factorization p <=
                ((p : Real) ^ rho) ^ n.factorization p := by
            gcongr
          rw [Real.rpow_pow_comm (Nat.cast_nonneg p) rho] at hpower
          exact hlocal.trans hpower
        case neg =>
          have heN' : n.factorization p + 1 <= N :=
            Nat.succ_le_iff.mpr (lt_of_not_ge heN)
          have heN_real :
              (((n.factorization p + 1 : Nat) : Real)) <= N := by
            exact_mod_cast heN'
          have hNP : (N : Real) <= (p : Real) ^ rho :=
            hP p (Nat.le_of_not_gt hpP)
          have hself :
              (p : Real) ^ rho <=
                ((p : Real) ^ rho) ^ n.factorization p :=
            (by
              simpa only [pow_one] using
                Bound.pow_le_pow_right_of_le_one_or_one_le
                  (Or.inl (And.intro
                    (hNP.trans' (by exact_mod_cast hN)) he_pos)))
          rw [Real.rpow_pow_comm (Nat.cast_nonneg p) rho] at hself
          exact heN_real.trans (hNP.trans hself)
    have hsmallCard :
        (n.primeFactors.filter fun p => p < P).card <= P := by
      calc
        _ <= (Finset.range P).card := Finset.card_le_card (by
          intro p hp
          rw [Finset.mem_filter] at hp
          rw [Finset.mem_range]
          exact hp.2)
        _ = P := Finset.card_range P
    have hconditionalProduct :
        Finset.prod n.primeFactors (fun p =>
          if p < P then (N : Real) else 1) =
          (N : Real) ^
            (n.primeFactors.filter fun p => p < P).card := by
      rw [Finset.prod_ite]
      simp
    have hprimePowerProduct :
        Finset.prod n.primeFactors (fun p =>
          (((p : Real) ^ n.factorization p) ^ rho)) =
          (n : Real) ^ rho := by
      rw [Real.finsetProd_rpow n.primeFactors
        (fun p => (p : Real) ^ n.factorization p)
        (fun p _ => pow_nonneg (Nat.cast_nonneg p) _) rho]
      congr 1
      exact_mod_cast Nat.prod_factorization_pow_eq_self hn
    have hsmallPowerNat :
        N ^ (n.primeFactors.filter fun p => p < P).card <= N ^ P :=
      Nat.pow_le_pow_right (lt_of_lt_of_le Nat.zero_lt_one hN) hsmallCard
    have hsmallPowerReal :
        (N : Real) ^ (n.primeFactors.filter fun p => p < P).card <=
          (N : Real) ^ P := by
      exact_mod_cast hsmallPowerNat
    calc
      (n.divisors.card : Real) =
          Finset.prod n.primeFactors (fun p =>
            (((n.factorization p + 1 : Nat) : Real))) := by
        rw [Nat.card_divisors hn, Nat.cast_prod]
      _ <= Finset.prod n.primeFactors (fun p =>
          (if p < P then (N : Real) else 1) *
            (((p : Real) ^ n.factorization p) ^ rho)) :=
        Finset.prod_le_prod (fun _ _ => by positivity) hfactor
      _ = Finset.prod n.primeFactors (fun p =>
            if p < P then (N : Real) else 1) *
          Finset.prod n.primeFactors (fun p =>
            (((p : Real) ^ n.factorization p) ^ rho)) := by
        rw [Finset.prod_mul_distrib]
      _ = (N : Real) ^
            (n.primeFactors.filter fun p => p < P).card *
          (n : Real) ^ rho := by
        rw [hconditionalProduct, hprimePowerProduct]
      _ <= (N : Real) ^ P * (n : Real) ^ rho :=
        mul_le_mul_of_nonneg_right
          hsmallPowerReal
          (Real.rpow_nonneg (Nat.cast_nonneg n) rho)

/-- The signed ordered factor-pair finset has twice as many elements as the
positive natural divisor finset. Both sides are empty at zero. -/
theorem card_int_divisorsAntidiag (z : Int) :
    z.divisorsAntidiag.card = 2 * z.natAbs.divisors.card := by
  cases z with
  | ofNat n =>
      rw [Int.ofNat_eq_natCast, Int.natAbs_natCast]
      simp only [Int.divisorsAntidiag, Finset.card_disjUnion,
        Finset.card_map]
      rw [Nat.map_div_right_divisors.symm]
      simp only [Finset.card_map]
      omega
  | negSucc n =>
      rw [Int.natAbs_negSucc]
      simp only [Int.divisorsAntidiag, Finset.card_disjUnion,
        Finset.card_map]
      rw [Nat.map_div_right_divisors.symm]
      simp only [Finset.card_map, Nat.succ_eq_add_one]
      omega

/-- Ordered signed factor pairs obey the same pointwise subpolynomial bound,
with one constant chosen uniformly before the integer. -/
theorem card_int_divisorsAntidiag_le_const_mul_rpow
    (rho : Real) (hrho : 0 < rho) :
    Exists fun C : Real => And (0 < C) (forall z : Int,
      (z.divisorsAntidiag.card : Real) <=
        C * (z.natAbs : Real) ^ rho) := by
  have hbound_exists := card_divisors_le_const_mul_rpow rho hrho
  let C := hbound_exists.choose
  have hC_and_bound := hbound_exists.choose_spec
  have hC : 0 < C := hC_and_bound.left
  have hbound := hC_and_bound.right
  refine Exists.intro (2 * C) (And.intro (mul_pos two_pos hC) ?_)
  intro z
  rw [card_int_divisorsAntidiag]
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hbound z.natAbs) zero_le_two

end PrimesRestrictedDigits
