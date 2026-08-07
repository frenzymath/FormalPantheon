import BoundedGaps.Maynard.MaynardSquarefreeRoughTail
import BoundedGaps.Maynard.MaynardS2TotientFactorization
import Mathlib.NumberTheory.ArithmeticFunction.Misc

noncomputable section

/-!
# Maynard's S2 g-function divisor expansion

For squarefree inputs, the local identity `1 + (p - 2) = p - 1`
turns the reciprocal totient of an LCM into a finite common-divisor sum.
This is Maynard2013v3, source lines 371--378.

The paper takes the totally multiplicative extension of `g(p)=p-2`. All
arguments here are squarefree, so `prodPrimeFactors` gives the same values on
the complete domain used by the proof; no claim about prime powers is needed.
-/

namespace BoundedGaps.Maynard

open Finset Nat ArithmeticFunction
open scoped BigOperators ArithmeticFunction.zeta
local instance s2GDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

def maynardS2G : ArithmeticFunction ℕ :=
  ArithmeticFunction.prodPrimeFactors (fun p => p - 2)

theorem maynardS2G_apply {n : ℕ} (hn : n ≠ 0) :
    maynardS2G n = ∏ p ∈ n.primeFactors, (p - 2) := by
  exact ArithmeticFunction.prodPrimeFactors_apply hn

theorem maynardS2G_prime {p : ℕ} (hp : p.Prime) :
    maynardS2G p = p - 2 := by
  rw [maynardS2G_apply hp.ne_zero, hp.primeFactors]
  simp

theorem sum_maynardS2G_divisors_eq_totient
    {n : ℕ} (hn : Squarefree n) :
    ∑ d ∈ n.divisors, maynardS2G d = Nat.totient n := by
  have hconv :=
    ArithmeticFunction.IsMultiplicative.prodPrimeFactors_add_of_squarefree
      (ArithmeticFunction.IsMultiplicative.prodPrimeFactors
        (fun p : ℕ => p - 2))
      (ArithmeticFunction.isMultiplicative_zeta :
        (ArithmeticFunction.zeta : ArithmeticFunction ℕ).IsMultiplicative) hn
  change (ArithmeticFunction.prodPrimeFactors
      (fun p => (maynardS2G + ArithmeticFunction.zeta) p)) n =
    (maynardS2G * (ArithmeticFunction.zeta : ArithmeticFunction ℕ)) n at hconv
  rw [ArithmeticFunction.mul_apply,
    sum_divisorsAntidiagonal (fun x y =>
      maynardS2G x * (ArithmeticFunction.zeta : ArithmeticFunction ℕ) y)] at hconv
  simp only [ArithmeticFunction.zeta_apply] at hconv
  have hconv' :
      (prodPrimeFactors fun p => (maynardS2G + zeta) p) n =
        ∑ d ∈ n.divisors, maynardS2G d := by
    rw [hconv]
    apply Finset.sum_congr rfl
    intro d hd
    have hquot : n / d ≠ 0 := by
      exact Nat.ne_of_gt (Nat.div_pos
        (Nat.le_of_dvd (Nat.pos_of_ne_zero hn.ne_zero)
          (Nat.dvd_of_mem_divisors hd))
        (Nat.pos_of_mem_divisors hd))
    simp [hquot]
  rw [← hconv']
  rw [ArithmeticFunction.prodPrimeFactors_apply hn.ne_zero]
  rw [totient_eq_prod_primeFactors_of_squarefree hn]
  apply Finset.prod_congr rfl
  intro p hpMem
  have hp := Nat.prime_of_mem_primeFactors hpMem
  rw [ArithmeticFunction.add_apply]
  rw [maynardS2G_prime hp, ArithmeticFunction.zeta_apply_ne hp.ne_zero,
    Nat.totient_prime hp]
  have hpTwo : 2 ≤ p := hp.two_le
  omega

theorem primeFactors_lcm_eq_union
    {d e : ℕ} (hd : d ≠ 0) (he : e ≠ 0) :
    (Nat.lcm d e).primeFactors = d.primeFactors ∪ e.primeFactors := by
  ext p
  simp only [Finset.mem_union]
  rw [Nat.mem_primeFactors, Nat.mem_primeFactors, Nat.mem_primeFactors]
  have hlcm : d.lcm e ≠ 0 := Nat.lcm_ne_zero hd he
  constructor
  · rintro ⟨hp, hpDvd, _⟩
    exact (hp.dvd_lcm.mp hpDvd).imp
      (fun h => ⟨hp, h, hd⟩) (fun h => ⟨hp, h, he⟩)
  · rintro (⟨hp, hpDvd, _⟩ | ⟨hp, hpDvd, _⟩)
    · exact ⟨hp, dvd_trans hpDvd (Nat.dvd_lcm_left d e), hlcm⟩
    · exact ⟨hp, dvd_trans hpDvd (Nat.dvd_lcm_right d e), hlcm⟩

theorem squarefree_lcm
    {d e : ℕ} (hd : Squarefree d) (he : Squarefree e) :
    Squarefree (Nat.lcm d e) := by
  apply Nat.squarefree_of_factorization_le_one
  · exact Nat.lcm_ne_zero hd.ne_zero he.ne_zero
  · intro p
    rw [Nat.factorization_lcm hd.ne_zero he.ne_zero]
    exact sup_le (hd.natFactorization_le_one p)
      (he.natFactorization_le_one p)

theorem totient_gcd_mul_totient_lcm_of_squarefree
    {d e : ℕ} (hd : Squarefree d) (he : Squarefree e) :
    Nat.totient (Nat.gcd d e) * Nat.totient (Nat.lcm d e) =
      Nat.totient d * Nat.totient e := by
  have hgcd : Squarefree (Nat.gcd d e) :=
    hd.squarefree_of_dvd (Nat.gcd_dvd_left d e)
  rw [totient_eq_prod_primeFactors_of_squarefree hgcd]
  rw [totient_eq_prod_primeFactors_of_squarefree (squarefree_lcm hd he)]
  rw [totient_eq_prod_primeFactors_of_squarefree hd]
  rw [totient_eq_prod_primeFactors_of_squarefree he]
  rw [Nat.primeFactors_gcd hd.ne_zero he.ne_zero]
  rw [primeFactors_lcm_eq_union hd.ne_zero he.ne_zero]
  rw [mul_comm]
  exact Finset.prod_union_inter

def commonDivisorS2GSum (d e : ℕ) : ℝ :=
  ∑ u ∈ (Nat.gcd d e).divisors, (maynardS2G u : ℝ)

theorem inv_totient_lcm_eq_maynardS2G_sum_div_mul
    {d e : ℕ} (hd : Squarefree d) (he : Squarefree e)
    (hdPos : 0 < d) (hePos : 0 < e) :
    (Nat.totient (Nat.lcm d e) : ℝ)⁻¹ =
      commonDivisorS2GSum d e /
        ((Nat.totient d : ℝ) * Nat.totient e) := by
  have hgcd : Squarefree (Nat.gcd d e) :=
    hd.squarefree_of_dvd (Nat.gcd_dvd_left d e)
  have hsumNat := sum_maynardS2G_divisors_eq_totient hgcd
  have hsum : commonDivisorS2GSum d e =
      (Nat.totient (Nat.gcd d e) : ℝ) := by
    unfold commonDivisorS2GSum
    exact_mod_cast hsumNat
  rw [hsum]
  have hrel := totient_gcd_mul_totient_lcm_of_squarefree hd he
  have hphiD : (Nat.totient d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.totient_pos.mpr hdPos))
  have hphiE : (Nat.totient e : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.totient_pos.mpr hePos))
  have hphiL : (Nat.totient (Nat.lcm d e) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.totient_pos.mpr
      (Nat.lcm_pos hdPos hePos)))
  have hrelR :
      (Nat.totient (Nat.gcd d e) : ℝ) * Nat.totient (Nat.lcm d e) =
        (Nat.totient d : ℝ) * Nat.totient e := by
    exact_mod_cast hrel
  field_simp
  nlinarith [hrelR]

noncomputable def commonDivisorS2TupleTerm
    (H : Finset ℕ) (d e u : H → ℕ) : ℝ :=
  ∏ h : H, (maynardS2G (u h) : ℝ) /
    ((Nat.totient (d h) : ℝ) * Nat.totient (e h))

theorem inverse_totientLcmProduct_eq_commonDivisorS2TupleSum
    {H : Finset ℕ} {R W : ℕ} {d e : H → ℕ}
    (hd : IsMaynardDivisorTuple H R W d)
    (he : IsMaynardDivisorTuple H R W e) :
    (∏ h : H,
      (Nat.totient (divisorTupleLcm H d e h) : ℝ))⁻¹ =
      ∑ u ∈ commonDivisorTupleSupport H d e,
        commonDivisorS2TupleTerm H d e u := by
  classical
  calc
    (∏ h : H,
        (Nat.totient (divisorTupleLcm H d e h) : ℝ))⁻¹ =
        ∏ h : H, commonDivisorS2GSum (d h) (e h) /
          ((Nat.totient (d h) : ℝ) * Nat.totient (e h)) := by
      rw [← Finset.prod_inv_distrib]
      apply Finset.prod_congr rfl
      intro h hh
      exact inv_totient_lcm_eq_maynardS2G_sum_div_mul
        (hd.coordinate_squarefree h) (he.coordinate_squarefree h)
        (Nat.pos_of_ne_zero (hd.coordinate_squarefree h).ne_zero)
        (Nat.pos_of_ne_zero (he.coordinate_squarefree h).ne_zero)
    _ = ∑ u ∈ commonDivisorTupleSupport H d e,
        commonDivisorS2TupleTerm H d e u := by
      unfold commonDivisorS2GSum commonDivisorTupleSupport
        commonDivisorS2TupleTerm
      calc
        (∏ h : H,
            (∑ u ∈ (Nat.gcd (d h) (e h)).divisors,
                (maynardS2G u : ℝ)) /
              ((Nat.totient (d h) : ℝ) * Nat.totient (e h))) =
            ∏ h : H, ∑ u ∈ (Nat.gcd (d h) (e h)).divisors,
              (maynardS2G u : ℝ) /
                ((Nat.totient (d h) : ℝ) * Nat.totient (e h)) := by
          apply Finset.prod_congr rfl
          intro h hh
          rw [Finset.sum_div]
        _ = ∑ u ∈ Fintype.piFinset
              (fun h : H => (Nat.gcd (d h) (e h)).divisors),
            ∏ h : H, (maynardS2G (u h) : ℝ) /
              ((Nat.totient (d h) : ℝ) * Nat.totient (e h)) :=
          Finset.prod_univ_sum _ _

noncomputable def compatibleDivisorPairRestrictedS2CommonDivisorTupleSum
    (H : Finset ℕ) (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) (m : H) : ℝ :=
  ∑ d : D, ∑ e : D.filter (fun e => IsCrossCoordinateCoprime H d.1 e),
    if d.1 m = 1 ∧ e.1 m = 1 then
      ∑ u ∈ commonDivisorTupleSupport H d.1 e.1,
        commonDivisorS2TupleTerm H d.1 e.1 u *
          (lambda d.1 * lambda e.1)
    else 0

theorem compatibleDivisorPairRestrictedTotientKernel_eq_commonDivisorS2TupleSum
    {H : Finset ℕ} {D : Finset (H → ℕ)}
    {lambda : (H → ℕ) → ℝ} {R W : ℕ} (m : H)
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d) :
    compatibleDivisorPairRestrictedTotientKernel H D lambda m =
      compatibleDivisorPairRestrictedS2CommonDivisorTupleSum H D lambda m := by
  classical
  unfold compatibleDivisorPairRestrictedTotientKernel
    compatibleDivisorPairRestrictedS2CommonDivisorTupleSum
  apply Finset.sum_congr rfl
  intro d hdMem
  apply Finset.sum_congr rfl
  intro e heMem
  by_cases hm : d.1 m = 1 ∧ e.1 m = 1
  · rw [if_pos hm, if_pos hm]
    have heD := (Finset.mem_filter.mp e.2).1
    rw [div_eq_mul_inv,
      inverse_totientLcmProduct_eq_commonDivisorS2TupleSum
        (hD d.1 d.2) (hD e.1 heD)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    ring
  · rw [if_neg hm, if_neg hm]

end BoundedGaps.Maynard
