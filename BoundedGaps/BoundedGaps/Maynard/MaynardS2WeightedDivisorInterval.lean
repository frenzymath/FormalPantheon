import BoundedGaps.Maynard.MaynardSquarefreeRoughTail
import BoundedGaps.Maynard.MaynardYMobiusInterval

noncomputable section

/-!
# Maynard's weighted upper-divisor interval identity

This is the scalar divisor identity used while expanding the restricted
`y^(m)` transform in Maynard 2013v3, source lines 417--430.
-/

namespace BoundedGaps.Maynard

open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius BigOperators

def maynardTotientAF : ArithmeticFunction ℕ where
  toFun := Nat.totient
  map_zero' := Nat.totient_zero

theorem maynardTotientAF_multiplicative :
    maynardTotientAF.IsMultiplicative := by
  constructor
  · exact Nat.totient_one
  · intro m n hmn
    exact Nat.totient_mul hmn

noncomputable def maynardDivTotientAF : ArithmeticFunction ℝ :=
  ArithmeticFunction.pdiv
    (ArithmeticFunction.id : ArithmeticFunction ℝ)
    (maynardTotientAF : ArithmeticFunction ℝ)

theorem maynardDivTotientAF_apply (n : ℕ) :
    maynardDivTotientAF n = (n : ℝ) / Nat.totient n := by
  unfold maynardDivTotientAF
  rw [ArithmeticFunction.pdiv_apply]
  simp [maynardTotientAF]

theorem maynardDivTotientAF_multiplicative :
    maynardDivTotientAF.IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_id.natCast.pdiv
    maynardTotientAF_multiplicative.natCast

theorem sum_moebius_mul_div_totient_divisors
    {n : ℕ} (hn : Squarefree n) :
    (∑ d ∈ n.divisors,
      (ArithmeticFunction.moebius d : ℝ) * (d : ℝ) / Nat.totient d) =
        (ArithmeticFunction.moebius n : ℝ) / Nat.totient n := by
  have hEuler :=
    ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree
      maynardDivTotientAF maynardDivTotientAF_multiplicative hn
  simp_rw [maynardDivTotientAF_apply] at hEuler
  calc
    (∑ d ∈ n.divisors,
        (ArithmeticFunction.moebius d : ℝ) * (d : ℝ) / Nat.totient d) =
        ∑ d ∈ n.divisors,
          (ArithmeticFunction.moebius d : ℝ) *
            ((d : ℝ) / Nat.totient d) := by
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ = ∏ p ∈ n.primeFactors,
          (1 - (p : ℝ) / Nat.totient p) := hEuler.symm
    _ = (ArithmeticFunction.moebius n : ℝ) / Nat.totient n := by
      have hmu :
          (∏ p ∈ n.primeFactors,
            (ArithmeticFunction.moebius p : ℝ)) =
              (ArithmeticFunction.moebius n : ℝ) := by
        exact
          (ArithmeticFunction.isMultiplicative_moebius.intCast
            (R := ℝ)).prod_primeFactors hn
      have hphi := totient_eq_prod_primeFactors_of_squarefree hn
      rw [← hmu, hphi]
      push_cast
      rw [← Finset.prod_div_distrib]
      apply Finset.prod_congr rfl
      intro p hpMem
      have hp := Nat.prime_of_mem_primeFactors hpMem
      rw [ArithmeticFunction.moebius_apply_prime hp, Nat.totient_prime hp]
      have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      rw [Nat.cast_sub hp.one_le]
      have hpOne : (p : ℝ) - 1 ≠ 0 := by nlinarith
      field_simp [hpOne]
      ring

theorem sum_moebius_mul_div_totient_upperDivisorInterval
    {r a : ℕ} (ha : Squarefree a) (hr : 0 < r) (hra : r ∣ a) :
    (∑ d ∈ upperDivisorInterval r a,
      (ArithmeticFunction.moebius d : ℝ) * (d : ℝ) / Nat.totient d) =
      (ArithmeticFunction.moebius a : ℝ) * (r : ℝ) / Nat.totient a := by
  classical
  let q := a / r
  have ha0 : a ≠ 0 := ha.ne_zero
  have hq0 : q ≠ 0 := by
    exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) hra) hr).ne'
  have hmul : r * q = a := Nat.mul_div_cancel' hra
  have hcop : Nat.Coprime r q := by
    apply Nat.coprime_of_squarefree_mul
    rwa [hmul]
  have hqSq : Squarefree q := by
    rw [← hmul] at ha
    exact (Nat.squarefree_mul_iff.mp ha).2.2
  have hreindex :
      (∑ d ∈ upperDivisorInterval r a,
        (ArithmeticFunction.moebius d : ℝ) * (d : ℝ) / Nat.totient d) =
      ∑ b ∈ q.divisors,
        maynardDivTotientAF r * (ArithmeticFunction.moebius r : ℝ) *
          ((ArithmeticFunction.moebius b : ℝ) * (b : ℝ) / Nat.totient b) := by
    apply Finset.sum_bij (fun d hd => d / r)
    · intro d hd
      have hdData := Finset.mem_filter.mp hd
      have hrd : r ∣ d := hdData.2
      apply Nat.mem_divisors.mpr
      refine ⟨?_, hq0⟩
      rw [Nat.dvd_div_iff_mul_dvd hra]
      rw [Nat.mul_div_cancel' hrd]
      exact Nat.dvd_of_mem_divisors hdData.1
    · intro d₁ hd₁ d₂ hd₂ hdiv
      have hr₁ := (Finset.mem_filter.mp hd₁).2
      have hr₂ := (Finset.mem_filter.mp hd₂).2
      calc
        d₁ = r * (d₁ / r) := (Nat.mul_div_cancel' hr₁).symm
        _ = r * (d₂ / r) := by rw [hdiv]
        _ = d₂ := Nat.mul_div_cancel' hr₂
    · intro b hb
      refine ⟨r * b, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Nat.mem_divisors.mpr ⟨?_, ha0⟩, dvd_mul_right r b⟩
        have hbDvd : b ∣ q := Nat.dvd_of_mem_divisors hb
        rw [← hmul]
        exact Nat.mul_dvd_mul_left r hbDvd
      · exact Nat.mul_div_cancel_left b hr
    · intro d hd
      have hdData := Finset.mem_filter.mp hd
      have hrd : r ∣ d := hdData.2
      have hquotDvd : d / r ∣ q := by
        rw [Nat.dvd_div_iff_mul_dvd hra]
        rw [Nat.mul_div_cancel' hrd]
        exact Nat.dvd_of_mem_divisors hdData.1
      have hcop' : Nat.Coprime r (d / r) := hcop.of_dvd_right hquotDvd
      have hdEq : d = r * (d / r) := (Nat.mul_div_cancel' hrd).symm
      have hmu :=
        ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop'
      have hratio :=
        maynardDivTotientAF_multiplicative.map_mul_of_coprime hcop'
      rw [hdEq, Nat.mul_div_cancel_left _ hr]
      calc
        (ArithmeticFunction.moebius (r * (d / r)) : ℝ) *
              ((r * (d / r) : ℕ) : ℝ) / Nat.totient (r * (d / r)) =
            (ArithmeticFunction.moebius (r * (d / r)) : ℝ) *
              maynardDivTotientAF (r * (d / r)) := by
          rw [maynardDivTotientAF_apply]
          ring
        _ = maynardDivTotientAF r * (ArithmeticFunction.moebius r : ℝ) *
              ((ArithmeticFunction.moebius (d / r) : ℝ) *
                maynardDivTotientAF (d / r)) := by
          rw [hmu, hratio]
          push_cast
          ring
        _ = maynardDivTotientAF r * (ArithmeticFunction.moebius r : ℝ) *
              ((ArithmeticFunction.moebius (d / r) : ℝ) *
                ((d / r : ℕ) : ℝ) / Nat.totient (d / r)) := by
          rw [maynardDivTotientAF_apply r,
            maynardDivTotientAF_apply (d / r)]
          ring
  rw [hreindex, ← Finset.mul_sum]
  rw [sum_moebius_mul_div_totient_divisors hqSq]
  simp only [maynardDivTotientAF_apply]
  have hmu := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
  have hphi := Nat.totient_mul hcop
  rw [← hmul]
  have hmuR : (ArithmeticFunction.moebius (r * q) : ℝ) =
      (ArithmeticFunction.moebius r : ℝ) * ArithmeticFunction.moebius q := by
    exact_mod_cast hmu
  have hphiMul : (Nat.totient (r * q) : ℝ) =
      (Nat.totient r : ℝ) * Nat.totient q := by
    exact_mod_cast hphi
  have hphiR : (Nat.totient r : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.totient_pos.mpr hr))
  have hqPos : 0 < q := Nat.pos_of_ne_zero hq0
  have hphiQ : (Nat.totient q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.totient_pos.mpr hqPos))
  rw [hmuR, hphiMul]
  field_simp [hphiR, hphiQ]

end BoundedGaps.Maynard
