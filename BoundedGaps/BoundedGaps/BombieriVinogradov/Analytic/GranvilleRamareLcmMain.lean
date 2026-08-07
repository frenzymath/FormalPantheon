import BoundedGaps.BombieriVinogradov.Analytic.GranvilleRamareCoprimeMoebius
import BoundedGaps.BombieriVinogradov.Analytic.GranvilleRamareMoments
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# The signed lcm term in the Granville--Ramare estimate

This file isolates the signed least-common-multiple main term in
Granville--Ramare1996, Proposition 10.1, printed p. 43.  The gcd quotient
reindex exposes the coprime Mobius harmonic sum from Lemma 10.2; its outer
divisor count is then bounded by the second moment in Lemma 10.3.

Semantic review: `SEM-457`.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

noncomputable section

private abbrev muR (n : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius n : ℤ) : ℝ)

private def positiveUpTo (N : ℕ) : Finset ℕ :=
  Finset.Ioc 0 N

private theorem abs_muR_eq_sq (n : ℕ) :
    |muR n| = (muR n) ^ 2 := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;>
    simp [muR, h]

private theorem gcd_lcm_mul_right
    {d g b : ℕ} (hg : g ∣ d) (hb : Nat.Coprime b d) :
    Nat.gcd d (g * b) = g ∧ Nat.lcm d (g * b) = d * b := by
  have hdEq : d = g * (d / g) := (Nat.mul_div_cancel' hg).symm
  have hcop : Nat.Coprime (d / g) b :=
    Nat.Coprime.of_dvd_left (Nat.div_dvd_of_dvd hg) hb.symm
  constructor
  · rw [hdEq, Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one]
  · rw [hdEq, Nat.lcm_mul_left, hcop.lcm_eq_mul]
    ac_rfl

private theorem muR_lcm_term_eq
    {d g b : ℕ} (hd : 0 < d) (hbPos : 0 < b)
    (hg : g ∣ d) (hb : Nat.Coprime b d) :
    muR d * muR (g * b) / (Nat.lcm d (g * b) : ℝ) =
      (muR d * muR g / (d : ℝ)) * (muR b / (b : ℝ)) := by
  have hcop : Nat.Coprime g b := (hb.coprime_dvd_right hg).symm
  have hmu :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
  have hmuR : muR (g * b) = muR g * muR b := by exact_mod_cast hmu
  rw [hmuR, (gcd_lcm_mul_right hg hb).2]
  push_cast
  field_simp

private def mainFiberSupport (d Z B : ℕ) : Finset (Σ _g : ℕ, ℕ) :=
  d.divisors.sigma (fun g =>
    (positiveUpTo (min (Z / g) (B / d))).filter
      (fun b => Nat.Coprime b d))

private theorem abs_mainFiber_le
    {d Z B : ℕ} (hdZ : d ∈ positiveUpTo Z) :
    |∑ e ∈ (positiveUpTo Z).filter (fun e => Nat.lcm d e ≤ B),
      muR d * muR e / (Nat.lcm d e : ℝ)| ≤
      (muR d) ^ 2 * (d.divisors.card : ℝ) / (d : ℝ) := by
  have hdPos : 0 < d := (Finset.mem_Ioc.mp hdZ).1
  by_cases hdSq : Squarefree d
  · have hreindex :
        (∑ e ∈ (positiveUpTo Z).filter (fun e => Nat.lcm d e ≤ B),
          muR d * muR e / (Nat.lcm d e : ℝ)) =
        ∑ x ∈ mainFiberSupport d Z B,
          (muR d * muR x.1 / (d : ℝ)) *
            (muR x.2 / (x.2 : ℝ)) := by
      apply Finset.sum_bij_ne_zero
          (fun e _he _hne => ⟨Nat.gcd d e, e / Nat.gcd d e⟩)
      · intro e he hne
        rcases Finset.mem_filter.mp he with ⟨heZ, hlcm⟩
        have hePos : 0 < e := (Finset.mem_Ioc.mp heZ).1
        have hmuE : ArithmeticFunction.moebius e ≠ 0 := by
          intro hzero
          apply hne
          simp [muR, hzero]
        have heSq := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmuE
        have hgPos : 0 < Nat.gcd d e := Nat.gcd_pos_of_pos_left e hdPos
        have hgDvd : Nat.gcd d e ∣ d := Nat.gcd_dvd_left d e
        have hbCop : Nat.Coprime (e / Nat.gcd d e) d := by
          simpa only [Nat.gcd_comm] using
            Nat.coprime_div_gcd_of_squarefree heSq hdPos.ne'
        have hbPos : 0 < e / Nat.gcd d e :=
          Nat.div_pos (Nat.le_of_dvd hePos (Nat.gcd_dvd_right d e)) hgPos
        have heEq : e = Nat.gcd d e * (e / Nat.gcd d e) :=
          (Nat.mul_div_cancel' (Nat.gcd_dvd_right d e)).symm
        have hlcmEq : Nat.lcm d e = d * (e / Nat.gcd d e) := by
          calc
            Nat.lcm d e =
                Nat.lcm d (Nat.gcd d e * (e / Nat.gcd d e)) := by rw [← heEq]
            _ = d * (e / Nat.gcd d e) :=
              (gcd_lcm_mul_right hgDvd hbCop).2
        apply Finset.mem_sigma.mpr
        refine ⟨Nat.mem_divisors.mpr ⟨hgDvd, hdPos.ne'⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hbPos, ?_⟩, hbCop⟩⟩
        exact le_min (Nat.div_le_div_right (Finset.mem_Ioc.mp heZ).2)
          ((Nat.le_div_iff_mul_le hdPos).2
            (by simpa only [Nat.mul_comm, ← hlcmEq] using hlcm))
      · intro e₁ he₁ hn₁ e₂ he₂ hn₂ h
        have hprod := congrArg
          (fun x : Σ _g : ℕ, ℕ => x.1 * x.2) h
        calc
          e₁ = Nat.gcd d e₁ * (e₁ / Nat.gcd d e₁) :=
            (Nat.mul_div_cancel' (Nat.gcd_dvd_right d e₁)).symm
          _ = Nat.gcd d e₂ * (e₂ / Nat.gcd d e₂) := by
            simpa only using hprod
          _ = e₂ := Nat.mul_div_cancel' (Nat.gcd_dvd_right d e₂)
      · rintro ⟨g, b⟩ hx hne
        rcases Finset.mem_sigma.mp hx with ⟨hgMem, hbMem⟩
        rcases Finset.mem_filter.mp hbMem with ⟨hbRange, hbCop⟩
        have hgDvd := Nat.dvd_of_mem_divisors hgMem
        have hgPos := Nat.pos_of_mem_divisors hgMem
        have hbData := Finset.mem_Ioc.mp hbRange
        have hdata := gcd_lcm_mul_right hgDvd hbCop
        refine ⟨g * b, ?_, ?_, ?_⟩
        · apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_Ioc.mpr ⟨Nat.mul_pos hgPos hbData.1, ?_⟩, ?_⟩
          · simpa only [Nat.mul_comm] using
              (Nat.le_div_iff_mul_le hgPos).mp (le_min_iff.mp hbData.2).1
          · rw [hdata.2]
            simpa only [Nat.mul_comm] using
              (Nat.le_div_iff_mul_le hdPos).mp (le_min_iff.mp hbData.2).2
        · rw [muR_lcm_term_eq hdPos hbData.1 hgDvd hbCop]
          exact hne
        · apply Sigma.ext hdata.1
          simp only [hdata.1, Nat.mul_div_cancel_left b hgPos]
          exact HEq.rfl
      · intro e he hne
        rcases Finset.mem_filter.mp he with ⟨heZ, hlcm⟩
        have hePos : 0 < e := (Finset.mem_Ioc.mp heZ).1
        have hmuE : ArithmeticFunction.moebius e ≠ 0 := by
          intro hzero
          apply hne
          simp [muR, hzero]
        have heSq := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmuE
        have hgPos : 0 < Nat.gcd d e := Nat.gcd_pos_of_pos_left e hdPos
        have hbPos : 0 < e / Nat.gcd d e :=
          Nat.div_pos (Nat.le_of_dvd hePos (Nat.gcd_dvd_right d e)) hgPos
        have hbCop : Nat.Coprime (e / Nat.gcd d e) d := by
          simpa only [Nat.gcd_comm] using
            Nat.coprime_div_gcd_of_squarefree heSq hdPos.ne'
        have heEq : e = Nat.gcd d e * (e / Nat.gcd d e) :=
          (Nat.mul_div_cancel' (Nat.gcd_dvd_right d e)).symm
        calc
          muR d * muR e / (Nat.lcm d e : ℝ) =
              muR d * muR (Nat.gcd d e * (e / Nat.gcd d e)) /
                (Nat.lcm d (Nat.gcd d e * (e / Nat.gcd d e)) : ℝ) := by
                  rw [← heEq]
          _ = _ := muR_lcm_term_eq hdPos hbPos
            (Nat.gcd_dvd_left d e) hbCop
    rw [hreindex]
    unfold mainFiberSupport
    change |∑ x ∈ d.divisors.sigma (fun g =>
      (positiveUpTo (min (Z / g) (B / d))).filter
        (fun b => Nat.Coprime b d)),
      (fun g b => (muR d * muR g / (d : ℝ)) *
        (muR b / (b : ℝ))) x.1 x.2| ≤ _
    rw [← Finset.sum_sigma' d.divisors
      (fun g => (positiveUpTo (min (Z / g) (B / d))).filter
        (fun b => Nat.Coprime b d))
      (fun g b => (muR d * muR g / (d : ℝ)) *
        (muR b / (b : ℝ)))]
    simp_rw [← Finset.mul_sum]
    calc
      |∑ g ∈ d.divisors, (muR d * muR g / (d : ℝ)) *
          ∑ b ∈ (positiveUpTo (min (Z / g) (B / d))).filter
            (fun b => Nat.Coprime b d), muR b / (b : ℝ)| ≤
          ∑ g ∈ d.divisors, (muR d) ^ 2 / (d : ℝ) := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
            apply Finset.sum_le_sum
            intro g hgMem
            have hgSq := hdSq.squarefree_of_dvd
              (Nat.dvd_of_mem_divisors hgMem)
            have hdMu : (muR d) ^ 2 = 1 := by
              exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hdSq
            have hgMu : (muR g) ^ 2 = 1 := by
              exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hgSq
            have habs : |muR d * muR g / (d : ℝ)| =
                (muR d) ^ 2 / (d : ℝ) := by
              rw [abs_div, abs_mul, abs_muR_eq_sq, abs_muR_eq_sq,
                abs_of_pos (by exact_mod_cast hdPos), hdMu, hgMu]
              ring
            rw [abs_mul, habs]
            exact mul_le_of_le_one_right (by positivity)
              (abs_sum_moebius_div_coprime_le_one d
                (min (Z / g) (B / d)))
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  · simp [muR, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hdSq]

/-- Granville--Ramare's signed lcm main term, with an arbitrary natural lcm
cutoff.  This is the `4/9` contribution in Proposition 10.1. -/
theorem abs_sum_moebius_mul_moebius_div_lcm_le_four_ninths
    {Z B : ℕ} (hZ : 1 ≤ Z) :
    |∑ d ∈ Finset.Ioc 0 Z,
      ∑ e ∈ (Finset.Ioc 0 Z).filter
        (fun e => Nat.lcm d e ≤ B),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          ((ArithmeticFunction.moebius e : ℤ) : ℝ) /
            (Nat.lcm d e : ℝ)| ≤
      (4 / 9 : ℝ) * (Real.log (Z : ℝ) + 3) ^ 2 := by
  change |∑ d ∈ positiveUpTo Z,
    ∑ e ∈ (positiveUpTo Z).filter (fun e => Nat.lcm d e ≤ B),
      muR d * muR e / (Nat.lcm d e : ℝ)| ≤ _
  calc
    |∑ d ∈ positiveUpTo Z,
        ∑ e ∈ (positiveUpTo Z).filter (fun e => Nat.lcm d e ≤ B),
          muR d * muR e / (Nat.lcm d e : ℝ)| ≤
        ∑ d ∈ positiveUpTo Z,
          |∑ e ∈ (positiveUpTo Z).filter (fun e => Nat.lcm d e ≤ B),
            muR d * muR e / (Nat.lcm d e : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ positiveUpTo Z,
        (muR d) ^ 2 * (d.divisors.card : ℝ) / (d : ℝ) := by
          apply Finset.sum_le_sum
          intro d hd
          exact abs_mainFiber_le hd
    _ ≤ _ := sum_sq_moebius_mul_card_divisors_div_le_four_ninths hZ

end

end BoundedGaps.Maynard
