import BoundedGaps.Arithmetic.SquarefreeReciprocalCoefficient
import BoundedGaps.Maynard.MaynardCoprimeHarmonic
import BoundedGaps.Maynard.MaynardLambdaDivisorIdentity
import BoundedGaps.Maynard.MaynardReciprocalSquareTail

noncomputable section

/-!
# A pre-sieved squarefree reciprocal-totient mean

Squarefree divisor convolution separates the mean into a uniformly bounded
reciprocal-square divisor factor and a coprime harmonic factor.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

def squarefreeCoprimeInvTotientMean (W Q : ℕ) : ℝ := by
  classical
  exact ∑ n ∈ Finset.Icc 1 Q,
    if Squarefree n ∧ Nat.Coprime n W then
      (1 : ℝ) / Nat.totient n
    else 0

theorem squarefreeCoprimeInvTotientMean_mono_cutoff
    {W : ℕ} : Monotone (fun Q : ℕ =>
      squarefreeCoprimeInvTotientMean W Q) := by
  intro Q₁ Q₂ hQ
  unfold squarefreeCoprimeInvTotientMean
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,
      (Finset.mem_Icc.mp hn).2.trans hQ⟩
  · intro n hn hnot
    by_cases hsq : Squarefree n ∧ Nat.Coprime n W
    · simp only [hsq]
      split <;> positivity
    · simp [hsq]

theorem squarefree_inv_totient_eq_divisor_convolution
    {n : ℕ} (hn : Squarefree n) :
    (1 : ℝ) / Nat.totient n =
      ∑ d ∈ n.divisors,
        (1 : ℝ) / ((n : ℝ) * Nat.totient d) := by
  have hnPos : (0 : ℝ) < n := by
    exact_mod_cast Nat.pos_of_ne_zero hn.ne_zero
  have hidentity := squarefree_div_totient_eq_sum_divisors_inv_totient hn
  calc
    (1 : ℝ) / Nat.totient n =
        ((n : ℝ) / Nat.totient n) / n := by field_simp
    _ = (∑ d ∈ n.divisors, (1 : ℝ) / Nat.totient d) / n := by
      rw [hidentity]
      simp only [one_div]
    _ = ∑ d ∈ n.divisors,
        (1 : ℝ) / ((n : ℝ) * Nat.totient d) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro d hd
      ring

private def squarefreeCoprimeSupport (W Q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 Q).filter (fun n => Squarefree n ∧ Nat.Coprime n W)

private def squarefreeSupport (Q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 Q).filter Squarefree

private def coprimeSupport (W Q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 Q).filter (Nat.Coprime · W)

private def squarefreeDivisorSigma (W Q : ℕ) : Finset (Σ _n : ℕ, ℕ) :=
  (squarefreeCoprimeSupport W Q).sigma (fun n => n.divisors)

private def divisorQuotientEncoding (x : Σ _n : ℕ, ℕ) : ℕ × ℕ :=
  (x.2, x.1 / x.2)

private def divisorQuotientWeight (x : ℕ × ℕ) : ℝ :=
  (1 : ℝ) / ((x.1 : ℝ) * Nat.totient x.1) * (1 / (x.2 : ℝ))

theorem divisorQuotientEncoding_injOn
    {W Q : ℕ} :
    Set.InjOn divisorQuotientEncoding (squarefreeDivisorSigma W Q) := by
  intro x hx y hy hxy
  have hxMem := Finset.mem_sigma.mp hx
  have hyMem := Finset.mem_sigma.mp hy
  have hd : x.2 = y.2 := congrArg Prod.fst hxy
  have hprodEq : x.2 * (x.1 / x.2) = y.2 * (y.1 / y.2) :=
    congrArg (fun z : ℕ × ℕ => z.1 * z.2) hxy
  apply Sigma.ext
  · calc
      x.1 = x.2 * (x.1 / x.2) :=
        (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hxMem.2)).symm
      _ = y.2 * (y.1 / y.2) := hprodEq
      _ = y.1 := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hyMem.2)
  · simp [hd]

theorem divisorQuotientEncoding_mem_product
    {W Q : ℕ} {x : Σ _n : ℕ, ℕ}
    (hx : x ∈ squarefreeDivisorSigma W Q) :
    divisorQuotientEncoding x ∈
      squarefreeSupport Q ×ˢ coprimeSupport W Q := by
  have hxMem := Finset.mem_sigma.mp hx
  have hnData := Finset.mem_filter.mp hxMem.1
  have hnBounds := Finset.mem_Icc.mp hnData.1
  have hdvd := Nat.dvd_of_mem_divisors hxMem.2
  have hnPos : 0 < x.1 := zero_lt_one.trans_le hnBounds.1
  have hdPos : 0 < x.2 := Nat.pos_of_dvd_of_pos hdvd hnPos
  have hdLe : x.2 ≤ x.1 := Nat.le_of_dvd hnPos hdvd
  have hqPos : 0 < x.1 / x.2 := Nat.div_pos hdLe hdPos
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨hdPos, hdLe.trans hnBounds.2⟩, hnData.2.1.squarefree_of_dvd hdvd⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨hqPos, (Nat.div_le_self _ _).trans hnBounds.2⟩, ?_⟩⟩
  exact Nat.Coprime.of_dvd_left (Nat.div_dvd_of_dvd hdvd) hnData.2.2

theorem divisorConvolutionTerm_eq_weight
    {W Q : ℕ} {x : Σ _n : ℕ, ℕ}
    (hx : x ∈ squarefreeDivisorSigma W Q) :
    (1 : ℝ) / ((x.1 : ℝ) * Nat.totient x.2) =
      divisorQuotientWeight (divisorQuotientEncoding x) := by
  have hxMem := Finset.mem_sigma.mp hx
  have hprod : (x.1 : ℝ) =
      (x.2 : ℝ) * (x.1 / x.2 : ℕ) := by
    exact_mod_cast (Nat.mul_div_cancel'
      (Nat.dvd_of_mem_divisors hxMem.2)).symm
  unfold divisorQuotientWeight divisorQuotientEncoding
  rw [hprod]
  push_cast
  ring

theorem squarefreeCoprimeInvTotientMean_le
    {W Q : ℕ} (hW : 0 < W) :
    squarefreeCoprimeInvTotientMean W Q ≤
      4 * (Nat.totient W : ℝ) *
        (1 + ((harmonic Q : ℚ) : ℝ) / W) := by
  classical
  let A := squarefreeSupport Q
  let B := coprimeSupport W Q
  let X := squarefreeDivisorSigma W Q
  let f := divisorQuotientEncoding
  let g := divisorQuotientWeight
  have hinj : Set.InjOn f X := divisorQuotientEncoding_injOn
  have himage : X.image f ⊆ A ×ˢ B := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact divisorQuotientEncoding_mem_product hx
  calc
    squarefreeCoprimeInvTotientMean W Q =
        ∑ n ∈ squarefreeCoprimeSupport W Q,
          (1 : ℝ) / Nat.totient n := by
      unfold squarefreeCoprimeInvTotientMean squarefreeCoprimeSupport
      rw [Finset.sum_filter]
    _ = ∑ n ∈ squarefreeCoprimeSupport W Q,
          ∑ d ∈ n.divisors, (1 : ℝ) / ((n : ℝ) * Nat.totient d) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact squarefree_inv_totient_eq_divisor_convolution
        (Finset.mem_filter.mp hn).2.1
    _ = ∑ x ∈ X, (1 : ℝ) / ((x.1 : ℝ) * Nat.totient x.2) := by
      unfold X squarefreeDivisorSigma
      rw [Finset.sum_sigma']
    _ = ∑ x ∈ X, g (f x) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact divisorConvolutionTerm_eq_weight hx
    _ = ∑ z ∈ X.image f, g z := by
      rw [Finset.sum_image]
      intro a ha b hb hab
      exact hinj ha hb hab
    _ ≤ ∑ z ∈ A ×ˢ B, g z := by
      apply Finset.sum_le_sum_of_subset_of_nonneg himage
      intro z hz hzNot
      unfold g divisorQuotientWeight
      positivity
    _ = squarefreeInvNatTotientSum Q * coprimeHarmonicSum W Q := by
      unfold A B g squarefreeSupport coprimeSupport
        squarefreeInvNatTotientSum coprimeHarmonicSum
      rw [Finset.sum_product]
      calc
        (∑ d ∈ (Finset.Icc 1 Q).filter Squarefree,
            ∑ m ∈ (Finset.Icc 1 Q).filter (Nat.Coprime · W),
              divisorQuotientWeight (d, m)) =
            ∑ d ∈ (Finset.Icc 1 Q).filter Squarefree,
              ((1 : ℝ) / ((d : ℝ) * Nat.totient d)) *
              (∑ m ∈ (Finset.Icc 1 Q).filter (Nat.Coprime · W),
                (1 : ℝ) / m) := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m hm
          unfold divisorQuotientWeight
          rfl
        _ = (∑ d ∈ Finset.Icc 1 Q,
              if Squarefree d then
                (1 : ℝ) / ((d : ℝ) * Nat.totient d) else 0) *
            (∑ m ∈ (Finset.Icc 1 Q).filter (Nat.Coprime · W),
              (1 : ℝ) / m) := by
          rw [← Finset.sum_filter]
          rw [Finset.sum_mul]
    _ ≤ 4 * coprimeHarmonicSum W Q := by
      apply mul_le_mul_of_nonneg_right (squarefreeInvNatTotientSum_le_four Q)
      unfold coprimeHarmonicSum
      positivity
    _ ≤ 4 * (Nat.totient W : ℝ) *
        (1 + ((harmonic Q : ℚ) : ℝ) / W) := by
      have hcop := coprimeHarmonicSum_le (Q := Q) hW
      nlinarith

theorem squarefreeCoprimeInvTotientMean_le_log
    {W Q : ℕ} (hW : 0 < W)
    (hWL : (W : ℝ) ≤ 1 + Real.log Q) :
    squarefreeCoprimeInvTotientMean W Q ≤
      8 * ((Nat.totient W : ℝ) / W) * (1 + Real.log Q) := by
  have hbase := squarefreeCoprimeInvTotientMean_le (Q := Q) hW
  have hWR : (0 : ℝ) < W := by exact_mod_cast hW
  have hharm : ((harmonic Q : ℚ) : ℝ) ≤ 1 + Real.log Q :=
    harmonic_le_one_add_log Q
  have hone : (1 : ℝ) ≤ (1 + Real.log Q) / W :=
    (le_div_iff₀ hWR).2 (by simpa using hWL)
  have hratio : ((harmonic Q : ℚ) : ℝ) / W ≤
      (1 + Real.log Q) / W :=
    div_le_div_of_nonneg_right hharm hWR.le
  have hbracket : 1 + ((harmonic Q : ℚ) : ℝ) / W ≤
      2 * ((1 + Real.log Q) / W) := by linarith
  calc
    squarefreeCoprimeInvTotientMean W Q ≤
        4 * (Nat.totient W : ℝ) *
          (1 + ((harmonic Q : ℚ) : ℝ) / W) := hbase
    _ ≤ 4 * (Nat.totient W : ℝ) *
          (2 * ((1 + Real.log Q) / W)) := by
      exact mul_le_mul_of_nonneg_left hbracket (by positivity)
    _ = 8 * ((Nat.totient W : ℝ) / W) * (1 + Real.log Q) := by ring

end BoundedGaps.Maynard
