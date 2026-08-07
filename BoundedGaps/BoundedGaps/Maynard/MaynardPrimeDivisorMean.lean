import BoundedGaps.Maynard.MaynardYDiagonalCollision

noncomputable section

namespace BoundedGaps.Maynard

open scoped BigOperators

/-! Quotient reindex for the scalar reciprocal-totient mean. -/

def squarefreeCoprimePrimeDivisorSupport
    (W Q p : ℕ) : Finset ℕ :=
  (Finset.Icc 1 Q).filter fun n =>
    Squarefree n ∧ Nat.Coprime n W ∧ p ∣ n

set_option maxRecDepth 2000 in
theorem squarefreeCoprimePrimeDivisorMean_le
    {W Q p : ℕ} (hp : p.Prime) :
    (∑ n ∈ squarefreeCoprimePrimeDivisorSupport W Q p,
        (1 : ℝ) / Nat.totient n) ≤
      (1 : ℝ) / Nat.totient p *
        squarefreeCoprimeInvTotientMean W Q := by
  classical
  let S := squarefreeCoprimePrimeDivisorSupport W Q p
  let T := (Finset.Icc 1 Q).filter fun n =>
    Squarefree n ∧ Nat.Coprime n W
  have hinj : Set.InjOn (fun n : ℕ => n / p) (S : Set ℕ) := by
    intro a ha b hb hab
    have haData := Finset.mem_filter.mp ha
    have hbData := Finset.mem_filter.mp hb
    have haMul : p * (a / p) = a := Nat.mul_div_cancel' haData.2.2.2
    have hbMul : p * (b / p) = b := Nat.mul_div_cancel' hbData.2.2.2
    change a / p = b / p at hab
    calc
      a = p * (a / p) := haMul.symm
      _ = p * (b / p) := by rw [hab]
      _ = b := hbMul
  have himage : S.image (fun n : ℕ => n / p) ⊆ T := by
    intro m hm
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
    have hnData := Finset.mem_filter.mp hn
    have hnInterval := Finset.mem_Icc.mp hnData.1
    have hnPos : 0 < n := hnInterval.1
    have hndvd := hnData.2.2.2
    have hmDvd : n / p ∣ n := Nat.div_dvd_of_dvd hndvd
    have hmPos : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hnPos hndvd)
      (Nat.pos_of_ne_zero hp.ne_zero)
    have hmSquarefree : Squarefree (n / p) :=
      hnData.2.1.squarefree_of_dvd hmDvd
    have hmCoprime : Nat.Coprime (n / p) W :=
      Nat.Coprime.of_dvd_left hmDvd hnData.2.2.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨hmPos, (Nat.div_le_self _ _).trans hnInterval.2⟩,
      ⟨hmSquarefree, hmCoprime⟩⟩
  have hrewrite :
      (∑ n ∈ S, (1 : ℝ) / Nat.totient n) =
        ∑ m ∈ S.image (fun n : ℕ => n / p),
          (1 : ℝ) / ((Nat.totient p : ℝ) * Nat.totient m) := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro n hn
    have hnData := Finset.mem_filter.mp hn
    have hmul : p * (n / p) = n := Nat.mul_div_cancel' hnData.2.2.2
    have hcopPM : Nat.Coprime p (n / p) := by
      apply Nat.coprime_of_squarefree_mul
      simpa [hmul] using hnData.2.1
    calc
      (1 : ℝ) / Nat.totient n =
          (1 : ℝ) / Nat.totient (p * (n / p)) := by rw [hmul]
      _ = (1 : ℝ) / ((Nat.totient p : ℝ) * Nat.totient (n / p)) := by
        rw [Nat.totient_mul hcopPM]
        push_cast
        rfl
  have hsubsetBound :
      (∑ m ∈ S.image (fun n : ℕ => n / p),
          (1 : ℝ) / ((Nat.totient p : ℝ) * Nat.totient m)) ≤
        ∑ m ∈ T,
          (1 : ℝ) / ((Nat.totient p : ℝ) * Nat.totient m) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg himage
    intro m hm hmNot
    positivity
  have hmean :
      squarefreeCoprimeInvTotientMean W Q =
        ∑ m ∈ T, (1 : ℝ) / Nat.totient m := by
    unfold squarefreeCoprimeInvTotientMean T
    rw [Finset.sum_filter]
  rw [show squarefreeCoprimePrimeDivisorSupport W Q p = S by rfl,
    hrewrite]
  calc
    (∑ m ∈ S.image (fun n : ℕ => n / p),
        (1 : ℝ) / ((Nat.totient p : ℝ) * Nat.totient m)) ≤
        ∑ m ∈ T,
          (1 : ℝ) / ((Nat.totient p : ℝ) * Nat.totient m) := hsubsetBound
    _ = (1 : ℝ) / Nat.totient p *
          ∑ m ∈ T, (1 : ℝ) / Nat.totient m := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      field_simp
    _ = (1 : ℝ) / Nat.totient p *
          squarefreeCoprimeInvTotientMean W Q := by rw [hmean]

def squarefreeCoprimePrimePairMass
    (W Q p : ℕ) : ℝ :=
  ∑ x ∈ squarefreeCoprimePrimeDivisorSupport W Q p,
    ∑ y ∈ squarefreeCoprimePrimeDivisorSupport W Q p,
      ((1 : ℝ) / Nat.totient x) * (1 / Nat.totient y)

theorem squarefreeCoprimePrimePairMass_le
    {W Q p : ℕ} (hp : p.Prime) :
  squarefreeCoprimePrimePairMass W Q p ≤
      ((1 : ℝ) / Nat.totient p *
        squarefreeCoprimeInvTotientMean W Q) ^ 2 := by
  unfold squarefreeCoprimePrimePairMass
  rw [← Finset.sum_mul_sum]
  have hsingle := squarefreeCoprimePrimeDivisorMean_le (W := W) (Q := Q) hp
  simpa [pow_two] using (mul_self_le_mul_self (by positivity) hsingle)

theorem sum_squarefreeCoprimePrimePairMass_le
    {W Q D : ℕ} (hD : 0 < D) :
    (∑ p ∈ roughPrimeSupport D Q,
      squarefreeCoprimePrimePairMass W Q p) ≤
      (squarefreeCoprimeInvTotientMean W Q) ^ 2 *
        (8 / (D : ℝ)) := by
  have hpoint : ∀ p ∈ roughPrimeSupport D Q,
      squarefreeCoprimePrimePairMass W Q p ≤
        (squarefreeCoprimeInvTotientMean W Q) ^ 2 *
          primeTotientSquareWeight p := by
    intro p hpSupport
    have hp : p.Prime :=
      (Finset.mem_filter.mp (show p ∈ roughPrimeSupport D Q from hpSupport)).2
    have hmass := squarefreeCoprimePrimePairMass_le
      (W := W) (Q := Q) hp
    calc
      squarefreeCoprimePrimePairMass W Q p ≤
          ((1 : ℝ) / Nat.totient p *
            squarefreeCoprimeInvTotientMean W Q) ^ 2 := hmass
      _ = (squarefreeCoprimeInvTotientMean W Q) ^ 2 *
            primeTotientSquareWeight p := by
        unfold primeTotientSquareWeight
        ring
  calc
    (∑ p ∈ roughPrimeSupport D Q,
        squarefreeCoprimePrimePairMass W Q p) ≤
        ∑ p ∈ roughPrimeSupport D Q,
          (squarefreeCoprimeInvTotientMean W Q) ^ 2 *
            primeTotientSquareWeight p := by
      apply Finset.sum_le_sum
      intro p hp
      exact hpoint p hp
    _ = (squarefreeCoprimeInvTotientMean W Q) ^ 2 *
          ∑ p ∈ roughPrimeSupport D Q,
            primeTotientSquareWeight p := by
      rw [Finset.mul_sum]
    _ ≤ (squarefreeCoprimeInvTotientMean W Q) ^ 2 * (8 / (D : ℝ)) := by
      apply mul_le_mul_of_nonneg_left
        (roughPrimeWeightSum_le hD)
      positivity

end BoundedGaps.Maynard
