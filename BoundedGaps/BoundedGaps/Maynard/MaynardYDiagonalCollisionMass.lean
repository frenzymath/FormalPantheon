import BoundedGaps.Maynard.MaynardYDiagonalCollisionUnion

noncomputable section

namespace BoundedGaps.Maynard

open scoped BigOperators

/-! Final finite reduction of the collision mass to scalar factors.

Source: `Maynard2013v3`, printed Section 6, `eq:S1CoprimeError`, source
lines 488--491. This file is the explicit project reconstruction reviewed in
`SEM-202`--`SEM-204`.
-/

def preSievedCoordinateInvTotientMass (W R : ℕ) : ℝ :=
  ∑ n ∈ preSievedCommonCoordinateSupport W R,
    (1 : ℝ) / Nat.totient n

def preSievedPrimeDivisorInvTotientMass
    (W R p : ℕ) : ℝ :=
  ∑ n ∈ squarefreeCoprimePrimeDivisorSupport W R p,
    (1 : ℝ) / Nat.totient n

set_option maxRecDepth 2000 in
theorem reciprocalTotientTupleWeight_sum_primeCollision_le_scalarFactors
    {H : Finset ℕ} {R D : ℕ} {x : (H × H) × ℕ}
    (hx : x ∈ collisionPairPrimeIndex H D R) :
    (∑ u ∈ collisionPairPrimeTupleSupport H R (primorial D) x,
      reciprocalTotientTupleWeight H u) ≤
      (preSievedPrimeDivisorInvTotientMass (primorial D) R x.2) ^ 2 *
        (preSievedCoordinateInvTotientMass (primorial D) R) ^
          (Fintype.card H - 2) := by
  obtain ⟨habMem, hpMem⟩ := Finset.mem_product.mp hx
  have habData := Finset.mem_filter.mp habMem
  have hab : x.1.1 ≠ x.1.2 := habData.2
  have hbox := reciprocalTotientTupleWeight_sum_primeCollision_le_box
    (H := H) (R := R) (W := primorial D)
    (a := x.1.1) (b := x.1.2) (p := x.2)
  calc
    (∑ u ∈ collisionPairPrimeTupleSupport H R (primorial D) x,
        reciprocalTotientTupleWeight H u) ≤
        ∏ h : H, ∑ n ∈
          (if h = x.1.1 ∨ h = x.1.2 then
            squarefreeCoprimePrimeDivisorSupport (primorial D) R x.2
          else preSievedCommonCoordinateSupport (primorial D) R),
          (1 : ℝ) / Nat.totient n := by
      exact hbox
    _ = (preSievedPrimeDivisorInvTotientMass
          (primorial D) R x.2) ^ 2 *
        (preSievedCoordinateInvTotientMass (primorial D) R) ^
          (Fintype.card H - 2) := by
      have hsum : ∀ h : H,
          (∑ n ∈
            (if h = x.1.1 ∨ h = x.1.2 then
              squarefreeCoprimePrimeDivisorSupport (primorial D) R x.2
            else preSievedCommonCoordinateSupport (primorial D) R),
            (1 : ℝ) / Nat.totient n) =
            (if h = x.1.1 ∨ h = x.1.2 then
              preSievedPrimeDivisorInvTotientMass
                (primorial D) R x.2
            else preSievedCoordinateInvTotientMass
              (primorial D) R) := by
        intro h
        by_cases hh : h = x.1.1 ∨ h = x.1.2 <;>
          simp [hh, preSievedPrimeDivisorInvTotientMass,
            preSievedCoordinateInvTotientMass]
      rw [Finset.prod_congr rfl (fun h _ => hsum h)]
      rw [coordinatePrimeCollisionMass_eq hab]

set_option maxRecDepth 2000 in
theorem collisionWeightSum_le_scalarFactorSum
    (H : Finset ℕ) (R D : ℕ) :
    (∑ u ∈ preSievedSimplexCollisionSupport H R (primorial D),
      reciprocalTotientTupleWeight H u) ≤
      ∑ x ∈ collisionPairPrimeIndex H D R,
        (preSievedPrimeDivisorInvTotientMass (primorial D) R x.2) ^ 2 *
          (preSievedCoordinateInvTotientMass (primorial D) R) ^
            (Fintype.card H - 2) := by
  calc
    (∑ u ∈ preSievedSimplexCollisionSupport H R (primorial D),
        reciprocalTotientTupleWeight H u) ≤
        ∑ x ∈ collisionPairPrimeIndex H D R,
          ∑ u ∈ collisionPairPrimeTupleSupport H R (primorial D) x,
            reciprocalTotientTupleWeight H u :=
      collisionWeightSum_le_pairPrimeSum H R D
    _ ≤ ∑ x ∈ collisionPairPrimeIndex H D R,
        (preSievedPrimeDivisorInvTotientMass (primorial D) R x.2) ^ 2 *
          (preSievedCoordinateInvTotientMass (primorial D) R) ^
            (Fintype.card H - 2) := by
      apply Finset.sum_le_sum
      intro x hx
      exact reciprocalTotientTupleWeight_sum_primeCollision_le_scalarFactors hx

set_option maxRecDepth 2000 in
theorem collisionWeightSum_le_roughScalarFactorSum
    (H : Finset ℕ) (R D : ℕ) :
    (∑ u ∈ preSievedSimplexCollisionSupport H R (primorial D),
      reciprocalTotientTupleWeight H u) ≤
      ∑ x ∈ collisionPairPrimeIndex H D R,
        ((1 : ℝ) / Nat.totient x.2 *
          squarefreeCoprimeInvTotientMean (primorial D) R) ^ 2 *
          (squarefreeCoprimeInvTotientMean (primorial D) R) ^
            (Fintype.card H - 2) := by
  apply le_trans (collisionWeightSum_le_scalarFactorSum H R D)
  apply Finset.sum_le_sum
  intro x hx
  have hxPrime := Finset.mem_product.mp hx |>.2
  have hp : x.2.Prime :=
    (Finset.mem_filter.mp hxPrime).2
  have hP : preSievedPrimeDivisorInvTotientMass
      (primorial D) R x.2 ≤
      (1 : ℝ) / Nat.totient x.2 *
        squarefreeCoprimeInvTotientMean (primorial D) R := by
    simpa [preSievedPrimeDivisorInvTotientMass] using
      (squarefreeCoprimePrimeDivisorMean_le
        (W := primorial D) (Q := R) hp)
  have hM : preSievedCoordinateInvTotientMass
      (primorial D) R ≤
      squarefreeCoprimeInvTotientMean (primorial D) R := by
    simpa [preSievedCoordinateInvTotientMass] using
      preSievedCoordinateInvTotientSum_le (primorial D) R
  have hP0 : 0 ≤ preSievedPrimeDivisorInvTotientMass
      (primorial D) R x.2 := by
    unfold preSievedPrimeDivisorInvTotientMass
    positivity
  have hM0 : 0 ≤ preSievedCoordinateInvTotientMass
      (primorial D) R := by
    unfold preSievedCoordinateInvTotientMass
    positivity
  have hP2 := (sq_le_sq₀ hP0 (hP0.trans hP)).mpr hP
  have hMpow := pow_le_pow_left₀ hM0 hM (Fintype.card H - 2)
  exact mul_le_mul hP2 hMpow (by positivity) (by positivity)

set_option maxRecDepth 2000 in
theorem collisionWeightSum_le_explicit
    {H : Finset ℕ} {R D : ℕ} (hD : 0 < D) :
    (∑ u ∈ preSievedSimplexCollisionSupport H R (primorial D),
      reciprocalTotientTupleWeight H u) ≤
      ((offDiagonalPairs H).card : ℝ) *
        (squarefreeCoprimeInvTotientMean (primorial D) R) ^
          Fintype.card H * (8 / (D : ℝ)) := by
  let M := squarefreeCoprimeInvTotientMean (primorial D) R
  have hrough := collisionWeightSum_le_roughScalarFactorSum H R D
  by_cases hEmpty : offDiagonalPairs H = ∅
  · simpa [collisionPairPrimeIndex, hEmpty] using hrough
  · have hNonempty : (offDiagonalPairs H).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hEmpty
    obtain ⟨ab, habMem⟩ := hNonempty
    have hab : ab.1 ≠ ab.2 :=
      (Finset.mem_filter.mp habMem).2
    have hpairSubset : ({ab.1, ab.2} : Finset H) ⊆ Finset.univ := by
      intro h hh
      exact Finset.mem_univ h
    have hcard : 2 ≤ Fintype.card H := by
      have hcardPair := Finset.card_le_card hpairSubset
      rw [Finset.card_pair hab] at hcardPair
      simpa using hcardPair
    have hadd : 2 + (Fintype.card H - 2) = Fintype.card H :=
      Nat.add_sub_of_le hcard
    have hterm : ∀ p : ℕ,
        ((1 : ℝ) / Nat.totient p * M) ^ 2 *
            M ^ (Fintype.card H - 2) =
          M ^ Fintype.card H * primeTotientSquareWeight p := by
      intro p
      unfold primeTotientSquareWeight
      calc
        ((1 : ℝ) / Nat.totient p * M) ^ 2 *
            M ^ (Fintype.card H - 2) =
            ((1 : ℝ) / Nat.totient p) ^ 2 *
              (M ^ 2 * M ^ (Fintype.card H - 2)) := by ring
        _ = ((1 : ℝ) / Nat.totient p) ^ 2 *
              M ^ Fintype.card H := by rw [← pow_add, hadd]
        _ = M ^ Fintype.card H *
              (1 / (Nat.totient p : ℝ) ^ 2) := by ring
    have hMnonneg : 0 ≤ M := by
      unfold M squarefreeCoprimeInvTotientMean
      apply Finset.sum_nonneg
      intro n hn
      split <;> positivity
    calc
      (∑ u ∈ preSievedSimplexCollisionSupport H R (primorial D),
          reciprocalTotientTupleWeight H u) ≤
          ∑ x ∈ collisionPairPrimeIndex H D R,
            ((1 : ℝ) / Nat.totient x.2 * M) ^ 2 *
              M ^ (Fintype.card H - 2) := by simpa [M] using hrough
      _ = ((offDiagonalPairs H).card : ℝ) *
          (M ^ Fintype.card H *
            ∑ p ∈ roughPrimeSupport D R,
              primeTotientSquareWeight p) := by
        unfold collisionPairPrimeIndex
        rw [Finset.sum_product]
        simp_rw [hterm]
        simp_rw [← Finset.mul_sum]
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤ ((offDiagonalPairs H).card : ℝ) *
          (M ^ Fintype.card H * (8 / (D : ℝ))) := by
        apply mul_le_mul_of_nonneg_left
        · apply mul_le_mul_of_nonneg_left (roughPrimeWeightSum_le hD)
          exact pow_nonneg hMnonneg _
        · positivity
      _ = ((offDiagonalPairs H).card : ℝ) *
          (squarefreeCoprimeInvTotientMean (primorial D) R) ^
            Fintype.card H * (8 / (D : ℝ)) := by
        unfold M
        ring

end BoundedGaps.Maynard
