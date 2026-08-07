import BoundedGaps.Maynard.ConcreteS2OffFaceRiemann
import BoundedGaps.Maynard.MaynardS2OuterPrimeSquareTail
import BoundedGaps.Maynard.MaynardYDiagonalCollisionMass

noncomputable section

namespace BoundedGaps.Maynard

open Filter Set
open scoped BigOperators

theorem maynardS2OuterScalarWeight_prime_le_inv_totient
    {p : ℕ} (hp : p.Prime) :
    maynardS2OuterScalarWeight p ≤ 1 / (Nat.totient p : ℝ) := by
  by_cases hp2 : p = 2
  · subst p
    rw [maynardS2OuterScalarWeight_two, Nat.totient_prime Nat.prime_two]
    norm_num
  · have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hsquare :=
      maynardS2OuterScalarWeight_prime_sq_le_primeTotientSquareWeight hp hp3
    apply (sq_le_sq₀ (maynardS2OuterScalarWeight_prime_nonneg hp)
      (by positivity : 0 ≤ 1 / (Nat.totient p : ℝ))).1
    simpa [primeTotientSquareWeight, div_pow] using hsquare

theorem maynardS2OuterSquarefreeAF_le_reciprocalTotientWeight
    {W n : ℕ} (hn : Squarefree n) (hcop : Nat.Coprime n W) :
    maynardS2OuterSquarefreeAF W n ≤
      1 / (Nat.totient n : ℝ) := by
  have hprime : ∀ p : ℕ, p ∈ n.primeFactors →
      maynardS2OuterScalarWeight p ≤ 1 / (Nat.totient p : ℝ) := by
    intro p hpMem
    exact maynardS2OuterScalarWeight_prime_le_inv_totient
      (Nat.prime_of_mem_primeFactors hpMem)
  have hprod : (∏ p ∈ n.primeFactors,
      maynardS2OuterScalarWeight p) ≤
      ∏ p ∈ n.primeFactors, 1 / (Nat.totient p : ℝ) := by
    apply Finset.prod_le_prod
    · intro p hpMem
      exact maynardS2OuterScalarWeight_prime_nonneg
        (Nat.prime_of_mem_primeFactors hpMem)
    · intro p hpMem
      exact hprime p hpMem
  have hfactor : (∏ p ∈ n.primeFactors,
      1 / (Nat.totient p : ℝ)) = 1 / (Nat.totient n : ℝ) := by
    have hphi := totient_eq_prod_primeFactors_of_squarefree hn
    have hphiR : (Nat.totient n : ℝ) =
        ∏ p ∈ n.primeFactors, (Nat.totient p : ℝ) := by
      exact_mod_cast hphi
    simp only [one_div]
    rw [Finset.prod_inv_distrib, ← hphiR]
  have houter := maynardS2OuterSquarefreeAF_apply_squarefree_of_coprime
    hn hcop
  rw [← maynardS2OuterScalarWeight_prod_eq hn] at houter
  calc
    maynardS2OuterSquarefreeAF W n =
        ∏ p ∈ n.primeFactors, maynardS2OuterScalarWeight p := by
      exact houter
    _ ≤ ∏ p ∈ n.primeFactors, 1 / (Nat.totient p : ℝ) := hprod
    _ = 1 / (Nat.totient n : ℝ) := hfactor
def preSievedCoordinateOuterMass (W R : ℕ) : ℝ :=
  ∑ n ∈ preSievedCommonCoordinateSupport W R,
      maynardS2OuterSquarefreeAF W n
def preSievedPrimeDivisorOuterMass
    (W R p : ℕ) : ℝ :=
  ∑ n ∈ squarefreeCoprimePrimeDivisorSupport W R p,
    maynardS2OuterSquarefreeAF W n

theorem preSievedCoordinateOuterMass_le_outerMean
    (W R : ℕ) :
    preSievedCoordinateOuterMass W R ≤
      maynardS2OuterSquarefreeMean W R := by
  unfold preSievedCoordinateOuterMass
  rw [← maynardS2OuterSquarefreeCoordinateSupport_sum_eq_mean W R]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    have hnData := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨hnData.2.1, (Finset.mem_range.mp hnData.1).le⟩,
      ⟨hnData.2.2.1, hnData.2.2.2⟩⟩
  · intro n hnFull hnNot
    exact maynardS2OuterSquarefreeAF_nonneg W n

set_option maxRecDepth 4000 in
theorem preSievedPrimeDivisorOuterMass_le_scalar_mul_outerMean
    {W R p : ℕ} (hp : p.Prime) :
    preSievedPrimeDivisorOuterMass W R p ≤
      maynardS2OuterScalarWeight p *
        maynardS2OuterSquarefreeMean W R := by
  classical
  let S := squarefreeCoprimePrimeDivisorSupport W R p
  let T := (Finset.Icc 1 R).filter fun n =>
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
      _ = p * (b / p) := congrArg (fun z => p * z) hab
      _ = b := hbMul
  have himage : S.image (fun n : ℕ => n / p) ⊆ T := by
    intro q hq
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hq
    have hnData := Finset.mem_filter.mp hn
    have hnInterval := Finset.mem_Icc.mp hnData.1
    have hndvd := hnData.2.2.2
    have hqDvd : n / p ∣ n := Nat.div_dvd_of_dvd hndvd
    have hqPos : 0 < n / p := Nat.div_pos
      (Nat.le_of_dvd hnInterval.1 hndvd) hp.pos
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨hqPos, (Nat.div_le_self _ _).trans hnInterval.2⟩,
      ⟨hnData.2.1.squarefree_of_dvd hqDvd,
        Nat.Coprime.of_dvd_left hqDvd hnData.2.2.1⟩⟩
  have hrewrite :
      (∑ n ∈ S, maynardS2OuterSquarefreeAF W n) =
        ∑ q ∈ S.image (fun n : ℕ => n / p),
          maynardS2OuterScalarWeight p *
            maynardS2OuterSquarefreeAF W q := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro n hn
    have hnData := Finset.mem_filter.mp hn
    have hmul : p * (n / p) = n := Nat.mul_div_cancel' hnData.2.2.2
    have hcop : Nat.Coprime p (n / p) := by
      apply Nat.coprime_of_squarefree_mul
      simpa [hmul] using hnData.2.1
    rw [show maynardS2OuterSquarefreeAF W n =
        maynardS2OuterSquarefreeAF W (p * (n / p)) by rw [hmul]]
    rw [(maynardS2OuterSquarefreeAF_isMultiplicative W).2 hcop]
    have hnCopW := hnData.2.2.1
    have hnCopW' : Nat.Coprime (p * (n / p)) W := by
      simpa [hmul] using hnCopW
    have hpCopW : Nat.Coprime p W :=
      Nat.Coprime.of_dvd_left (Nat.dvd_mul_right p (n / p))
        hnCopW'
    have hpAF : maynardS2OuterSquarefreeAF W p =
        maynardS2OuterScalarWeight p := by
      exact maynardS2OuterSquarefreeAF_apply_squarefree_of_coprime
        hp.squarefree hpCopW
    rw [hpAF]
  rw [show preSievedPrimeDivisorOuterMass W R p =
      ∑ n ∈ S, maynardS2OuterSquarefreeAF W n by rfl, hrewrite]
  calc
    _ ≤ ∑ q ∈ T, maynardS2OuterScalarWeight p *
        maynardS2OuterSquarefreeAF W q := by
      apply Finset.sum_le_sum_of_subset_of_nonneg himage
      intro q hq hqNot
      exact mul_nonneg
        (maynardS2OuterScalarWeight_prime_nonneg hp)
        (maynardS2OuterSquarefreeAF_nonneg W q)
    _ = maynardS2OuterScalarWeight p *
        maynardS2OuterSquarefreeMean W R := by
      have hmean : (∑ q ∈ T, maynardS2OuterSquarefreeAF W q) =
          maynardS2OuterSquarefreeMean W R := by
        simpa [T, squarefreeCoprimeCoordinateSupport] using
          (maynardS2OuterSquarefreeCoordinateSupport_sum_eq_mean W R)
      rw [← Finset.mul_sum]
      rw [hmean]

def outerTupleWeight (H : Finset ℕ) (W : ℕ) (u : H → ℕ) : ℝ :=
  ∏ h : H, maynardS2OuterSquarefreeAF W (u h)

def outerCoordinatePrimeCollisionBox
    (H : Finset ℕ) (W R : ℕ) (a b : H) (p : ℕ) :
    Finset (H → ℕ) :=
  coordinatePrimeCollisionBox H W R a b p

theorem outerTupleWeight_sum_primeCollision_le_box
    {H : Finset ℕ} {R W : ℕ} {a b : H} {p : ℕ} :
    (∑ u ∈ (preSievedSimplexTupleSupport H R W).filter
        (fun u => p ∣ u a ∧ p ∣ u b), outerTupleWeight H W u) ≤
      ∏ h : H, ∑ n ∈
        (if h = a ∨ h = b then
          squarefreeCoprimePrimeDivisorSupport W R p
        else preSievedCommonCoordinateSupport W R),
        maynardS2OuterSquarefreeAF W n := by
  calc
    _ ≤ ∑ u ∈ outerCoordinatePrimeCollisionBox H W R a b p,
        outerTupleWeight H W u := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro u hu
        have huData := Finset.mem_filter.mp hu
        exact mem_coordinatePrimeCollisionBox_of_independent huData.1
          huData.2.1 huData.2.2
      · intro u huBox huNot
        exact Finset.prod_nonneg (fun h hh =>
          maynardS2OuterSquarefreeAF_nonneg W (u h))
    _ = _ := by
      unfold outerCoordinatePrimeCollisionBox outerTupleWeight
      exact (Finset.prod_univ_sum (fun h : H =>
        if h = a ∨ h = b then
          squarefreeCoprimePrimeDivisorSupport W R p
        else preSievedCommonCoordinateSupport W R)
        (fun h : H => fun n => maynardS2OuterSquarefreeAF W n)).symm

def preSievedOuterPrimeCollisionScalarMass
    (W R p : ℕ) : ℝ :=
  preSievedPrimeDivisorOuterMass W R p

set_option maxRecDepth 5000 in
theorem outerTupleWeight_sum_primeCollision_le_scalarFactors
    {H : Finset ℕ} {R D : ℕ} {x : (H × H) × ℕ}
    (hx : x ∈ collisionPairPrimeIndex H D R) :
    (∑ u ∈ collisionPairPrimeTupleSupport H R (primorial D) x,
      outerTupleWeight H (primorial D) u) ≤
      (preSievedOuterPrimeCollisionScalarMass
          (primorial D) R x.2) ^ 2 *
        (preSievedCoordinateOuterMass (primorial D) R) ^
          (Fintype.card H - 2) := by
  obtain ⟨habMem, hpMem⟩ := Finset.mem_product.mp hx
  have habData := Finset.mem_filter.mp habMem
  have hab : x.1.1 ≠ x.1.2 := habData.2
  have hbox := outerTupleWeight_sum_primeCollision_le_box
    (H := H) (R := R) (W := primorial D)
    (a := x.1.1) (b := x.1.2) (p := x.2)
  calc
    (∑ u ∈ collisionPairPrimeTupleSupport H R (primorial D) x,
        outerTupleWeight H (primorial D) u) ≤
        ∏ h : H, ∑ n ∈
          (if h = x.1.1 ∨ h = x.1.2 then
            squarefreeCoprimePrimeDivisorSupport (primorial D) R x.2
          else preSievedCommonCoordinateSupport (primorial D) R),
          maynardS2OuterSquarefreeAF (primorial D) n := by
      exact hbox
    _ = (preSievedOuterPrimeCollisionScalarMass
          (primorial D) R x.2) ^ 2 *
        (preSievedCoordinateOuterMass (primorial D) R) ^
          (Fintype.card H - 2) := by
      have hsum : ∀ h : H,
          (∑ n ∈
            (if h = x.1.1 ∨ h = x.1.2 then
              squarefreeCoprimePrimeDivisorSupport (primorial D) R x.2
            else preSievedCommonCoordinateSupport (primorial D) R),
            maynardS2OuterSquarefreeAF (primorial D) n) =
            (if h = x.1.1 ∨ h = x.1.2 then
              preSievedOuterPrimeCollisionScalarMass
                (primorial D) R x.2
            else preSievedCoordinateOuterMass
              (primorial D) R) := by
        intro h
        by_cases hh : h = x.1.1 ∨ h = x.1.2
        · simp only [if_pos hh]
          rfl
        · simp only [if_neg hh]
          rfl
      rw [Finset.prod_congr rfl (fun h _ => hsum h)]
      rw [coordinatePrimeCollisionMass_eq hab]

set_option maxRecDepth 5000 in
theorem outerCollisionWeightSum_le_roughScalarFactorSum
    (H : Finset ℕ) (R D : ℕ) :
    (∑ u ∈ preSievedSimplexCollisionSupport H R (primorial D),
      outerTupleWeight H (primorial D) u) ≤
      ∑ x ∈ collisionPairPrimeIndex H D R,
        (maynardS2OuterScalarWeight x.2 *
            maynardS2OuterSquarefreeMean (primorial D) R) ^ 2 *
          (maynardS2OuterSquarefreeMean (primorial D) R) ^
            (Fintype.card H - 2) := by
  calc
    (∑ u ∈ preSievedSimplexCollisionSupport H R (primorial D),
        outerTupleWeight H (primorial D) u) ≤
        ∑ x ∈ collisionPairPrimeIndex H D R,
          ∑ u ∈ collisionPairPrimeTupleSupport H R (primorial D) x,
            outerTupleWeight H (primorial D) u := by
      have hunion := collisionSupport_subset_pairPrimeUnion H R D
      calc
        _ ≤ ∑ u ∈ collisionPairPrimeTupleUnion H R D,
            outerTupleWeight H (primorial D) u := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hunion
          intro u hu huNot
          exact Finset.prod_nonneg (fun h hh =>
            maynardS2OuterSquarefreeAF_nonneg (primorial D) (u h))
        _ ≤ _ := by
          unfold collisionPairPrimeTupleUnion
          exact sum_biUnion_le_sum _ _ _ (fun u => by
            exact Finset.prod_nonneg (fun h hh =>
              maynardS2OuterSquarefreeAF_nonneg (primorial D) (u h)))
    _ ≤ ∑ x ∈ collisionPairPrimeIndex H D R,
        (maynardS2OuterScalarWeight x.2 *
            maynardS2OuterSquarefreeMean (primorial D) R) ^ 2 *
          (maynardS2OuterSquarefreeMean (primorial D) R) ^
            (Fintype.card H - 2) := by
      apply Finset.sum_le_sum
      intro x hx
      have hp : x.2.Prime :=
        (Finset.mem_filter.mp (Finset.mem_product.mp hx |>.2)).2
      have hP := preSievedPrimeDivisorOuterMass_le_scalar_mul_outerMean
        (W := primorial D) (R := R) (p := x.2) hp
      have hM := preSievedCoordinateOuterMass_le_outerMean
        (primorial D) R
      have hP0 : 0 ≤ preSievedPrimeDivisorOuterMass
          (primorial D) R x.2 := by
        unfold preSievedPrimeDivisorOuterMass
        apply Finset.sum_nonneg
        intro n hn
        exact maynardS2OuterSquarefreeAF_nonneg (primorial D) n
      have hM0 : 0 ≤ preSievedCoordinateOuterMass
          (primorial D) R := by
        unfold preSievedCoordinateOuterMass
        apply Finset.sum_nonneg
        intro n hn
        exact maynardS2OuterSquarefreeAF_nonneg (primorial D) n
      have htarget0 : 0 ≤ maynardS2OuterScalarWeight x.2 *
          maynardS2OuterSquarefreeMean (primorial D) R := by
        exact mul_nonneg
          (maynardS2OuterScalarWeight_prime_nonneg hp)
          (by
            unfold maynardS2OuterSquarefreeMean
            apply Finset.sum_nonneg
            intro n hn
            exact maynardS2OuterSquarefreeAF_nonneg (primorial D) n)
      have hP2 := (sq_le_sq₀ hP0 htarget0).mpr hP
      have hMpow := pow_le_pow_left₀ hM0 hM (Fintype.card H - 2)
      exact (outerTupleWeight_sum_primeCollision_le_scalarFactors hx).trans
        (mul_le_mul hP2 hMpow (by positivity) (by positivity))

set_option maxRecDepth 5000 in
theorem outerCollisionWeightSum_le_explicit
    {H : Finset ℕ} {R D : ℕ} (hD : 2 ≤ D) :
    (∑ u ∈ preSievedSimplexCollisionSupport H R (primorial D),
      outerTupleWeight H (primorial D) u) ≤
      ((offDiagonalPairs H).card : ℝ) *
        (maynardS2OuterSquarefreeMean (primorial D) R) ^
          Fintype.card H * (8 / (D : ℝ)) := by
  let M := maynardS2OuterSquarefreeMean (primorial D) R
  have hrough := outerCollisionWeightSum_le_roughScalarFactorSum H R D
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
        (maynardS2OuterScalarWeight p * M) ^ 2 *
            M ^ (Fintype.card H - 2) =
          M ^ Fintype.card H * (maynardS2OuterScalarWeight p) ^ 2 := by
      intro p
      calc
        (maynardS2OuterScalarWeight p * M) ^ 2 *
              M ^ (Fintype.card H - 2) =
            (maynardS2OuterScalarWeight p) ^ 2 *
              (M ^ 2 * M ^ (Fintype.card H - 2)) := by ring
        _ = (maynardS2OuterScalarWeight p) ^ 2 * M ^ Fintype.card H := by
          rw [← pow_add, hadd]
        _ = M ^ Fintype.card H *
            (maynardS2OuterScalarWeight p) ^ 2 := by ring
    have hMnonneg : 0 ≤ M := by
      unfold M maynardS2OuterSquarefreeMean
      apply Finset.sum_nonneg
      intro n hn
      exact maynardS2OuterSquarefreeAF_nonneg
        (primorial D) n
    calc
      (∑ u ∈ preSievedSimplexCollisionSupport H R (primorial D),
          outerTupleWeight H (primorial D) u) ≤
          ∑ x ∈ collisionPairPrimeIndex H D R,
            (maynardS2OuterScalarWeight x.2 * M) ^ 2 *
              M ^ (Fintype.card H - 2) := by simpa [M] using hrough
      _ = ((offDiagonalPairs H).card : ℝ) *
          (M ^ Fintype.card H *
            ∑ p ∈ roughPrimeSupport D R,
              (maynardS2OuterScalarWeight p) ^ 2) := by
        unfold collisionPairPrimeIndex
        rw [Finset.sum_product]
        simp_rw [hterm]
        simp_rw [← Finset.mul_sum]
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤ ((offDiagonalPairs H).card : ℝ) *
          (M ^ Fintype.card H * (8 / (D : ℝ))) := by
        apply mul_le_mul_of_nonneg_left
        · apply mul_le_mul_of_nonneg_left
            (by
              have htail :=
                sum_maynardS2OuterScalarWeight_sq_prime_tail_le
                  (D := D) (Q := R + 1) hD
              have hset : Finset.Ico (D + 1) (R + 1) =
                  Finset.Icc (D + 1) R := by
                ext p
                simp
              rw [hset] at htail
              simpa [roughPrimeSupport] using htail)
          exact pow_nonneg hMnonneg _
        · positivity
      _ = ((offDiagonalPairs H).card : ℝ) * M ^ Fintype.card H *
          (8 / (D : ℝ)) := by ring

def normalizedEngelsmaS2OffFaceCollisionOuterMass
    (alpha : ℝ) (m : BoundedGaps.engelsmaTuple) (N : ℕ) : ℝ :=
  (∑ u ∈ preSievedSimplexCollisionSupport
      (engelsmaOffFaceFinset m) (engelsmaMaynardRadius alpha N)
        (engelsmaMaynardModulus N),
    outerTupleWeight (engelsmaOffFaceFinset m)
      (engelsmaMaynardModulus N) u) /
    (preSieveSingularSeries (tripleLogCutoff (N - 1)) *
      Real.log (engelsmaMaynardRadius alpha N)) ^
        Fintype.card (engelsmaOffFaceFinset m)

set_option maxRecDepth 7000 in
set_option maxHeartbeats 1200000 in
theorem tendsto_normalizedEngelsmaS2OffFaceCollisionOuterMass_zero
    {alpha : ℝ} (halpha : 0 < alpha)
    (m : BoundedGaps.engelsmaTuple) :
    Tendsto (fun N : ℕ =>
      normalizedEngelsmaS2OffFaceCollisionOuterMass alpha m N)
      atTop (nhds 0) := by
  let H := engelsmaOffFaceFinset m
  let cardH := Fintype.card H
  let base : ℕ → ℝ := fun N =>
    preSieveSingularSeries (tripleLogCutoff (N - 1)) *
      Real.log (engelsmaMaynardRadius alpha N)
  let M : ℕ → ℝ := fun N =>
    maynardS2OuterSquarefreeMean (engelsmaMaynardModulus N)
      (engelsmaMaynardRadius alpha N)
  have hratio : Tendsto (fun N : ℕ => M N / base N)
      atTop (nhds 1) := by
    simpa [M, base] using
      (tendsto_engelsmaS2OuterSquarefreeMean_fractionalRadius_nonneg
        halpha (show (0 : ℝ) ≤ 1 by norm_num))
  have hpow : Tendsto (fun N : ℕ => (M N / base N) ^ cardH)
      atTop (nhds 1) := by simpa using hratio.pow cardH
  have hD : ∀ᶠ N : ℕ in atTop, 2 ≤ tripleLogCutoff (N - 1) := by
    obtain ⟨N₀, hN₀⟩ := exists_tripleLogCutoff_ge 2
    filter_upwards [eventually_ge_atTop (N₀ + 1)] with N hN
    exact hN₀ (N - 1) (by omega)
  have hbase : ∀ᶠ N : ℕ in atTop, 0 < base N := by
    filter_upwards [eventually_one_lt_engelsmaMaynardRadius halpha] with N hRN
    dsimp [base]
    have hS := preSieveSingularSeries_pos (tripleLogCutoff (N - 1))
    have hL : 0 < Real.log (engelsmaMaynardRadius alpha N) := by
      exact Real.log_pos (by exact_mod_cast hRN)
    positivity
  have htail : Tendsto (fun N : ℕ =>
      (8 : ℝ) / (tripleLogCutoff (N - 1) : ℝ)) atTop (nhds 0) := by
    have hDlog : Tendsto (fun N : ℕ =>
        (tripleLogCutoff (N - 1) : ℝ)) atTop atTop := by
      apply tendsto_natCast_atTop_atTop.comp
      exact tendsto_shifted_tripleLogCutoff
    simpa [div_eq_mul_inv] using
      (tendsto_inv_atTop_zero.comp hDlog).const_mul (8 : ℝ)
  have hprod : Tendsto (fun N : ℕ =>
      ((offDiagonalPairs H).card : ℝ) *
        ((8 : ℝ) / (tripleLogCutoff (N - 1) : ℝ)) *
          (M N / base N) ^ cardH) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul htail).mul hpow
  have hnonneg : ∀ᶠ N : ℕ in atTop,
      0 ≤ normalizedEngelsmaS2OffFaceCollisionOuterMass alpha m N := by
    filter_upwards [hbase] with N hbaseN
    unfold normalizedEngelsmaS2OffFaceCollisionOuterMass
    apply div_nonneg
    · apply Finset.sum_nonneg
      intro u hu
      exact Finset.prod_nonneg (fun h hh =>
        maynardS2OuterSquarefreeAF_nonneg (engelsmaMaynardModulus N) (u h))
    · positivity
  apply squeeze_zero' hnonneg ?_ hprod
  filter_upwards [hD, hbase] with N hDN hbaseN
  let D := tripleLogCutoff (N - 1)
  let W := engelsmaMaynardModulus N
  let R := engelsmaMaynardRadius alpha N
  have hraw := outerCollisionWeightSum_le_explicit
    (H := H) (R := R) (D := D) hDN
  have hW : W = primorial D := by
    simp [W, D, engelsmaMaynardModulus]
  have hscale : 0 < base N ^ cardH := by positivity
  have hbound : normalizedEngelsmaS2OffFaceCollisionOuterMass alpha m N ≤
      ((offDiagonalPairs H).card : ℝ) * (8 / (D : ℝ)) *
        (M N / base N) ^ cardH := by
    unfold normalizedEngelsmaS2OffFaceCollisionOuterMass
    change (∑ u ∈ preSievedSimplexCollisionSupport H R W,
        outerTupleWeight H W u) / (base N) ^ cardH ≤ _
    apply (div_le_iff₀ hscale).2
    rw [hW]
    calc
      (∑ u ∈ preSievedSimplexCollisionSupport H R (primorial D),
          outerTupleWeight H (primorial D) u) ≤
          ((offDiagonalPairs H).card : ℝ) * M N ^ cardH *
            (8 / (D : ℝ)) := by
              simpa [M, D, W, R, H, cardH, engelsmaMaynardModulus] using hraw
      _ = (((offDiagonalPairs H).card : ℝ) *
          (8 / (D : ℝ)) * (M N / base N) ^ cardH) *
          base N ^ cardH := by
        rw [div_pow]
        field_simp [hbaseN.ne']
  exact hbound
end BoundedGaps.Maynard
