import Waring.Analytic.HuaCriticalBlocks

/-!
# Long-range estimates in Hua's induction

This file turns the exact root-block decomposition into a norm bound and
records the two real-power inequalities for nonterminal and terminal blocks.
-/

namespace Waring.Analytic

open scoped BigOperators

/-- The triangle inequality bounds a formal complete sum by its modulus. -/
theorem norm_integerFormalPolynomialCompleteSum_le_modulus
    (q : Nat) [NeZero q] (F : Polynomial Int) :
    ‖integerFormalPolynomialCompleteSum (q := q) F‖ ≤ q := by
  rw [integerFormalPolynomialCompleteSum]
  calc
    ‖∑ x : ZMod q,
        ZMod.stdAddChar
          ((F.map (Int.castRingHom (ZMod q))).eval x)‖ ≤
      ∑ x : ZMod q,
        ‖ZMod.stdAddChar
          ((F.map (Int.castRingHom (ZMod q))).eval x)‖ :=
      norm_sum_le _ _
    _ = q := by simp

/-- Cancellation and the triangle inequality reduce a long complete sum to
the norms of its surviving normalized-derivative root blocks. -/
theorem norm_integerFormalPolynomialCompleteSum_le_huaCriticalBlocks
    {p t m : Nat} [Fact p.Prime] [NeZero p] [NeZero m]
    (hm : p ^ (t + 1) ∣ m) (F D : Polynomial Int)
    (hderivative : F.derivative = Polynomial.C ((p : Int) ^ t) * D)
    (hD : D.map (Int.castRingHom (ZMod p)) ≠ 0) :
    ‖integerFormalPolynomialCompleteSum
        (q := p ^ (t + 1) * m) F‖ ≤
      ∑ x ∈ (D.map (Int.castRingHom (ZMod p))).roots.toFinset,
        ‖huaCriticalBlockSum (q := p ^ (t + 1) * m)
          p (p ^ t * m) (x.val : Int) F‖ := by
  rw [integerFormalPolynomialCompleteSum_eq_sum_huaRootBlocks
    hm F D hderivative hD]
  calc
    ‖∑ x ∈ (D.map (Int.castRingHom (ZMod p))).roots.toFinset,
        ∑ k : Fin (p ^ t * m),
          ZMod.stdAddChar
            ((F.map (Int.castRingHom
              (ZMod (p ^ (t + 1) * m)))).eval
                (((huaRootBlockIndex p t m x k).val : Nat) :
                  ZMod (p ^ (t + 1) * m)))‖ ≤
      ∑ x ∈ (D.map (Int.castRingHom (ZMod p))).roots.toFinset,
        ‖∑ k : Fin (p ^ t * m),
          ZMod.stdAddChar
            ((F.map (Int.castRingHom
              (ZMod (p ^ (t + 1) * m)))).eval
                (((huaRootBlockIndex p t m x k).val : Nat) :
                  ZMod (p ^ (t + 1) * m)))‖ := norm_sum_le _ _
    _ = ∑ x ∈ (D.map (Int.castRingHom (ZMod p))).roots.toFinset,
        ‖huaCriticalBlockSum (q := p ^ (t + 1) * m)
          p (p ^ t * m) (x.val : Int) F‖ := by
      apply Finset.sum_congr rfl
      intro x _
      rw [sum_huaRootBlock_eq_mul_huaCriticalBlockSum, norm_mul]
      simp

/-- Prime-power form of the preceding critical-block reduction. -/
theorem norm_integerFormalPolynomialCompleteSum_primePower_le_huaCriticalBlocks
    {p l : Nat} [Fact p.Prime] [NeZero p]
    {F : Polynomial Int} (phase : HuaPhaseData p F)
    (hlong : 2 * (phase.derivativeData.exponent + 1) ≤ l) :
    ‖integerFormalPolynomialCompleteSum (q := p ^ l) F‖ ≤
      ∑ x ∈ phase.roots,
        ‖huaCriticalBlockSum (q := p ^ l)
          p (p ^ (l - 1)) (x.val : Int) F‖ := by
  let t := phase.derivativeData.exponent
  let m := p ^ (l - t - 1)
  have hbetween : t + 1 ≤ l - t - 1 := by
    dsimp only [t] at hlong ⊢
    omega
  have hm : p ^ (t + 1) ∣ m := by
    dsimp only [m]
    exact pow_dvd_pow p hbetween
  have hmodulus : p ^ (t + 1) * m = p ^ l := by
    dsimp only [m]
    rw [← pow_add]
    congr 1
    dsimp only [t] at hlong ⊢
    omega
  have hlength : p ^ t * m = p ^ (l - 1) := by
    dsimp only [m]
    rw [← pow_add]
    congr 1
    dsimp only [t] at hlong ⊢
    omega
  have hbound := norm_integerFormalPolynomialCompleteSum_le_huaCriticalBlocks
    hm F phase.derivativeData.normalized
      phase.derivativeData.derivative_eq
      phase.derivativeData.map_normalized_ne_zero
  change ‖integerFormalPolynomialCompleteSum
      (q := p ^ (t + 1) * m) F‖ ≤
    ∑ x ∈ phase.roots,
      ‖huaCriticalBlockSum (q := p ^ (t + 1) * m)
        p (p ^ t * m) (x.val : Int) F‖ at hbound
  simpa only [hmodulus, hlength] using hbound

/-- The nonterminal quotient and repetition factor fits the ambient
`p^(4*l/5)` scale because every critical exponent is at most five. -/
theorem hua_nonterminal_block_scale_le
    (p l sigma : Nat) (hp : 1 ≤ p) (hsigmaL : sigma ≤ l)
    (hsigmaFive : sigma ≤ 5) :
    ((p ^ (sigma - 1) : Nat) : Real) *
        (p : Real) ^ (((4 * (l - sigma) : Nat) : Real) / 5) ≤
      (p : Real) ^ (((4 * l : Nat) : Real) / 5) := by
  have hpOne : (1 : Real) ≤ p := by exact_mod_cast hp
  have hNat :
      5 * (sigma - 1) + 4 * (l - sigma) ≤ 4 * l := by
    omega
  have hNatReal :
      ((5 * (sigma - 1) + 4 * (l - sigma) : Nat) : Real) ≤
        ((4 * l : Nat) : Real) := by
    exact_mod_cast hNat
  have hExponent :
      ((sigma - 1 : Nat) : Real) +
          ((4 * (l - sigma) : Nat) : Real) / 5 ≤
        ((4 * l : Nat) : Real) / 5 := by
    push_cast at hNatReal ⊢
    linarith
  rw [Nat.cast_pow, ← Real.rpow_natCast,
    ← Real.rpow_add (by positivity : (0 : Real) < p)]
  exact Real.rpow_le_rpow_of_exponent_le hpOne hExponent

/-- A terminal block also fits the ambient scale when `l ≤ 5`. -/
theorem hua_terminal_block_scale_le
    (p l : Nat) (hp : 1 ≤ p) (hlFive : l ≤ 5) :
    ((p ^ (l - 1) : Nat) : Real) ≤
      (p : Real) ^ (((4 * l : Nat) : Real) / 5) := by
  have hpOne : (1 : Real) ≤ p := by exact_mod_cast hp
  have hNat : 5 * (l - 1) ≤ 4 * l := by omega
  have hNatReal :
      ((5 * (l - 1) : Nat) : Real) ≤ ((4 * l : Nat) : Real) := by
    exact_mod_cast hNat
  have hExponent :
      ((l - 1 : Nat) : Real) ≤ ((4 * l : Nat) : Real) / 5 := by
    push_cast at hNatReal ⊢
    linarith
  rw [Nat.cast_pow, ← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le hpOne hExponent

/-- In the complementary short range the missing `p^(l/5)` factor is at
most `25`, using only `p < 11` and `p^t ≤ 5`. -/
theorem hua_short_range_scale_le_twentyFive
    (p t l : Nat) (hp : 2 ≤ p) (hpSmall : p < 11)
    (hpt : p ^ t ≤ 5) (hl : l < 2 * (t + 1)) :
    (p : Real) ^ ((l : Real) / 5) ≤ 25 := by
  have ht : t ≤ 2 := by
    by_contra hnot
    have hthree : 3 ≤ t := by omega
    have height : 8 ≤ p ^ t := by
      calc
        8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) hthree
        _ ≤ p ^ t := Nat.pow_le_pow_left hp t
    omega
  have hlFive : l ≤ 5 := by omega
  have hpTen : (p : Real) ≤ 10 := by
    exact_mod_cast (by omega : p ≤ 10)
  calc
    (p : Real) ^ ((l : Real) / 5) ≤
        (10 : Real) ^ ((l : Real) / 5) :=
      Real.rpow_le_rpow (by positivity) hpTen (by positivity)
    _ ≤ (10 : Real) ^ (1 : Real) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hlReal : (l : Real) ≤ 5 := by exact_mod_cast hlFive
      linarith
    _ ≤ 25 := by norm_num

end Waring.Analytic
