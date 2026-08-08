import Waring.Analytic.HuaRootBlocks

/-!
# Critical root blocks in Hua's induction

This file factors each surviving root block into its constant root phase and
the normalized critical quotient.  It includes the separate terminal branch
needed when the critical content exponent reaches the modulus exponent.
-/

namespace Waring.Analytic

open scoped BigOperators

/-- The translated-difference sum over the high coordinates of one Hua root
block. -/
noncomputable def huaCriticalBlockSum {q : Nat} [NeZero q]
    (p s : Nat) (x : Int) (F : Polynomial Int) : Complex :=
  ∑ k : Fin s, ZMod.stdAddChar
    (((scaledTaylorDifference (p : Int) x F).eval
      (k.val : Int) : Int) : ZMod q)

/-- A root-block index has its expected integer representative. -/
@[simp] theorem huaRootBlockIndex_val (p t m : Nat) [NeZero p]
    (x : ZMod p) (k : Fin (p ^ t * m)) :
    (huaRootBlockIndex p t m x k).val = x.val + p * k.val := by
  cases p with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ p => rfl

/-- The original phase on a root block splits into its constant root value
and the scaled Taylor difference. -/
theorem stdAddChar_huaRootBlockIndex
    {p t m : Nat} [NeZero p] [NeZero m]
    (x : ZMod p) (k : Fin (p ^ t * m)) (F : Polynomial Int) :
    ZMod.stdAddChar
      ((F.map (Int.castRingHom
        (ZMod (p ^ (t + 1) * m)))).eval
          (((huaRootBlockIndex p t m x k).val : Nat) :
            ZMod (p ^ (t + 1) * m))) =
      ZMod.stdAddChar
          ((F.eval (x.val : Int) : Int) :
            ZMod (p ^ (t + 1) * m)) *
        ZMod.stdAddChar
          (((scaledTaylorDifference (p : Int) (x.val : Int) F).eval
            (k.val : Int) : Int) : ZMod (p ^ (t + 1) * m)) := by
  rw [← ZMod.stdAddChar.map_add_eq_mul]
  apply congrArg ZMod.stdAddChar
  rw [huaRootBlockIndex_val]
  have heval :
      (F.map (Int.castRingHom
        (ZMod (p ^ (t + 1) * m)))).eval
          ((x.val + p * k.val : Nat) :
            ZMod (p ^ (t + 1) * m)) =
        ((F.eval ((x.val : Int) + (p : Int) * (k.val : Int)) : Int) :
          ZMod (p ^ (t + 1) * m)) := by
    rw [show ((x.val + p * k.val : Nat) :
          ZMod (p ^ (t + 1) * m)) =
        (Int.castRingHom (ZMod (p ^ (t + 1) * m)))
          ((x.val : Int) + (p : Int) * (k.val : Int)) by simp]
    exact Polynomial.eval_map_apply _ _
  rw [heval, eval_scaledTaylorDifference]
  push_cast
  ring

/-- Factoring the constant character out of a complete root block leaves the
translated critical-block sum. -/
theorem sum_huaRootBlock_eq_mul_huaCriticalBlockSum
    {p t m : Nat} [NeZero p] [NeZero m]
    (x : ZMod p) (F : Polynomial Int) :
    (∑ k : Fin (p ^ t * m),
      ZMod.stdAddChar
        ((F.map (Int.castRingHom
          (ZMod (p ^ (t + 1) * m)))).eval
            (((huaRootBlockIndex p t m x k).val : Nat) :
              ZMod (p ^ (t + 1) * m)))) =
      ZMod.stdAddChar
          ((F.eval (x.val : Int) : Int) :
            ZMod (p ^ (t + 1) * m)) *
        huaCriticalBlockSum (q := p ^ (t + 1) * m)
          p (p ^ t * m) (x.val : Int) F := by
  rw [huaCriticalBlockSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact stdAddChar_huaRootBlockIndex x k F

/-- Cancelling the exact critical content and reindexing repeated periods
gives the child complete sum. -/
theorem huaCriticalBlockSum_eq_repeated_quotient
    (p u r : Nat) [Fact p.Prime] [NeZero p] [NeZero r]
    (x : Int) (F : Polynomial Int) :
    let T := scaledTaylorDifference (p : Int) x F
    let sigma := padicValInt p T.content
    let G := primePowerContentQuotient p T
    huaCriticalBlockSum (q := r * p ^ sigma)
        p (u * r) x F =
      (u : Complex) * integerFormalPolynomialCompleteSum (q := r) G := by
  dsimp only
  let T := scaledTaylorDifference (p : Int) x F
  let sigma := padicValInt p T.content
  let G := primePowerContentQuotient p T
  have hfactor : T = Polynomial.C ((p : Int) ^ sigma) * G := by
    dsimp only [G, sigma, T]
    exact eq_C_pow_mul_primePowerContentQuotient p _
  rw [huaCriticalBlockSum]
  calc
    (∑ k : Fin (u * r),
        ZMod.stdAddChar
          ((T.eval (k.val : Int) : Int) : ZMod (r * p ^ sigma))) =
      ∑ k : Fin (u * r),
        ZMod.stdAddChar
          ((((p : Int) ^ sigma * G.eval (k.val : Int) : Int)) :
            ZMod (r * p ^ sigma)) := by
      apply Finset.sum_congr rfl
      intro k _
      apply congrArg ZMod.stdAddChar
      apply congrArg (fun z : Int ↦ (z : ZMod (r * p ^ sigma)))
      have heval := congrArg
        (fun A : Polynomial Int ↦ A.eval (k.val : Int)) hfactor
      simpa only [Polynomial.eval_mul, Polynomial.eval_C] using heval
    _ = (u : Complex) * ∑ y : Fin r,
        ZMod.stdAddChar ((G.eval (y.val : Int) : Int) : ZMod r) := by
      exact sum_scaled_polynomial_phase_repeated u r (p ^ sigma) G
    _ = (u : Complex) *
        integerFormalPolynomialCompleteSum (q := r) G := by
      rw [integerFormalPolynomialCompleteSum_eq_fin]

/-- Nonterminal prime-power block formula. -/
theorem huaCriticalBlockSum_primePower_eq_repeated_quotient
    (p l : Nat) [Fact p.Prime] [NeZero p]
    (x : Int) (F : Polynomial Int)
    (hone : 1 ≤ padicValInt p
      (scaledTaylorDifference (p : Int) x F).content)
    (hle : padicValInt p
      (scaledTaylorDifference (p : Int) x F).content ≤ l) :
    let T := scaledTaylorDifference (p : Int) x F
    let sigma := padicValInt p T.content
    let G := primePowerContentQuotient p T
    huaCriticalBlockSum (q := p ^ l) p (p ^ (l - 1)) x F =
      (p ^ (sigma - 1) : Complex) *
        integerFormalPolynomialCompleteSum (q := p ^ (l - sigma)) G := by
  dsimp only
  let T := scaledTaylorDifference (p : Int) x F
  let sigma := padicValInt p T.content
  let G := primePowerContentQuotient p T
  change 1 ≤ sigma at hone
  change sigma ≤ l at hle
  have hlength : p ^ (sigma - 1) * p ^ (l - sigma) =
      p ^ (l - 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hmodulus : p ^ (l - sigma) * p ^ sigma = p ^ l := by
    rw [← pow_add]
    congr 1
    omega
  have hrepeat := huaCriticalBlockSum_eq_repeated_quotient
    p (p ^ (sigma - 1)) (p ^ (l - sigma)) x F
  dsimp only at hrepeat
  change huaCriticalBlockSum (q := p ^ (l - sigma) * p ^ sigma)
      p (p ^ (sigma - 1) * p ^ (l - sigma)) x F =
    ((p ^ (sigma - 1) : Nat) : Complex) *
      integerFormalPolynomialCompleteSum (q := p ^ (l - sigma)) G at hrepeat
  simpa only [hlength, hmodulus, Nat.cast_pow] using hrepeat

/-- Terminal critical blocks have constant translated phase. -/
theorem huaCriticalBlockSum_primePower_eq_card_of_le_exponent
    (p l : Nat) [Fact p.Prime] [NeZero p]
    (x : Int) (F : Polynomial Int)
    (hle : l ≤ padicValInt p
      (scaledTaylorDifference (p : Int) x F).content) :
    huaCriticalBlockSum (q := p ^ l) p (p ^ (l - 1)) x F =
      (p ^ (l - 1) : Complex) := by
  let T := scaledTaylorDifference (p : Int) x F
  let sigma := padicValInt p T.content
  let G := primePowerContentQuotient p T
  change l ≤ sigma at hle
  have hfactor : T = Polynomial.C ((p : Int) ^ sigma) * G := by
    dsimp only [G, sigma, T]
    exact eq_C_pow_mul_primePowerContentQuotient p _
  rw [huaCriticalBlockSum]
  calc
    (∑ k : Fin (p ^ (l - 1)),
      ZMod.stdAddChar ((T.eval (k.val : Int) : Int) : ZMod (p ^ l))) =
        ∑ _k : Fin (p ^ (l - 1)), (1 : Complex) := by
      apply Finset.sum_congr rfl
      intro k _
      have heval := congrArg
        (fun A : Polynomial Int ↦ A.eval (k.val : Int)) hfactor
      have heval' : T.eval (k.val : Int) =
          (p : Int) ^ sigma * G.eval (k.val : Int) := by
        simpa only [Polynomial.eval_mul, Polynomial.eval_C] using heval
      have hpow : (p : Int) ^ l ∣ (p : Int) ^ sigma :=
        pow_dvd_pow (p : Int) hle
      have hdvd : (p : Int) ^ l ∣ T.eval (k.val : Int) := by
        rw [heval']
        exact dvd_mul_of_dvd_left hpow _
      have hcast :
          ((T.eval (k.val : Int) : Int) : ZMod (p ^ l)) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd
      rw [hcast]
      simp
    _ = (p ^ (l - 1) : Complex) := by simp

-- Primality is retained in these reviewed critical-block signatures to keep
-- terminal and recursive cases on one uniform prime-power interface.
attribute [nolint unusedArguments]
  huaCriticalBlockSum_eq_repeated_quotient
  huaCriticalBlockSum_primePower_eq_card_of_le_exponent

end Waring.Analytic
