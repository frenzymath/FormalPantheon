import Waring.Analytic.HuaDerivativeData

/-!
# Normalized derivative recursion in Hua's estimate

This file differentiates a critical translated quotient and constructs its
next normalized derivative.  Together with Hua's translated-polynomial lemma,
this proves that child root complexity is at most the parent root multiplicity
[HUA1957-BOOK, pp. 4, 6-7].
-/

namespace Waring.Analytic

private theorem right_exponent_le_left_exponent_of_C_pow_mul_eq
    {p : Nat} [Fact p.Prime] (a b : Nat) (Q R : Polynomial Int)
    (hQ : Q.map (Int.castRingHom (ZMod p)) ≠ 0)
    (hEq : Polynomial.C ((p : Int) ^ a) * Q =
      Polynomial.C ((p : Int) ^ b) * R) :
    b ≤ a := by
  obtain ⟨n, hn⟩ := exists_coeff_prime_not_dvd_of_map_ne_zero Q hQ
  by_contra hle
  have hab : a + 1 ≤ b := by omega
  have hcoeff := congrArg (fun G : Polynomial Int ↦ G.coeff n) hEq
  simp only [Polynomial.coeff_C_mul] at hcoeff
  have hdivRight :
      (p : Int) ^ (a + 1) ∣ (p : Int) ^ b * R.coeff n :=
    dvd_mul_of_dvd_left (pow_dvd_pow (p : Int) hab) _
  rw [← hcoeff] at hdivRight
  have hpne : (p : Int) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpowne : (p : Int) ^ a ≠ 0 := pow_ne_zero _ hpne
  have hpdiv : (p : Int) ∣ Q.coeff n := by
    rw [pow_succ] at hdivRight
    exact (Int.mul_dvd_mul_iff_left hpowne).mp hdivRight
  exact hn hpdiv

private theorem derivative_eq_C_pow_mul_of_C_pow_mul_eq
    {p : Nat} [Fact p.Prime] (total sigma : Nat)
    (Q G : Polynomial Int) (hle : sigma ≤ total)
    (hEq : Polynomial.C ((p : Int) ^ total) * Q =
      Polynomial.C ((p : Int) ^ sigma) * G.derivative) :
    G.derivative = Polynomial.C ((p : Int) ^ (total - sigma)) * Q := by
  have hsplit : (p : Int) ^ total =
      (p : Int) ^ sigma * (p : Int) ^ (total - sigma) := by
    rw [← pow_add]
    congr 1
    omega
  have hEq' :
      Polynomial.C ((p : Int) ^ sigma) *
          (Polynomial.C ((p : Int) ^ (total - sigma)) * Q) =
        Polynomial.C ((p : Int) ^ sigma) * G.derivative := by
    rw [← mul_assoc, ← Polynomial.C_mul, ← hsplit]
    exact hEq
  have hpne : (p : Int) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hCne : Polynomial.C ((p : Int) ^ sigma) ≠ 0 :=
    Polynomial.C_ne_zero.mpr (pow_ne_zero _ hpne)
  exact (mul_left_cancel₀ hCne hEq').symm

/-- Differentiation and both exact content factorizations give the scalar
identity relating a child derivative to the translated parent normalization. -/
theorem C_pow_mul_huaScaledTranslateQuotient_eq_C_pow_mul_derivative
    {p : Nat} [Fact p.Prime] (F : Polynomial Int)
    (d : HuaDerivativeData p F) (x : Int) :
    let T := scaledTaylorDifference (p : Int) x F
    let sigma := padicValInt p T.content
    let G := primePowerContentQuotient p T
    let u := huaScaledTranslateExponent p x d.normalized
    let Q := huaScaledTranslateQuotient p x d.normalized
    Polynomial.C ((p : Int) ^ (d.exponent + 1 + u)) * Q =
      Polynomial.C ((p : Int) ^ sigma) * G.derivative := by
  dsimp only
  let T := scaledTaylorDifference (p : Int) x F
  let sigma := padicValInt p T.content
  let G := primePowerContentQuotient p T
  let u := huaScaledTranslateExponent p x d.normalized
  let Q := huaScaledTranslateQuotient p x d.normalized
  have htranslate : huaScaledTranslate p x d.normalized =
      Polynomial.C ((p : Int) ^ u) * Q := by
    dsimp only [u, Q]
    exact eq_C_pow_mul_primePowerContentQuotient p
      (huaScaledTranslate p x d.normalized)
  have hTleft : T.derivative =
      Polynomial.C ((p : Int) ^ (d.exponent + 1 + u)) * Q := by
    calc
      T.derivative = Polynomial.C (p : Int) *
          huaScaledTranslate p x F.derivative :=
        derivative_scaledTaylorDifference_eq_C_mul_huaScaledTranslate p x F
      _ = Polynomial.C (p : Int) *
          huaScaledTranslate p x
            (Polynomial.C ((p : Int) ^ d.exponent) * d.normalized) := by
        rw [d.derivative_eq]
      _ = Polynomial.C (p : Int) *
          (Polynomial.C ((p : Int) ^ d.exponent) *
            huaScaledTranslate p x d.normalized) := by
        rw [huaScaledTranslate_C_mul]
      _ = Polynomial.C ((p : Int) ^ (d.exponent + 1 + u)) * Q := by
        rw [htranslate]
        rw [← mul_assoc, ← mul_assoc, ← Polynomial.C_mul,
          ← Polynomial.C_mul]
        congr 2
        rw [pow_add, pow_add]
        ring
  have hfactor : T = Polynomial.C ((p : Int) ^ sigma) * G := by
    dsimp only [T, sigma, G]
    exact eq_C_pow_mul_primePowerContentQuotient p
      (scaledTaylorDifference (p : Int) x F)
  have hTright : T.derivative =
      Polynomial.C ((p : Int) ^ sigma) * G.derivative := by
    rw [hfactor, Polynomial.derivative_C_mul]
  exact hTleft.symm.trans hTright

/-- Every critical quotient admits derivative data whose total root
complexity is bounded by the parent normalized root multiplicity at the chosen
residue.  This is the recursive content of Hua's Lemma 1.4. -/
theorem exists_childHuaDerivativeData
    {p : Nat} [Fact p.Prime] (F : Polynomial Int)
    (d : HuaDerivativeData p F) (x : Int) :
    let T := scaledTaylorDifference (p : Int) x F
    let G := primePowerContentQuotient p T
    ∃ child : HuaDerivativeData p G,
      child.complexity ≤ d.multiplicity (x : ZMod p) := by
  dsimp only
  let T := scaledTaylorDifference (p : Int) x F
  let sigma := padicValInt p T.content
  let G := primePowerContentQuotient p T
  let u := huaScaledTranslateExponent p x d.normalized
  let Q := huaScaledTranslateQuotient p x d.normalized
  let total := d.exponent + 1 + u
  have hQ : Q.map (Int.castRingHom (ZMod p)) ≠ 0 := by
    dsimp only [Q]
    apply map_huaScaledTranslateQuotient_ne_zero
    intro hzero
    apply d.map_normalized_ne_zero
    rw [hzero, Polynomial.map_zero]
  have hscalar : Polynomial.C ((p : Int) ^ total) * Q =
      Polynomial.C ((p : Int) ^ sigma) * G.derivative := by
    simpa only [total, T, sigma, G, u, Q] using
      C_pow_mul_huaScaledTranslateQuotient_eq_C_pow_mul_derivative F d x
  have hsigma : sigma ≤ total :=
    right_exponent_le_left_exponent_of_C_pow_mul_eq
      total sigma Q G.derivative hQ hscalar
  have hderivative : G.derivative =
      Polynomial.C ((p : Int) ^ (total - sigma)) * Q :=
    derivative_eq_C_pow_mul_of_C_pow_mul_eq
      total sigma Q G hsigma hscalar
  let child : HuaDerivativeData p G :=
    { exponent := total - sigma
      normalized := Q
      derivative_eq := hderivative
      map_normalized_ne_zero := hQ }
  refine ⟨child, (child.complexity_le_natDegree).trans ?_⟩
  change (Q.map (Int.castRingHom (ZMod p))).natDegree ≤
    Polynomial.rootMultiplicity (x : ZMod p)
      (d.normalized.map (Int.castRingHom (ZMod p)))
  exact natDegree_map_huaScaledTranslateQuotient_le_rootMultiplicity
    x d.normalized d.map_normalized_ne_zero

-- Primality remains in this checked recursion identity because every
-- `HuaDerivativeData` transition is exposed through the same prime-indexed API.
attribute [nolint unusedArguments]
  C_pow_mul_huaScaledTranslateQuotient_eq_C_pow_mul_derivative

end Waring.Analytic
