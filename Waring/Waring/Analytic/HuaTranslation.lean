import Waring.Analytic.HuaDerivativeContent

/-!
# Hua's translated-polynomial lemma

This file proves the polynomial lemma controlling the child derivative in
Hua's prime-power induction [HUA1957-BOOK, p. 4, Lemma 1.4].  After translating
at a root and removing the exact common coefficient `p`-power, the reduction
modulo `p` has degree at most the parent root multiplicity.
-/

namespace Waring.Analytic

/-- The polynomial `A(x+p*X)` used in Hua's derivative recursion. -/
noncomputable def huaScaledTranslate (p : Nat) (x : Int)
    (A : Polynomial Int) : Polynomial Int :=
  (A.taylor x).comp (Polynomial.C (p : Int) * Polynomial.X)

/-- The exact common coefficient `p`-power exponent of `A(x+p*X)`. -/
noncomputable def huaScaledTranslateExponent (p : Nat) (x : Int)
    (A : Polynomial Int) : Nat :=
  padicValInt p (huaScaledTranslate p x A).content

/-- The translate `A(x+p*X)` after removal of its exact common coefficient
`p`-power. -/
noncomputable def huaScaledTranslateQuotient (p : Nat) (x : Int)
    (A : Polynomial Int) : Polynomial Int :=
  primePowerContentQuotient p (huaScaledTranslate p x A)

/-- Coefficients of `A(x+p*X)` are the Hasse derivatives at `x`, scaled by
the corresponding power of `p`. -/
@[simp] theorem coeff_huaScaledTranslate (p : Nat) (x : Int)
    (A : Polynomial Int) (n : Nat) :
    (huaScaledTranslate p x A).coeff n =
      (Polynomial.hasseDeriv n A).eval x * (p : Int) ^ n := by
  rw [huaScaledTranslate, Polynomial.comp_C_mul_X_coeff,
    Polynomial.taylor_coeff]

/-- Evaluation of a mapped integer Hasse derivative agrees with mapping its
integer evaluation. -/
theorem map_eval_hasseDeriv (p : Nat) (x : Int) (A : Polynomial Int)
    (n : Nat) :
    (((Polynomial.hasseDeriv n A).eval x : Int) : ZMod p) =
      (Polynomial.hasseDeriv n
        (A.map (Int.castRingHom (ZMod p)))).eval (x : ZMod p) := by
  rw [← map_hasseDeriv]
  change (Int.castRingHom (ZMod p))
      ((Polynomial.hasseDeriv n A).eval x) =
    Polynomial.eval ((Int.castRingHom (ZMod p)) x)
      ((Polynomial.hasseDeriv n A).map (Int.castRingHom (ZMod p)))
  rw [Polynomial.eval_map_apply]

/-- The Hasse derivative at the root multiplicity of a nonzero polynomial
does not vanish. -/
theorem eval_hasseDeriv_rootMultiplicity_ne_zero
    {K : Type*} [Field K] (A : Polynomial K) (x : K) (hA : A ≠ 0) :
    (Polynomial.hasseDeriv (Polynomial.rootMultiplicity x A) A).eval x ≠
      0 := by
  let r := Polynomial.rootMultiplicity x A
  have htaylor : A.taylor x ≠ 0 :=
    (Polynomial.taylor_eq_zero x A).not.mpr hA
  have hr : r = (A.taylor x).natTrailingDegree := by
    simpa only [r, Polynomial.taylor_apply] using
      (Polynomial.rootMultiplicity_eq_natTrailingDegree (p := A) (t := x))
  have hcoeff : (A.taylor x).coeff r ≠ 0 := by
    rw [hr]
    exact Polynomial.coeff_natTrailingDegree_ne_zero.mpr htaylor
  simpa only [r, Polynomial.taylor_coeff] using hcoeff

/-- Scaling the variable by a nonzero prime and translating cannot annihilate
a nonzero integer polynomial. -/
theorem huaScaledTranslate_ne_zero {p : Nat} [Fact p.Prime]
    (x : Int) (A : Polynomial Int) (hA : A ≠ 0) :
    huaScaledTranslate p x A ≠ 0 := by
  rw [huaScaledTranslate, ne_eq, Polynomial.comp_eq_zero_iff]
  push Not
  constructor
  · exact (Polynomial.taylor_eq_zero x A).not.mpr hA
  intro _ heq
  have hcoeff := congrArg (fun F : Polynomial Int ↦ F.coeff 1) heq
  have hpzero : p = 0 := by
    simpa [Mathlib.Tactic.ComputeDegree.coeff_intCast_ite] using hcoeff
  exact (Fact.out : p.Prime).ne_zero hpzero

/-- The common coefficient exponent of `A(x+p*X)` is at most the root
multiplicity of `x` in `A mod p`. -/
theorem huaScaledTranslateExponent_le_rootMultiplicity
    {p : Nat} [Fact p.Prime] (x : Int) (A : Polynomial Int)
    (hmap : A.map (Int.castRingHom (ZMod p)) ≠ 0) :
    huaScaledTranslateExponent p x A ≤
      Polynomial.rootMultiplicity (x : ZMod p)
        (A.map (Int.castRingHom (ZMod p))) := by
  let P := A.map (Int.castRingHom (ZMod p))
  let r := Polynomial.rootMultiplicity (x : ZMod p) P
  let u := huaScaledTranslateExponent p x A
  change u ≤ r
  have hpne : (p : Int) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hhasseP :
      (Polynomial.hasseDeriv r P).eval (x : ZMod p) ≠ 0 :=
    eval_hasseDeriv_rootMultiplicity_ne_zero P (x : ZMod p) hmap
  have hhasse :
      ¬(p : Int) ∣ (Polynomial.hasseDeriv r A).eval x := by
    intro hdiv
    apply hhasseP
    have hzero :
        (((Polynomial.hasseDeriv r A).eval x : Int) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdiv
    rw [map_eval_hasseDeriv] at hzero
    exact hzero
  have hpowContent :
      (p : Int) ^ u ∣ (huaScaledTranslate p x A).content :=
    padicValInt_dvd (huaScaledTranslate p x A).content
  by_contra hle
  have hru : r < u := Nat.lt_of_not_ge hle
  have hpow : (p : Int) ^ (r + 1) ∣ (p : Int) ^ u :=
    pow_dvd_pow (p : Int) (by omega)
  have hdivCoeff :
      (p : Int) ^ (r + 1) ∣ (huaScaledTranslate p x A).coeff r :=
    hpow.trans (hpowContent.trans (Polynomial.content_dvd_coeff r))
  rw [coeff_huaScaledTranslate] at hdivCoeff
  have hpowne : (p : Int) ^ r ≠ 0 := pow_ne_zero _ hpne
  have hpdiv : (p : Int) ∣ (Polynomial.hasseDeriv r A).eval x := by
    rw [pow_succ'] at hdivCoeff
    exact (Int.mul_dvd_mul_iff_right hpowne).mp (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hdivCoeff)
  exact hhasse hpdiv

/-- Hua's Lemma 1.4: after exact content normalization, the reduction of
`A(x+p*X)` has degree at most the multiplicity of `x` as a root of `A mod p`. -/
theorem natDegree_map_huaScaledTranslateQuotient_le_rootMultiplicity
    {p : Nat} [Fact p.Prime] (x : Int) (A : Polynomial Int)
    (hmap : A.map (Int.castRingHom (ZMod p)) ≠ 0) :
    ((huaScaledTranslateQuotient p x A).map
      (Int.castRingHom (ZMod p))).natDegree ≤
        Polynomial.rootMultiplicity (x : ZMod p)
          (A.map (Int.castRingHom (ZMod p))) := by
  let B := huaScaledTranslate p x A
  let Q := huaScaledTranslateQuotient p x A
  let u := huaScaledTranslateExponent p x A
  let r := Polynomial.rootMultiplicity (x : ZMod p)
    (A.map (Int.castRingHom (ZMod p)))
  change (Q.map (Int.castRingHom (ZMod p))).natDegree ≤ r
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hrn
  have hur : u ≤ r :=
    huaScaledTranslateExponent_le_rootMultiplicity x A hmap
  have hun : u + 1 ≤ n := by omega
  have hpow : (p : Int) ^ (u + 1) ∣ (p : Int) ^ n :=
    pow_dvd_pow (p : Int) hun
  have hdivB : (p : Int) ^ (u + 1) ∣ B.coeff n := by
    dsimp only [B]
    rw [coeff_huaScaledTranslate]
    exact dvd_mul_of_dvd_right hpow _
  have hfactor : B = Polynomial.C ((p : Int) ^ u) * Q := by
    dsimp only [B, Q, u]
    exact eq_C_pow_mul_primePowerContentQuotient p
      (huaScaledTranslate p x A)
  have hcoeff := congrArg (fun G : Polynomial Int ↦ G.coeff n) hfactor
  have hcoeff' : B.coeff n = (p : Int) ^ u * Q.coeff n := by
    simpa only [Polynomial.coeff_C_mul] using hcoeff
  rw [hcoeff'] at hdivB
  have hpne : (p : Int) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpowne : (p : Int) ^ u ≠ 0 := pow_ne_zero _ hpne
  have hpdiv : (p : Int) ∣ Q.coeff n := by
    rw [pow_succ] at hdivB
    exact (Int.mul_dvd_mul_iff_left hpowne).mp hdivB
  rw [Polynomial.coeff_map]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hpdiv

/-- The quotient in Hua's Lemma 1.4 is nonzero modulo `p`. -/
theorem map_huaScaledTranslateQuotient_ne_zero
    {p : Nat} [Fact p.Prime] (x : Int) (A : Polynomial Int) (hA : A ≠ 0) :
    (huaScaledTranslateQuotient p x A).map
        (Int.castRingHom (ZMod p)) ≠ 0 := by
  exact map_primePowerContentQuotient_ne_zero _
    (huaScaledTranslate_ne_zero x A hA)

end Waring.Analytic
