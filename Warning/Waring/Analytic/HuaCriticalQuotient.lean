import Waring.Analytic.HuaPhaseData

/-!
# Critical quotients in Hua's small-prime induction

This file proves the fixed-degree analogues of Hua's Lemma 1.5 and shows that
the algebraic phase invariant is preserved by every normalized critical
quotient [HUA1957-BOOK, pp. 5-7].
-/

namespace Waring.Analytic

/-- Every positive coefficient of a scaled Taylor difference has the uniform
Hasse-derivative formula. -/
theorem coeff_scaledTaylorDifference_of_pos (scale center : Int)
    (F : Polynomial Int) (n : Nat) (hn : 0 < n) :
    (scaledTaylorDifference scale center F).coeff n =
      (Polynomial.hasseDeriv n F).eval center * scale ^ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  simpa [Nat.succ_eq_add_one] using
    coeff_succ_scaledTaylorDifference scale center F k

/-- At a root of the normalized derivative, every coefficient of the critical
Taylor difference is divisible by `p^2`. -/
theorem prime_sq_dvd_content_scaledTaylorDifference_of_normalized_root
    {p : Nat} [Fact p.Prime] {F : Polynomial Int}
    (phase : HuaPhaseData p F) (x : Int)
    (hroot : (phase.derivativeData.normalized.map
      (Int.castRingHom (ZMod p))).eval (x : ZMod p) = 0) :
    (p : Int) ^ 2 ∣
      (scaledTaylorDifference (p : Int) x F).content := by
  let d := phase.derivativeData
  have hpD : (p : Int) ∣ d.normalized.eval x := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    change (Int.castRingHom (ZMod p)) (d.normalized.eval x) = 0
    rw [← Polynomial.eval_map_apply]
    exact hroot
  have hderivEval : F.derivative.eval x =
      (p : Int) ^ d.exponent * d.normalized.eval x := by
    have h := congrArg (fun A : Polynomial Int ↦ A.eval x) d.derivative_eq
    simpa [Polynomial.eval_mul, Polynomial.eval_C] using h
  rw [Polynomial.dvd_content_iff_C_dvd,
    Polynomial.C_dvd_iff_dvd_coeff]
  intro n
  cases n with
  | zero => simp
  | succ k =>
      rw [coeff_succ_scaledTaylorDifference]
      cases k with
      | zero =>
          have hlinear :
              (p : Int) ^ 2 ∣ F.derivative.eval x * (p : Int) := by
            rw [hderivEval]
            rcases hpD with ⟨z, hz⟩
            refine ⟨(p : Int) ^ d.exponent * z, ?_⟩
            rw [hz]
            ring
          simpa only [zero_add, pow_one, Polynomial.hasseDeriv_one'] using
            hlinear
      | succ k =>
          apply dvd_mul_of_dvd_right
          exact pow_dvd_pow (p : Int) (by omega)

/-- A normalized derivative root has critical content exponent at least two. -/
theorem two_le_padicValInt_content_scaledTaylorDifference
    {p : Nat} [Fact p.Prime] {F : Polynomial Int}
    (phase : HuaPhaseData p F) (x : Int)
    (hroot : (phase.derivativeData.normalized.map
      (Int.castRingHom (ZMod p))).eval (x : ZMod p) = 0) :
    2 ≤ padicValInt p
      (scaledTaylorDifference (p : Int) x F).content := by
  have hdiv :=
    prime_sq_dvd_content_scaledTaylorDifference_of_normalized_root
      phase x hroot
  rw [padicValInt_dvd_iff] at hdiv
  rcases hdiv with hzero | hbound
  · have hcontent :
        (scaledTaylorDifference (p : Int) x F).content ≠ 0 :=
      Polynomial.content_eq_zero_iff.not.mpr
        (phase.scaledTaylorDifference_ne_zero x)
    exact (hcontent hzero).elim
  · exact hbound

/-- Hua's Lemma 1.5 in fixed ambient degree five: the exact common content
exponent of a critical Taylor difference is at most five. -/
theorem padicValInt_content_scaledTaylorDifference_le_five
    {p : Nat} [Fact p.Prime] {F : Polynomial Int}
    (phase : HuaPhaseData p F) (x : Int) :
    padicValInt p
      (scaledTaylorDifference (p : Int) x F).content ≤ 5 := by
  let P := F.map (Int.castRingHom (ZMod p))
  let j := P.natDegree
  let T := scaledTaylorDifference (p : Int) x F
  let sigma := padicValInt p T.content
  change sigma ≤ 5
  have hjFive : j ≤ 5 :=
    Polynomial.natDegree_map_le.trans phase.natDegree_le_five
  have hPcoeffZero : P.coeff 0 = 0 := by
    dsimp only [P]
    rw [Polynomial.coeff_map, phase.coeff_zero]
    simp
  have hjPos : 0 < j := by
    by_contra hj
    have hjzero : j = 0 := Nat.eq_zero_of_not_pos hj
    have hconstant : P = Polynomial.C (P.coeff 0) :=
      Polynomial.eq_C_of_natDegree_eq_zero hjzero
    rw [hPcoeffZero, Polynomial.C_0] at hconstant
    exact phase.map_ne_zero hconstant
  have hhasseP :
      (Polynomial.hasseDeriv j P).eval (x : ZMod p) ≠ 0 := by
    rw [Polynomial.hasseDeriv_natDegree_eq_C, Polynomial.eval_C]
    exact Polynomial.leadingCoeff_ne_zero.mpr phase.map_ne_zero
  have hhasse :
      ¬(p : Int) ∣ (Polynomial.hasseDeriv j F).eval x := by
    intro hdiv
    apply hhasseP
    have hzero :
        (((Polynomial.hasseDeriv j F).eval x : Int) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdiv
    rw [map_eval_hasseDeriv] at hzero
    exact hzero
  have hpowContent : (p : Int) ^ sigma ∣ T.content :=
    padicValInt_dvd T.content
  have hsigmaJ : sigma ≤ j := by
    by_contra hle
    have hjs : j + 1 ≤ sigma := by omega
    have hpow : (p : Int) ^ (j + 1) ∣ (p : Int) ^ sigma :=
      pow_dvd_pow (p : Int) hjs
    have hdiv : (p : Int) ^ (j + 1) ∣ T.coeff j :=
      hpow.trans (hpowContent.trans (Polynomial.content_dvd_coeff j))
    dsimp only [T] at hdiv
    rw [coeff_scaledTaylorDifference_of_pos _ _ _ _ hjPos] at hdiv
    have hpne : (p : Int) ≠ 0 := by
      exact_mod_cast (Fact.out : p.Prime).ne_zero
    have hpowne : (p : Int) ^ j ≠ 0 := pow_ne_zero _ hpne
    have hpdiv : (p : Int) ∣ (Polynomial.hasseDeriv j F).eval x := by
      rw [pow_succ'] at hdiv
      exact (Int.mul_dvd_mul_iff_right hpowne).mp (by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hdiv)
    exact hhasse hpdiv
  exact hsigmaJ.trans hjFive

/-- A normalized critical quotient again carries Hua phase data, and its
normalized derivative-root complexity is at most the multiplicity of the
parent root from which it arose. -/
theorem exists_childHuaPhaseData
    {p : Nat} [Fact p.Prime] {F : Polynomial Int}
    (phase : HuaPhaseData p F) (x : Int) :
    let T := scaledTaylorDifference (p : Int) x F
    let G := primePowerContentQuotient p T
    ∃ child : HuaPhaseData p G,
      child.complexity ≤ phase.multiplicity (x : ZMod p) := by
  dsimp only
  let T := scaledTaylorDifference (p : Int) x F
  let G := primePowerContentQuotient p T
  obtain ⟨dchild, hcomplexity⟩ :=
    exists_childHuaDerivativeData F phase.derivativeData x
  have hfactor : T = Polynomial.C
      ((p : Int) ^ padicValInt p T.content) * G := by
    dsimp only [G]
    exact eq_C_pow_mul_primePowerContentQuotient p T
  have hcoeffZero : G.coeff 0 = 0 := by
    have hcoeff := congrArg (fun A : Polynomial Int ↦ A.coeff 0) hfactor
    rw [coeff_zero_scaledTaylorDifference,
      Polynomial.coeff_C_mul] at hcoeff
    have hpne :
        (p : Int) ^ padicValInt p T.content ≠ 0 := by
      exact pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
    exact (mul_eq_zero.mp hcoeff.symm).resolve_left hpne
  have hdegree : G.natDegree ≤ 5 :=
    (natDegree_primePowerContentQuotient_le p T).trans
      (natDegree_scaledTaylorDifference_le (p : Int) x F 5
        phase.natDegree_le_five)
  have hmap : G.map (Int.castRingHom (ZMod p)) ≠ 0 :=
    map_primePowerContentQuotient_ne_zero T
      (phase.scaledTaylorDifference_ne_zero x)
  exact
    ⟨{ coeff_zero := hcoeffZero
       natDegree_le_five := hdegree
       map_ne_zero := hmap
       derivativeData := dchild },
      hcomplexity⟩

end Waring.Analytic
