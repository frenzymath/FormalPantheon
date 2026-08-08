import Waring.Analytic.HuaPolynomialSum

/-!
# Digit cancellation in Hua's prime-power induction

This file implements the `t+1`-digit decomposition and additive-character
orthogonality in Hua's Lemma 1.6 [HUA1957-BOOK, p. 6].
-/

namespace Waring.Analytic

open scoped BigOperators

/-- Reindex a complete polynomial sum into a low block modulo `m` and
`t+1` further base-`p` digits, then apply the exact linear Taylor identity. -/
theorem integerFormalPolynomialCompleteSum_huaDigit_reindex
    (p t m : Nat) [NeZero p] [NeZero m]
    (hm : p ^ (t + 1) ∣ m) (F D : Polynomial Int)
    (hderivative :
      F.derivative = Polynomial.C ((p : Int) ^ t) * D) :
    integerFormalPolynomialCompleteSum
        (q := p ^ (t + 1) * m) F =
      ∑ y : Fin m,
        ZMod.stdAddChar
          ((F.map (Int.castRingHom
            (ZMod (p ^ (t + 1) * m)))).eval
              ((y.val : Nat) : ZMod (p ^ (t + 1) * m))) *
        ∑ z : Fin (p ^ (t + 1)),
          ZMod.stdAddChar
            ((D.map (Int.castRingHom
              (ZMod (p ^ (t + 1) * m)))).eval
                ((y.val : Nat) : ZMod (p ^ (t + 1) * m)) *
              (((p ^ t * m : Nat) : ZMod (p ^ (t + 1) * m)) *
                ((z.val : Nat) : ZMod (p ^ (t + 1) * m)))) := by
  rw [integerFormalPolynomialCompleteSum]
  rw [← (ZMod.finEquiv (p ^ (t + 1) * m)).toEquiv.sum_comp]
  rw [← (finProdFinEquiv : Fin (p ^ (t + 1)) × Fin m ≃
    Fin (p ^ (t + 1) * m)).sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [show
      (ZMod.finEquiv (p ^ (t + 1) * m)).toEquiv
          (finProdFinEquiv (z, y)) =
        ((y.val : Nat) : ZMod (p ^ (t + 1) * m)) +
          (m : Nat) *
            ((z.val : Nat) : ZMod (p ^ (t + 1) * m)) by
    change ZMod.finEquiv (p ^ (t + 1) * m)
      (finProdFinEquiv (z, y)) = _
    rw [zmod_finEquiv_apply]
    change ((y.val + m * z.val : Nat) :
      ZMod (p ^ (t + 1) * m)) = _
    push_cast
    ring]
  rw [eval_add_huaDigitScale p t m hm F D hderivative]
  rw [ZMod.stdAddChar.map_add_eq_mul]

/-- The `t+1` further digits form a complete linear character sum.  It
survives exactly when the normalized derivative vanishes modulo `p`. -/
theorem huaDigit_inner_sum_eq_ite
    {p t m : Nat} [Fact p.Prime] [NeZero p] [NeZero m]
    (D : Polynomial Int) (y : Fin m) :
    ∑ z : Fin (p ^ (t + 1)),
      ZMod.stdAddChar
        ((D.map (Int.castRingHom (ZMod (p ^ (t + 1) * m)))).eval
            ((y.val : Nat) : ZMod (p ^ (t + 1) * m)) *
          (((p ^ t * m : Nat) : ZMod (p ^ (t + 1) * m)) *
            ((z.val : Nat) : ZMod (p ^ (t + 1) * m)))) =
      if (D.map (Int.castRingHom (ZMod p))).eval
          ((y.val : Nat) : ZMod p) = 0
      then p ^ (t + 1) else 0 := by
  let n := p ^ (t + 1)
  let c : ZMod n :=
    (((p : Int) ^ t * D.eval (y.val : Int) : Int) : ZMod n)
  have hn : n = p ^ t * p := by
    simp [n, pow_succ, mul_comm]
  have hevalp :
      (D.map (Int.castRingHom (ZMod p))).eval
          ((y.val : Nat) : ZMod p) =
        ((D.eval (y.val : Int) : Int) : ZMod p) := by
    rw [show ((y.val : Nat) : ZMod p) =
        (Int.castRingHom (ZMod p)) (y.val : Int) by simp]
    exact Polynomial.eval_map_apply _ _
  have hright :
      (D.map (Int.castRingHom (ZMod p))).eval
          ((y.val : Nat) : ZMod p) = 0 ↔
        (p : Int) ∣ D.eval (y.val : Int) := by
    rw [hevalp]
    exact ZMod.intCast_zmod_eq_zero_iff_dvd _ _
  have hciff : c = 0 ↔
      (D.map (Int.castRingHom (ZMod p))).eval
          ((y.val : Nat) : ZMod p) = 0 := by
    rw [hright]
    change ((((p : Int) ^ t * D.eval (y.val : Int) : Int) :
      ZMod n) = 0 ↔ _)
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    rw [hn]
    norm_cast
    have hpowne : (p : Int) ^ t ≠ 0 := by
      exact pow_ne_zero _ (by
        exact_mod_cast (Fact.out : p.Prime).ne_zero)
    constructor
    · intro hdiv
      have hdiv' : (p : Int) ^ t * (p : Int) ∣
          (p : Int) ^ t * D.eval (y.val : Int) := by
        simpa using hdiv
      exact (Int.mul_dvd_mul_iff_left hpowne).mp hdiv'
    · intro hdiv
      exact Int.mul_dvd_mul_left ((p : Int) ^ t) hdiv
  calc
    ∑ z : Fin (p ^ (t + 1)),
      ZMod.stdAddChar
        ((D.map (Int.castRingHom (ZMod (p ^ (t + 1) * m)))).eval
            ((y.val : Nat) : ZMod (p ^ (t + 1) * m)) *
          (((p ^ t * m : Nat) : ZMod (p ^ (t + 1) * m)) *
            ((z.val : Nat) : ZMod (p ^ (t + 1) * m)))) =
        ∑ z : Fin n,
          ZMod.stdAddChar
            (zmodScale n m ((ZMod.finEquiv n).toEquiv z * c)) := by
      dsimp only [n]
      apply Finset.sum_congr rfl
      intro z _
      apply congrArg ZMod.stdAddChar
      rw [show (ZMod.finEquiv (p ^ (t + 1))).toEquiv z =
          ((z.val : Nat) : ZMod (p ^ (t + 1))) by
        change ZMod.finEquiv (p ^ (t + 1)) z = _
        exact zmod_finEquiv_apply z]
      dsimp only [c, n]
      rw [show
          ((z.val : Nat) : ZMod (p ^ (t + 1))) *
              (((p : Int) ^ t * D.eval (y.val : Int) : Int) :
                ZMod (p ^ (t + 1))) =
            (((z.val : Int) * ((p : Int) ^ t *
              D.eval (y.val : Int)) : Int) :
                ZMod (p ^ (t + 1))) by
        push_cast
        ring]
      rw [zmodScale_intCast]
      have hevalq :
          (D.map (Int.castRingHom
            (ZMod (p ^ (t + 1) * m)))).eval
              ((y.val : Nat) : ZMod (p ^ (t + 1) * m)) =
            ((D.eval (y.val : Int) : Int) :
              ZMod (p ^ (t + 1) * m)) := by
        rw [show ((y.val : Nat) : ZMod (p ^ (t + 1) * m)) =
            (Int.castRingHom (ZMod (p ^ (t + 1) * m)))
              (y.val : Int) by simp]
        exact Polynomial.eval_map_apply _ _
      rw [hevalq]
      push_cast
      ring
    _ = if c = 0 then n else 0 := by
      exact sum_fin_stdAddChar_zmodScale n m c
    _ = if (D.map (Int.castRingHom (ZMod p))).eval
          ((y.val : Nat) : ZMod p) = 0
        then p ^ (t + 1) else 0 := by
      have hif :
          (if c = 0 then n else 0) =
            if (D.map (Int.castRingHom (ZMod p))).eval
                ((y.val : Nat) : ZMod p) = 0
            then p ^ (t + 1) else 0 :=
        if_congr hciff (by simp [n]) rfl
      exact_mod_cast hif

/-- After the `t+1`-digit character sum is evaluated, only low residues at
which the normalized derivative vanishes remain. -/
theorem integerFormalPolynomialCompleteSum_eq_huaLowResidues
    {p t m : Nat} [Fact p.Prime] [NeZero p] [NeZero m]
    (hm : p ^ (t + 1) ∣ m) (F D : Polynomial Int)
    (hderivative :
      F.derivative = Polynomial.C ((p : Int) ^ t) * D) :
    integerFormalPolynomialCompleteSum
        (q := p ^ (t + 1) * m) F =
      ∑ y : Fin m,
        if (D.map (Int.castRingHom (ZMod p))).eval
            ((y.val : Nat) : ZMod p) = 0
        then (p ^ (t + 1) : Nat) *
          ZMod.stdAddChar
            ((F.map (Int.castRingHom
              (ZMod (p ^ (t + 1) * m)))).eval
                ((y.val : Nat) : ZMod (p ^ (t + 1) * m)))
        else 0 := by
  rw [integerFormalPolynomialCompleteSum_huaDigit_reindex
    p t m hm F D hderivative]
  apply Finset.sum_congr rfl
  intro y _
  rw [huaDigit_inner_sum_eq_ite D y]
  split_ifs <;> simp_all [mul_comm]

/-- Equivalently, cancellation simply discards every full-modulus residue
whose low base-`p` digit is not a normalized derivative root. -/
theorem integerFormalPolynomialCompleteSum_eq_huaSurvivingResidues
    {p t m : Nat} [Fact p.Prime] [NeZero p] [NeZero m]
    (hm : p ^ (t + 1) ∣ m) (F D : Polynomial Int)
    (hderivative :
      F.derivative = Polynomial.C ((p : Int) ^ t) * D) :
    integerFormalPolynomialCompleteSum
        (q := p ^ (t + 1) * m) F =
      ∑ a : Fin (p ^ (t + 1) * m),
        if (D.map (Int.castRingHom (ZMod p))).eval
            ((a.val : Nat) : ZMod p) = 0
        then ZMod.stdAddChar
          ((F.map (Int.castRingHom
            (ZMod (p ^ (t + 1) * m)))).eval
              ((a.val : Nat) : ZMod (p ^ (t + 1) * m)))
        else 0 := by
  rw [integerFormalPolynomialCompleteSum_eq_huaLowResidues
    hm F D hderivative]
  rw [← (finProdFinEquiv : Fin (p ^ (t + 1)) × Fin m ≃
    Fin (p ^ (t + 1) * m)).sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  have hpdiv : p ∣ m :=
    (dvd_pow_self p (Nat.succ_ne_zero t)).trans hm
  have hindexMod (z : Fin (p ^ (t + 1))) :
      (((finProdFinEquiv (z, y)).val : Nat) : ZMod p) =
        ((y.val : Nat) : ZMod p) := by
    change ((y.val + m * z.val : Nat) : ZMod p) = _
    push_cast
    rw [show ((m : Nat) : ZMod p) = 0 by
      exact (ZMod.natCast_eq_zero_iff m p).mpr hpdiv]
    simp
  by_cases hy : (D.map (Int.castRingHom (ZMod p))).eval
      ((y.val : Nat) : ZMod p) = 0
  · rw [if_pos hy]
    have hrootIndex (z : Fin (p ^ (t + 1))) :
        (D.map (Int.castRingHom (ZMod p))).eval
            (((finProdFinEquiv (z, y)).val : Nat) : ZMod p) = 0 := by
      rw [hindexMod z]
      exact hy
    have hevalDp :
        (D.map (Int.castRingHom (ZMod p))).eval
            ((y.val : Nat) : ZMod p) =
          ((D.eval (y.val : Int) : Int) : ZMod p) := by
      rw [show ((y.val : Nat) : ZMod p) =
          (Int.castRingHom (ZMod p)) (y.val : Int) by simp]
      exact Polynomial.eval_map_apply _ _
    have hdvd : (p : Int) ∣ D.eval (y.val : Int) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      rw [← hevalDp]
      exact hy
    have hphase (z : Fin (p ^ (t + 1))) :
        (F.map (Int.castRingHom
          (ZMod (p ^ (t + 1) * m)))).eval
            (((finProdFinEquiv (z, y)).val : Nat) :
              ZMod (p ^ (t + 1) * m)) =
          (F.map (Int.castRingHom
            (ZMod (p ^ (t + 1) * m)))).eval
              ((y.val : Nat) : ZMod (p ^ (t + 1) * m)) := by
      rw [show
          (((finProdFinEquiv (z, y)).val : Nat) :
              ZMod (p ^ (t + 1) * m)) =
            ((y.val : Nat) : ZMod (p ^ (t + 1) * m)) +
              (m : Nat) *
                ((z.val : Nat) : ZMod (p ^ (t + 1) * m)) by
        change ((y.val + m * z.val : Nat) :
          ZMod (p ^ (t + 1) * m)) = _
        push_cast
        ring]
      rw [eval_add_huaDigitScale p t m hm F D hderivative]
      have hevalDq :
          (D.map (Int.castRingHom
            (ZMod (p ^ (t + 1) * m)))).eval
              ((y.val : Nat) : ZMod (p ^ (t + 1) * m)) =
            ((D.eval (y.val : Int) : Int) :
              ZMod (p ^ (t + 1) * m)) := by
        rw [show ((y.val : Nat) : ZMod (p ^ (t + 1) * m)) =
            (Int.castRingHom (ZMod (p ^ (t + 1) * m)))
              (y.val : Int) by simp]
        exact Polynomial.eval_map_apply _ _
      rw [hevalDq]
      have hlinear :
          ((D.eval (y.val : Int) : Int) :
              ZMod (p ^ (t + 1) * m)) *
              (((p ^ t * m : Nat) :
                  ZMod (p ^ (t + 1) * m)) *
                ((z.val : Nat) : ZMod (p ^ (t + 1) * m))) = 0 := by
        rw [show
            ((D.eval (y.val : Int) : Int) :
                ZMod (p ^ (t + 1) * m)) *
                (((p ^ t * m : Nat) :
                    ZMod (p ^ (t + 1) * m)) *
                  ((z.val : Nat) : ZMod (p ^ (t + 1) * m))) =
              (((D.eval (y.val : Int) *
                ((p ^ t * m : Nat) : Int) * (z.val : Int) : Int)) :
                  ZMod (p ^ (t + 1) * m)) by
          push_cast
          ring]
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        rcases hdvd with ⟨d, hd⟩
        refine ⟨d * (z.val : Int), ?_⟩
        rw [hd]
        push_cast
        ring
      rw [hlinear, add_zero]
    calc
      (p ^ (t + 1) : Nat) *
          ZMod.stdAddChar
            ((F.map (Int.castRingHom
              (ZMod (p ^ (t + 1) * m)))).eval
                ((y.val : Nat) : ZMod (p ^ (t + 1) * m))) =
          ∑ _z : Fin (p ^ (t + 1)),
            ZMod.stdAddChar
              ((F.map (Int.castRingHom
                (ZMod (p ^ (t + 1) * m)))).eval
                  ((y.val : Nat) : ZMod (p ^ (t + 1) * m))) := by
        simp
      _ = ∑ z : Fin (p ^ (t + 1)),
          if (D.map (Int.castRingHom (ZMod p))).eval
              (((finProdFinEquiv (z, y)).val : Nat) : ZMod p) = 0
          then ZMod.stdAddChar
            ((F.map (Int.castRingHom
              (ZMod (p ^ (t + 1) * m)))).eval
                (((finProdFinEquiv (z, y)).val : Nat) :
                  ZMod (p ^ (t + 1) * m)))
          else 0 := by
        apply Finset.sum_congr rfl
        intro z _
        rw [if_pos (hrootIndex z), hphase z]
  · rw [if_neg hy]
    have hnotrootIndex (z : Fin (p ^ (t + 1))) :
        (D.map (Int.castRingHom (ZMod p))).eval
            (((finProdFinEquiv (z, y)).val : Nat) : ZMod p) ≠ 0 := by
      rw [hindexMod z]
      exact hy
    simp only [if_neg (hnotrootIndex _), Finset.sum_const_zero]

end Waring.Analytic
