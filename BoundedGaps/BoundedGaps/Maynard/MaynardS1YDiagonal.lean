import BoundedGaps.Maynard.MaynardS1UnrestrictedReindex

noncomputable section

/-!
# The exact unrestricted S1 Y-diagonal

The quadratic divisor transform is evaluated on coefficients arising from a
supported Maynard `y`. This is the diagonal core only; cross-coordinate
compatibility is not discarded here.
-/

namespace BoundedGaps.Maynard

open scoped ArithmeticFunction.Moebius BigOperators

def maynardYDiagonalSum
    (H : Finset ℕ) (R W : ℕ) (y : (H → ℕ) → ℝ) : ℝ :=
  ∑ u ∈ maynardDivisorTupleSupport H R W,
    y u ^ 2 / ∏ h : H, (Nat.totient (u h) : ℝ)

theorem isMaynardDivisorTuple_of_mem_box_of_dvd
    {H : Finset ℕ} {R W : ℕ} {r e : H → ℕ}
    (_hrBox : r ∈ maynardDivisorTupleBox H R)
    (he : IsMaynardDivisorTuple H R W e)
    (hre : ∀ h : H, r h ∣ e h) :
    IsMaynardDivisorTuple H R W r := by
  have hprod : divisorTupleProduct H r ∣ divisorTupleProduct H e := by
    unfold divisorTupleProduct
    exact Finset.prod_dvd_prod_of_dvd r e (fun h _ => hre h)
  have hePos : 0 < divisorTupleProduct H e :=
    Nat.pos_of_ne_zero he.2.2.ne_zero
  have hrLe : divisorTupleProduct H r ≤ divisorTupleProduct H e :=
    Nat.le_of_dvd hePos hprod
  exact ⟨lt_of_le_of_lt hrLe he.1,
    Nat.Coprime.of_dvd_left hprod he.2.1, he.2.2.squarefree_of_dvd hprod⟩

theorem maynardCoefficientFromY_eq_zero_of_not_isMaynard
    {H : Finset ℕ} {R W : ℕ} {y : (H → ℕ) → ℝ}
    (hy : IsSupportedMaynardY H R W y)
    {d : H → ℕ} (hdBox : d ∈ maynardDivisorTupleBox H R)
    (hdNot : ¬IsMaynardDivisorTuple H R W d) :
    maynardCoefficientFromY H R W y d = 0 := by
  classical
  have hquot :
      maynardCoefficientFromY H R W y d /
          (divisorTupleProduct H d : ℝ) = 0 := by
    rw [maynardCoefficientFromY_div_product_eq_sum hy hdBox]
    apply Finset.sum_eq_zero
    intro e heBox
    by_cases hcond : divisorTupleProduct H e < R ∧
        (∀ h : H, d h ∣ e h)
    · rw [if_pos hcond]
      by_cases hye : y e = 0
      · simp [hye]
      · exact False.elim (hdNot
          (isMaynardDivisorTuple_of_mem_box_of_dvd hdBox (hy e hye) hcond.2))
    · rw [if_neg hcond]
  have hprodNe : (divisorTupleProduct H d : ℝ) ≠ 0 := by
    exact_mod_cast (divisorTupleProduct_pos_of_mem_box hdBox).ne'
  rcases div_eq_zero_iff.mp hquot with hzero | hprodZero
  · exact hzero
  · exact False.elim (hprodNe hprodZero)

theorem sum_maynardSupport_eq_box_for_coefficientFromY
    {H : Finset ℕ} {R W : ℕ} {y : (H → ℕ) → ℝ}
    (hy : IsSupportedMaynardY H R W y) (u : H → ℕ) :
    (∑ d ∈ maynardDivisorTupleSupport H R W,
        if ∀ h : H, u h ∣ d h then
          maynardCoefficientFromY H R W y d /
            (divisorTupleProduct H d : ℝ)
        else 0) =
      ∑ d ∈ maynardDivisorTupleBox H R,
        if ∀ h : H, u h ∣ d h then
          maynardCoefficientFromY H R W y d /
            (divisorTupleProduct H d : ℝ)
        else 0 := by
  classical
  apply Finset.sum_subset
  · intro d hd
    exact (mem_maynardDivisorTupleSupport_iff.mp hd).1
  · intro d hdBox hdNot
    have hdNotMaynard : ¬IsMaynardDivisorTuple H R W d := by
      intro hd
      exact hdNot (mem_maynardDivisorTupleSupport_iff.mpr ⟨hdBox, hd⟩)
    rw [maynardCoefficientFromY_eq_zero_of_not_isMaynard hy hdBox hdNotMaynard]
    simp

theorem maynardYQuadraticTerm_eq_diagonalTerm
    {H : Finset ℕ} {R W : ℕ} {y : (H → ℕ) → ℝ}
    (hy : IsSupportedMaynardY H R W y)
    {u : H → ℕ} (hu : IsMaynardDivisorTuple H R W u) :
    (∏ h : H, (Nat.totient (u h) : ℝ)) *
        (∑ d ∈ maynardDivisorTupleSupport H R W,
          if ∀ h : H, u h ∣ d h then
            maynardCoefficientFromY H R W y d /
              (divisorTupleProduct H d : ℝ)
          else 0) ^ 2 =
      y u ^ 2 / ∏ h : H, (Nat.totient (u h) : ℝ) := by
  classical
  let muU : ℝ := ∏ h : H, (ArithmeticFunction.moebius (u h) : ℝ)
  let phiU : ℝ := ∏ h : H, (Nat.totient (u h) : ℝ)
  let S : ℝ := ∑ d ∈ maynardDivisorTupleSupport H R W,
    if ∀ h : H, u h ∣ d h then
      maynardCoefficientFromY H R W y d /
        (divisorTupleProduct H d : ℝ)
    else 0
  have hsupportBox := sum_maynardSupport_eq_box_for_coefficientFromY hy u
  have hforward := maynardYFromCoefficients_maynardCoefficientFromY hy hu
  unfold maynardYFromCoefficients at hforward
  rw [← hsupportBox] at hforward
  have hprefactor :
      (∏ h : H, (ArithmeticFunction.moebius (u h) : ℝ) *
          Nat.totient (u h)) = muU * phiU := by
    dsimp [muU, phiU]
    exact Finset.prod_mul_distrib
  have hforward' : muU * phiU * S = y u := by
    rw [← hprefactor]
    exact hforward
  have hmuSq : muU * muU = 1 := by
    dsimp [muU]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro h hh
    have hsq := (squarefree_iff_moebius_sq_eq_one (u h)).mp
      (hu.coordinate_squarefree h)
    exact_mod_cast (by simpa [pow_two] using hsq)
  have hphiNe : phiU ≠ 0 := by
    apply ne_of_gt
    dsimp [phiU]
    apply Finset.prod_pos
    intro h hh
    exact_mod_cast Nat.totient_pos.mpr
      (Nat.pos_of_ne_zero (hu.coordinate_squarefree h).ne_zero)
  change phiU * S ^ 2 = y u ^ 2 / phiU
  apply (eq_div_iff hphiNe).2
  calc
    phiU * S ^ 2 * phiU = (muU * phiU * S) ^ 2 := by
      rw [pow_two]
      nlinarith [hmuSq]
    _ = y u ^ 2 := by rw [hforward']

theorem maynardYQuadraticTransform_eq_diagonalSum
    {H : Finset ℕ} {R W : ℕ} {y : (H → ℕ) → ℝ}
    (hy : IsSupportedMaynardY H R W y) :
    maynardYQuadraticTransform H R
        (maynardDivisorTupleSupport H R W)
        (maynardCoefficientFromY H R W y) =
      maynardYDiagonalSum H R W y := by
  classical
  unfold maynardYQuadraticTransform maynardYDiagonalSum
  calc
    (∑ u ∈ maynardDivisorTupleBox H R,
        (∏ h : H, (Nat.totient (u h) : ℝ)) *
          (∑ d ∈ maynardDivisorTupleSupport H R W,
            if ∀ h : H, u h ∣ d h then
              maynardCoefficientFromY H R W y d /
                (divisorTupleProduct H d : ℝ)
            else 0) ^ 2) =
        ∑ u ∈ maynardDivisorTupleSupport H R W,
          (∏ h : H, (Nat.totient (u h) : ℝ)) *
            (∑ d ∈ maynardDivisorTupleSupport H R W,
              if ∀ h : H, u h ∣ d h then
                maynardCoefficientFromY H R W y d /
                  (divisorTupleProduct H d : ℝ)
              else 0) ^ 2 := by
      symm
      apply Finset.sum_subset
      · intro u hu
        exact (mem_maynardDivisorTupleSupport_iff.mp hu).1
      · intro u huBox huNot
        have hinner :
            (∑ d ∈ maynardDivisorTupleSupport H R W,
              if ∀ h : H, u h ∣ d h then
                maynardCoefficientFromY H R W y d /
                  (divisorTupleProduct H d : ℝ)
              else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro d hd
          rw [if_neg]
          intro hud
          exact huNot (mem_maynardDivisorTupleSupport_iff.mpr ⟨huBox,
            isMaynardDivisorTuple_of_mem_box_of_dvd huBox
              (isMaynardDivisorTuple_of_mem_support hd) hud⟩)
        rw [hinner, zero_pow (by decide), mul_zero]
    _ = ∑ u ∈ maynardDivisorTupleSupport H R W,
          y u ^ 2 / ∏ h : H, (Nat.totient (u h) : ℝ) := by
      apply Finset.sum_congr rfl
      intro u hu
      exact maynardYQuadraticTerm_eq_diagonalTerm hy
        (isMaynardDivisorTuple_of_mem_support hu)

theorem unrestrictedCommonDivisorTupleSum_eq_maynardYDiagonalSum
    {H : Finset ℕ} {R W : ℕ} {y : (H → ℕ) → ℝ}
    (hy : IsSupportedMaynardY H R W y) :
    unrestrictedDivisorPairCommonDivisorTupleSum H
        (maynardDivisorTupleSupport H R W)
        (maynardCoefficientFromY H R W y) =
      maynardYDiagonalSum H R W y := by
  rw [unrestrictedCommonDivisorTupleSum_eq_maynardYQuadraticTransform
    (fun d hd => isMaynardDivisorTuple_of_mem_support hd)]
  exact maynardYQuadraticTransform_eq_diagonalSum hy

theorem unrestrictedCommonDivisorTupleSum_eq_maynardYValueDiagonal
    (H : Finset ℕ) (R W : ℕ) (F : (H → ℝ) → ℝ) :
    unrestrictedDivisorPairCommonDivisorTupleSum H
        (maynardDivisorTupleSupport H R W) (maynardCoefficient H R W F) =
      maynardYDiagonalSum H R W (maynardYValue H R W F) := by
  have hcoeff : maynardCoefficient H R W F =
      maynardCoefficientFromY H R W (maynardYValue H R W F) := by
    funext d
    exact maynardCoefficient_eq_fromYValue H R W F d
  rw [hcoeff]
  exact unrestrictedCommonDivisorTupleSum_eq_maynardYDiagonalSum
    (isSupportedMaynardY_maynardYValue H R W F)

end BoundedGaps.Maynard
