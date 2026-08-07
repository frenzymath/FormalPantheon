import BoundedGaps.Maynard.MaynardS2RestrictedStarredRoughSum
import BoundedGaps.Maynard.MaynardS1StarredFactorization
import BoundedGaps.Maynard.MaynardS2CrossTupleTail
import BoundedGaps.Maynard.MaynardS2GPositivity

noncomputable section

/-!
# Pointwise reciprocal-g majorant for restricted S2 starred terms

The restricted coefficient factors are related to Maynard's exact restricted
`Y` transform. Starred lcm factorization then separates the common `g` product
from the cross reciprocal-`g` square weight.
-/

namespace BoundedGaps.Maynard

open scoped ArithmeticFunction.Moebius BigOperators
local instance restrictedS2StarredSummandBoundDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

def commonS2GProduct (H : Finset ℕ) (u : H → ℕ) : ℝ :=
  ∏ h : H, (maynardS2G (u h) : ℝ)

def crossS2GProduct
    (H : Finset ℕ)
    (s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ) : ℝ :=
  ∏ x ∈ (offDiagonalPairs H).attach,
    (maynardS2G (s x.1 x.2) : ℝ)

theorem maynardS2G_leftCrossLowerTuple
    {H : Finset ℕ} {u : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    (hstar : IsStarredCrossTuple H u s) (h : H) :
    maynardS2G (leftCrossLowerTuple H u s h) =
      maynardS2G (u h) *
        ∏ x ∈ outgoingCrossIndices H h, maynardS2G (s x.1 x.2) := by
  have hmult : maynardS2G.IsMultiplicative := by
    unfold maynardS2G
    exact ArithmeticFunction.IsMultiplicative.prodPrimeFactors _
  rw [leftCrossLowerTuple, outgoingCrossLcm_eq_product hstar]
  rw [Nat.Coprime.lcm_eq_mul (u_coprime_outgoingCrossProduct hstar h)]
  rw [hmult.map_mul_of_coprime
    (u_coprime_outgoingCrossProduct hstar h).gcd_eq_one]
  rw [outgoingCrossProduct]
  rw [hmult.map_prod (fun x : ↑(offDiagonalPairs H) => s x.1 x.2)
    (outgoingCrossIndices H h) (outgoingCross_pairwise hstar h)]

theorem maynardS2G_rightCrossLowerTuple
    {H : Finset ℕ} {u : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    (hstar : IsStarredCrossTuple H u s) (h : H) :
    maynardS2G (rightCrossLowerTuple H u s h) =
      maynardS2G (u h) *
        ∏ x ∈ incomingCrossIndices H h, maynardS2G (s x.1 x.2) := by
  have hmult : maynardS2G.IsMultiplicative := by
    unfold maynardS2G
    exact ArithmeticFunction.IsMultiplicative.prodPrimeFactors _
  rw [rightCrossLowerTuple, incomingCrossLcm_eq_product hstar]
  rw [Nat.Coprime.lcm_eq_mul (u_coprime_incomingCrossProduct hstar h)]
  rw [hmult.map_mul_of_coprime
    (u_coprime_incomingCrossProduct hstar h).gcd_eq_one]
  rw [incomingCrossProduct]
  rw [hmult.map_prod (fun x : ↑(offDiagonalPairs H) => s x.1 x.2)
    (incomingCrossIndices H h) (incomingCross_pairwise hstar h)]

theorem prod_outgoingS2G_eq_crossS2GProduct
    {H : Finset ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ} :
    (∏ h : H, ∏ x ∈ outgoingCrossIndices H h,
      (maynardS2G (s x.1 x.2) : ℝ)) = crossS2GProduct H s := by
  unfold crossS2GProduct outgoingCrossIndices
  exact Finset.prod_fiberwise (offDiagonalPairs H).attach
    (fun x => x.1.1) (fun x => (maynardS2G (s x.1 x.2) : ℝ))

theorem prod_incomingS2G_eq_crossS2GProduct
    {H : Finset ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ} :
    (∏ h : H, ∏ x ∈ incomingCrossIndices H h,
      (maynardS2G (s x.1 x.2) : ℝ)) = crossS2GProduct H s := by
  unfold crossS2GProduct incomingCrossIndices
  exact Finset.prod_fiberwise (offDiagonalPairs H).attach
    (fun x => x.1.2) (fun x => (maynardS2G (s x.1 x.2) : ℝ))

theorem prod_maynardS2G_leftCrossLowerTuple
    {H : Finset ℕ} {u : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    (hstar : IsStarredCrossTuple H u s) :
    (∏ h : H, (maynardS2G (leftCrossLowerTuple H u s h) : ℝ)) =
      commonS2GProduct H u * crossS2GProduct H s := by
  unfold commonS2GProduct
  simp_rw [maynardS2G_leftCrossLowerTuple hstar]
  push_cast
  rw [Finset.prod_mul_distrib, prod_outgoingS2G_eq_crossS2GProduct]

theorem prod_maynardS2G_rightCrossLowerTuple
    {H : Finset ℕ} {u : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    (hstar : IsStarredCrossTuple H u s) :
    (∏ h : H, (maynardS2G (rightCrossLowerTuple H u s h) : ℝ)) =
      commonS2GProduct H u * crossS2GProduct H s := by
  unfold commonS2GProduct
  simp_rw [maynardS2G_rightCrossLowerTuple hstar]
  push_cast
  rw [Finset.prod_mul_distrib, prod_incomingS2G_eq_crossS2GProduct]

theorem restrictedS2Y_leftCrossLower_eq
    {H : Finset ℕ} {R W : ℕ} {y : (H → ℕ) → ℝ} (m : H)
    {u : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ} :
    maynardS2RestrictedYFromCoefficients H
        (maynardDivisorTupleSupport H R W)
        (maynardCoefficientFromY H R W y) m
        (leftCrossLowerTuple H u s) =
      (∏ h : H, (ArithmeticFunction.moebius
        (leftCrossLowerTuple H u s h) : ℝ) *
        maynardS2G (leftCrossLowerTuple H u s h)) *
        restrictedS2LeftCoefficientFactor H R W y m u s := by
  unfold maynardS2RestrictedYFromCoefficients
    restrictedS2LeftCoefficientFactor restrictedS2LeftCrossDivides
  apply congrArg (fun S : ℝ =>
    (∏ h : H, (ArithmeticFunction.moebius
      (leftCrossLowerTuple H u s h) : ℝ) *
      maynardS2G (leftCrossLowerTuple H u s h)) * S)
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hdiv : ∀ h : H, leftCrossLowerTuple H u s h ∣ d h
  · by_cases hm : d m = 1
    · rw [if_pos ⟨hdiv, hm⟩, if_pos]
      exact ⟨leftCrossLowerTuple_dvd_iff.mp hdiv, hm⟩
    · rw [if_neg (by exact fun h => hm h.2), if_neg]
      intro h
      exact hm h.2
  · rw [if_neg (by exact fun h => hdiv h.1), if_neg]
    intro h
    exact hdiv (leftCrossLowerTuple_dvd_iff.mpr h.1)

theorem restrictedS2Y_rightCrossLower_eq
    {H : Finset ℕ} {R W : ℕ} {y : (H → ℕ) → ℝ} (m : H)
    {u : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ} :
    maynardS2RestrictedYFromCoefficients H
        (maynardDivisorTupleSupport H R W)
        (maynardCoefficientFromY H R W y) m
        (rightCrossLowerTuple H u s) =
      (∏ h : H, (ArithmeticFunction.moebius
        (rightCrossLowerTuple H u s h) : ℝ) *
        maynardS2G (rightCrossLowerTuple H u s h)) *
        restrictedS2RightCoefficientFactor H R W y m u s := by
  unfold maynardS2RestrictedYFromCoefficients
    restrictedS2RightCoefficientFactor restrictedS2RightCrossDivides
  apply congrArg (fun S : ℝ =>
    (∏ h : H, (ArithmeticFunction.moebius
      (rightCrossLowerTuple H u s h) : ℝ) *
      maynardS2G (rightCrossLowerTuple H u s h)) * S)
  apply Finset.sum_congr rfl
  intro e he
  by_cases hdiv : ∀ h : H, rightCrossLowerTuple H u s h ∣ e h
  · by_cases hm : e m = 1
    · rw [if_pos ⟨hdiv, hm⟩, if_pos]
      exact ⟨rightCrossLowerTuple_dvd_iff.mp hdiv, hm⟩
    · rw [if_neg (by exact fun h => hm h.2), if_neg]
      intro h
      exact hm h.2
  · rw [if_neg (by exact fun h => hdiv h.1), if_neg]
    intro h
    exact hdiv (rightCrossLowerTuple_dvd_iff.mpr h.1)

theorem abs_real_moebius_eq_one_of_squarefree
    {n : ℕ} (hn : Squarefree n) :
    |(ArithmeticFunction.moebius n : ℝ)| = 1 := by
  have hsq : (ArithmeticFunction.moebius n : ℝ) ^ 2 = 1 := by
    exact_mod_cast (squarefree_iff_moebius_sq_eq_one n).mp hn
  rcases (sq_eq_one_iff.mp hsq) with h | h
  · rw [h]
    norm_num
  · rw [h]
    norm_num

theorem abs_restrictedS2Prefactor_eq_gProduct
    {H : Finset ℕ} {R : ℕ} {D : ℕ} {r : H → ℕ}
    (hr : IsMaynardDivisorTuple H R (primorial D) r) :
    |∏ h : H, (ArithmeticFunction.moebius (r h) : ℝ) *
        maynardS2G (r h)| = ∏ h : H, (maynardS2G (r h) : ℝ) := by
  rw [Finset.abs_prod]
  apply Finset.prod_congr rfl
  intro h hh
  rw [abs_mul, abs_real_moebius_eq_one_of_squarefree
    (hr.coordinate_squarefree h), abs_of_nonneg, one_mul]
  exact Nat.cast_nonneg _

theorem commonS2GProduct_pos_of_restrictedStarred
    {H : Finset ℕ} {R D : ℕ} {m : H} {u : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    (hD : 2 ≤ D)
    (hstar : IsRestrictedS2StarredCrossTuple H R (primorial D) m u s) :
    0 < commonS2GProduct H u := by
  unfold commonS2GProduct
  apply Finset.prod_pos
  intro h hh
  have hdiv := u_dvd_leftCrossLowerTuple H u s h
  have hl := hstar.2.1.1
  exact_mod_cast maynardS2G_pos_of_squarefree_coprime_primorial hD
    ((hl.coordinate_squarefree h).squarefree_of_dvd hdiv)
    (Nat.Coprime.of_dvd_left hdiv (hl.coordinate_coprime_W h))

theorem crossS2GProduct_pos_of_restrictedStarred
    {H : Finset ℕ} {R D : ℕ} {m : H} {u : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    (hD : 2 ≤ D)
    (hstar : IsRestrictedS2StarredCrossTuple H R (primorial D) m u s) :
    0 < crossS2GProduct H s := by
  unfold crossS2GProduct
  apply Finset.prod_pos
  intro x hx
  have hab := x.2
  have hdiv := cross_dvd_leftCrossLowerTuple u s x.1 hab
  have hl := hstar.2.1.1
  exact_mod_cast maynardS2G_pos_of_squarefree_coprime_primorial hD
    ((hl.coordinate_squarefree x.1.1).squarefree_of_dvd hdiv)
    (Nat.Coprime.of_dvd_left hdiv (hl.coordinate_coprime_W x.1.1))

theorem abs_restrictedS2LeftCoefficientFactor_le
    {H : Finset ℕ} {R D : ℕ} {y : (H → ℕ) → ℝ} (m : H)
    {u : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    {B : ℝ}
    (hyBound : ∀ r,
      IsMaynardDivisorTuple H R (primorial D) r → r m = 1 →
      |maynardS2RestrictedYFromCoefficients H
          (maynardDivisorTupleSupport H R (primorial D))
          (maynardCoefficientFromY H R (primorial D) y) m r| ≤ B)
    (hD : 2 ≤ D)
    (hstar : IsRestrictedS2StarredCrossTuple H R (primorial D) m u s) :
    |restrictedS2LeftCoefficientFactor H R (primorial D) y m u s| ≤
      B / (commonS2GProduct H u * crossS2GProduct H s) := by
  have hU := commonS2GProduct_pos_of_restrictedStarred hD hstar
  have hS := crossS2GProduct_pos_of_restrictedStarred hD hstar
  have hden : 0 < commonS2GProduct H u * crossS2GProduct H s :=
    mul_pos hU hS
  have hY := hyBound (leftCrossLowerTuple H u s)
    hstar.2.1.1 hstar.2.1.2
  rw [restrictedS2Y_leftCrossLower_eq m,
    abs_mul, abs_restrictedS2Prefactor_eq_gProduct hstar.2.1.1,
    prod_maynardS2G_leftCrossLowerTuple hstar.1] at hY
  apply (le_div_iff₀ hden).2
  simpa [mul_assoc, mul_comm, mul_left_comm] using hY

theorem abs_restrictedS2RightCoefficientFactor_le
    {H : Finset ℕ} {R D : ℕ} {y : (H → ℕ) → ℝ} (m : H)
    {u : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    {B : ℝ}
    (hyBound : ∀ r,
      IsMaynardDivisorTuple H R (primorial D) r → r m = 1 →
      |maynardS2RestrictedYFromCoefficients H
          (maynardDivisorTupleSupport H R (primorial D))
          (maynardCoefficientFromY H R (primorial D) y) m r| ≤ B)
    (hD : 2 ≤ D)
    (hstar : IsRestrictedS2StarredCrossTuple H R (primorial D) m u s) :
    |restrictedS2RightCoefficientFactor H R (primorial D) y m u s| ≤
      B / (commonS2GProduct H u * crossS2GProduct H s) := by
  have hU := commonS2GProduct_pos_of_restrictedStarred hD hstar
  have hS := crossS2GProduct_pos_of_restrictedStarred hD hstar
  have hden : 0 < commonS2GProduct H u * crossS2GProduct H s :=
    mul_pos hU hS
  have hY := hyBound (rightCrossLowerTuple H u s)
    hstar.2.2.1 hstar.2.2.2
  rw [restrictedS2Y_rightCrossLower_eq m,
    abs_mul, abs_restrictedS2Prefactor_eq_gProduct hstar.2.2.1,
    prod_maynardS2G_rightCrossLowerTuple hstar.1] at hY
  apply (le_div_iff₀ hden).2
  simpa [mul_assoc, mul_comm, mul_left_comm] using hY

theorem crossS2GProduct_inv_sq_eq
    {H : Finset ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ} :
    (1 : ℝ) / crossS2GProduct H s ^ 2 =
      ∏ x ∈ (offDiagonalPairs H).attach,
        (1 : ℝ) / (maynardS2G (s x.1 x.2) : ℝ) ^ 2 := by
  unfold crossS2GProduct
  rw [← Finset.prod_pow]
  simp only [one_div, Finset.prod_inv_distrib]

theorem abs_restrictedS2StarredCrossSummand_le_separated
    {H : Finset ℕ} {R D : ℕ} {y : (H → ℕ) → ℝ} (m : H)
    {u : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    {B : ℝ} (hB : 0 ≤ B)
    (hyBound : ∀ r,
      IsMaynardDivisorTuple H R (primorial D) r → r m = 1 →
      |maynardS2RestrictedYFromCoefficients H
          (maynardDivisorTupleSupport H R (primorial D))
          (maynardCoefficientFromY H R (primorial D) y) m r| ≤ B)
    (hD : 2 ≤ D)
    (hs : s ∈ roughCrossTupleSupport H D R)
    (hstar : IsRestrictedS2StarredCrossTuple H R (primorial D) m u s) :
    |crossMoebiusTupleTerm H s * commonS2GProduct H u *
        restrictedS2LeftCoefficientFactor H R (primorial D) y m u s *
        restrictedS2RightCoefficientFactor H R (primorial D) y m u s| ≤
      B ^ 2 * roughS2CrossTupleReciprocalGSquareWeight H s *
        ((1 : ℝ) / commonS2GProduct H u) := by
  have hU := commonS2GProduct_pos_of_restrictedStarred hD hstar
  have hS := crossS2GProduct_pos_of_restrictedStarred hD hstar
  have hleft := abs_restrictedS2LeftCoefficientFactor_le m hyBound hD hstar
  have hright := abs_restrictedS2RightCoefficientFactor_le m hyBound hD hstar
  have hcross := abs_crossMoebiusTupleTerm_le_one s
  simp only [abs_mul]
  rw [abs_of_pos hU]
  calc
    |crossMoebiusTupleTerm H s| * commonS2GProduct H u *
          |restrictedS2LeftCoefficientFactor H R (primorial D) y m u s| *
          |restrictedS2RightCoefficientFactor H R (primorial D) y m u s| ≤
        1 * commonS2GProduct H u *
          (B / (commonS2GProduct H u * crossS2GProduct H s)) *
          (B / (commonS2GProduct H u * crossS2GProduct H s)) := by
      gcongr
    _ = B ^ 2 / (commonS2GProduct H u * crossS2GProduct H s ^ 2) := by
      field_simp [ne_of_gt hU, ne_of_gt hS]
    _ = B ^ 2 * (1 / crossS2GProduct H s ^ 2) *
          (1 / commonS2GProduct H u) := by
      field_simp [ne_of_gt hU, ne_of_gt hS]
    _ = B ^ 2 * roughS2CrossTupleReciprocalGSquareWeight H s *
          (1 / commonS2GProduct H u) := by
      rw [crossS2GProduct_inv_sq_eq,
        (roughS2CrossTupleReciprocalGSquareWeight_eq_inv_g_product hs).symm]

end BoundedGaps.Maynard
