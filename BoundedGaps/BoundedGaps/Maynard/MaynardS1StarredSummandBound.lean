import BoundedGaps.Maynard.MaynardPreSievedTotientMean
import BoundedGaps.Maynard.MaynardS1StarredRoughSupport

noncomputable section

/-!
# A pointwise majorant for starred S1 cross terms

The factored lower denominators cancel one common-variable totient product.
The remaining majorant separates into a common reciprocal-totient weight and
a cross reciprocal-totient-square weight.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators

def commonTotientProduct (H : Finset ℕ) (u : H → ℕ) : ℕ :=
  ∏ h : H, Nat.totient (u h)

def preSievedCommonCoordinateSupport (W R : ℕ) : Finset ℕ :=
  (Finset.range R).filter fun n =>
    0 < n ∧ Squarefree n ∧ Nat.Coprime n W

def preSievedCommonTupleSupport (H : Finset ℕ) (W R : ℕ) :
    Finset (H → ℕ) :=
  Fintype.piFinset fun _ : H => preSievedCommonCoordinateSupport W R

def commonTupleInvTotientMean (H : Finset ℕ) (W R : ℕ) : ℝ :=
  ∑ u ∈ preSievedCommonTupleSupport H W R,
    (1 : ℝ) / (commonTotientProduct H u : ℝ)

theorem preSievedCommonTupleSupport_subset_maynardDivisorTupleBox
    (H : Finset ℕ) (W R : ℕ) :
    preSievedCommonTupleSupport H W R ⊆ maynardDivisorTupleBox H R := by
  intro u hu
  rw [preSievedCommonTupleSupport, Fintype.mem_piFinset] at hu
  rw [mem_maynardDivisorTupleBox_iff]
  intro h
  have huh := Finset.mem_filter.mp (hu h)
  exact ⟨Nat.one_le_iff_ne_zero.mpr huh.2.1.ne',
    Finset.mem_range.mp huh.1⟩

theorem preSievedCommonTupleSupport_of_leftYFactor_ne_zero
    {H : Finset ℕ} {R W : ℕ} {y : (H → ℕ) → ℝ}
    (hy : IsSupportedMaynardY H R W y)
    {u : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    (hu : u ∈ maynardDivisorTupleBox H R)
    (hl : leftCrossYFactor H y u s ≠ 0) :
    u ∈ preSievedCommonTupleSupport H W R := by
  have hlSupport := hy _ (leftCrossYFactor_ne_zero_y_ne_zero hl)
  rw [preSievedCommonTupleSupport, Fintype.mem_piFinset]
  intro h
  rw [preSievedCommonCoordinateSupport, Finset.mem_filter]
  have huBounds := mem_maynardDivisorTupleBox_iff.mp hu h
  have huDvd := u_dvd_leftCrossLowerTuple H u s h
  exact ⟨Finset.mem_range.mpr huBounds.2,
    zero_lt_one.trans_le huBounds.1,
    (hlSupport.coordinate_squarefree h).squarefree_of_dvd huDvd,
    Nat.Coprime.of_dvd_left huDvd (hlSupport.coordinate_coprime_W h)⟩

theorem preSievedCoordinateInvTotientSum_le
    (W R : ℕ) :
    (∑ n ∈ preSievedCommonCoordinateSupport W R,
        (1 : ℝ) / Nat.totient n) ≤
      squarefreeCoprimeInvTotientMean W R := by
  classical
  calc
    (∑ n ∈ preSievedCommonCoordinateSupport W R,
        (1 : ℝ) / Nat.totient n) ≤
        ∑ n ∈ (Finset.Icc 1 R).filter
          (fun n => Squarefree n ∧ Nat.Coprime n W),
          (1 : ℝ) / Nat.totient n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        have hnData := Finset.mem_filter.mp hn
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_Icc.mpr
          ⟨Nat.one_le_iff_ne_zero.mpr hnData.2.1.ne',
            Nat.le_of_lt (Finset.mem_range.mp hnData.1)⟩,
          hnData.2.2.1, hnData.2.2.2⟩
      · intro n hn hnNot
        positivity
    _ = squarefreeCoprimeInvTotientMean W R := by
      unfold squarefreeCoprimeInvTotientMean
      rw [Finset.sum_filter]

theorem inv_commonTotientProduct_eq_product
    (H : Finset ℕ) (u : H → ℕ) :
    (1 : ℝ) / (commonTotientProduct H u : ℝ) =
      ∏ h : H, (1 : ℝ) / Nat.totient (u h) := by
  unfold commonTotientProduct
  push_cast
  simp only [one_div, Finset.prod_inv_distrib]

theorem commonTupleInvTotientMean_eq_pow
    (H : Finset ℕ) (W R : ℕ) :
    commonTupleInvTotientMean H W R =
      (∑ n ∈ preSievedCommonCoordinateSupport W R,
        (1 : ℝ) / Nat.totient n) ^ Fintype.card H := by
  classical
  unfold commonTupleInvTotientMean preSievedCommonTupleSupport
  calc
    (∑ u ∈ Fintype.piFinset
        (fun _ : H => preSievedCommonCoordinateSupport W R),
        (1 : ℝ) / (commonTotientProduct H u : ℝ)) =
        ∑ u ∈ Fintype.piFinset
          (fun _ : H => preSievedCommonCoordinateSupport W R),
          ∏ h : H, (1 : ℝ) / Nat.totient (u h) := by
      apply Finset.sum_congr rfl
      intro u hu
      exact inv_commonTotientProduct_eq_product H u
    _ = ∏ _h : H, ∑ n ∈ preSievedCommonCoordinateSupport W R,
          (1 : ℝ) / Nat.totient n := by
      exact Finset.sum_prod_piFinset
        (preSievedCommonCoordinateSupport W R)
        (fun _h : H => fun n => (1 : ℝ) / Nat.totient n)
    _ = _ := by simp

theorem commonTupleInvTotientMean_le
    (H : Finset ℕ) (W R : ℕ) :
    commonTupleInvTotientMean H W R ≤
      (squarefreeCoprimeInvTotientMean W R) ^ Fintype.card H := by
  rw [commonTupleInvTotientMean_eq_pow]
  apply pow_le_pow_left₀
  · positivity
  · exact preSievedCoordinateInvTotientSum_le W R

theorem abs_real_moebius_le_one (n : ℕ) :
    |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;> simp [h]

theorem abs_moebiusTupleProduct_le_one
    {H : Finset ℕ} (r : H → ℕ) :
    |∏ h : H, (ArithmeticFunction.moebius (r h) : ℝ)| ≤ 1 := by
  rw [Finset.abs_prod]
  calc
    (∏ h : H, |(ArithmeticFunction.moebius (r h) : ℝ)|) ≤
        ∏ _h : H, (1 : ℝ) := by
      apply Finset.prod_le_prod
      · intro h hh
        exact abs_nonneg _
      · intro h hh
        exact abs_real_moebius_le_one (r h)
    _ = 1 := by simp

theorem abs_crossMoebiusTupleTerm_le_one
    {H : Finset ℕ}
    (s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ) :
    |crossMoebiusTupleTerm H s| ≤ 1 := by
  unfold crossMoebiusTupleTerm
  rw [Finset.abs_prod]
  calc
    (∏ x ∈ (offDiagonalPairs H).attach,
        |(ArithmeticFunction.moebius (s x.1 x.2) : ℝ)|) ≤
        ∏ _x ∈ (offDiagonalPairs H).attach, (1 : ℝ) := by
      apply Finset.prod_le_prod
      · intro x hx
        exact abs_nonneg _
      · intro x hx
        exact abs_real_moebius_le_one (s x.1 x.2)
    _ = 1 := by simp

theorem commonTotientProduct_pos_of_preSieved
    {H : Finset ℕ} {W R : ℕ} {u : H → ℕ}
    (hu : u ∈ preSievedCommonTupleSupport H W R) :
    0 < commonTotientProduct H u := by
  unfold commonTotientProduct
  apply Finset.prod_pos
  intro h hh
  have huh := Fintype.mem_piFinset.mp hu h
  exact Nat.totient_pos.mpr (Finset.mem_filter.mp huh).2.1

theorem squarefreeRoughUnitSupport_pos
    {D Q n : ℕ} (hn : n ∈ squarefreeRoughUnitSupport D Q) :
    0 < n := by
  rw [squarefreeRoughUnitSupport, Finset.mem_insert] at hn
  rcases hn with rfl | hn
  · exact Nat.zero_lt_one
  · exact zero_lt_one.trans_le
      (Nat.one_le_of_lt (Finset.mem_Icc.mp
        (Finset.mem_filter.mp hn).1).1)

theorem crossTotientProduct_pos_of_rough
    {H : Finset ℕ} {D R : ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    (hs : s ∈ roughCrossTupleSupport H D R) :
    0 < crossTotientProduct H s := by
  unfold crossTotientProduct
  apply Finset.prod_pos
  intro x hx
  have hsx := (Finset.mem_pi.mp hs) x.1 x.2
  exact Nat.totient_pos.mpr (squarefreeRoughUnitSupport_pos hsx)

theorem abs_leftCrossYFactor_le
    {H : Finset ℕ} {y : (H → ℕ) → ℝ} {B : ℝ}
    (hyBound : ∀ r, |y r| ≤ B)
    {u : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    (hu : u ∈ preSievedCommonTupleSupport H W R)
    (hs : s ∈ roughCrossTupleSupport H D R)
    (hstar : IsStarredCrossTuple H u s) :
    |leftCrossYFactor H y u s| ≤
      B / ((commonTotientProduct H u : ℝ) *
        (crossTotientProduct H s : ℝ)) := by
  have hdenNat := prod_totient_leftCrossLowerTuple hstar
  have hden : (∏ h : H,
      (Nat.totient (leftCrossLowerTuple H u s h) : ℝ)) =
      (commonTotientProduct H u : ℝ) *
        (crossTotientProduct H s : ℝ) := by
    simpa [commonTotientProduct] using congrArg (fun n : ℕ => (n : ℝ)) hdenNat
  have hU : (0 : ℝ) < commonTotientProduct H u := by
    exact_mod_cast commonTotientProduct_pos_of_preSieved hu
  have hS : (0 : ℝ) < crossTotientProduct H s := by
    exact_mod_cast crossTotientProduct_pos_of_rough hs
  unfold leftCrossYFactor
  rw [abs_div, abs_mul, hden, abs_of_pos (mul_pos hU hS)]
  apply div_le_div_of_nonneg_right _ (mul_pos hU hS).le
  have hmul := mul_le_mul (abs_moebiusTupleProduct_le_one
      (leftCrossLowerTuple H u s))
    (hyBound (leftCrossLowerTuple H u s)) (abs_nonneg _) zero_le_one
  simpa only [one_mul] using hmul

theorem abs_rightCrossYFactor_le
    {H : Finset ℕ} {y : (H → ℕ) → ℝ} {B : ℝ}
    (hyBound : ∀ r, |y r| ≤ B)
    {u : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    (hu : u ∈ preSievedCommonTupleSupport H W R)
    (hs : s ∈ roughCrossTupleSupport H D R)
    (hstar : IsStarredCrossTuple H u s) :
    |rightCrossYFactor H y u s| ≤
      B / ((commonTotientProduct H u : ℝ) *
        (crossTotientProduct H s : ℝ)) := by
  have hdenNat := prod_totient_rightCrossLowerTuple hstar
  have hden : (∏ h : H,
      (Nat.totient (rightCrossLowerTuple H u s h) : ℝ)) =
      (commonTotientProduct H u : ℝ) *
        (crossTotientProduct H s : ℝ) := by
    simpa [commonTotientProduct] using congrArg (fun n : ℕ => (n : ℝ)) hdenNat
  have hU : (0 : ℝ) < commonTotientProduct H u := by
    exact_mod_cast commonTotientProduct_pos_of_preSieved hu
  have hS : (0 : ℝ) < crossTotientProduct H s := by
    exact_mod_cast crossTotientProduct_pos_of_rough hs
  unfold rightCrossYFactor
  rw [abs_div, abs_mul, hden, abs_of_pos (mul_pos hU hS)]
  apply div_le_div_of_nonneg_right _ (mul_pos hU hS).le
  have hmul := mul_le_mul (abs_moebiusTupleProduct_le_one
      (rightCrossLowerTuple H u s))
    (hyBound (rightCrossLowerTuple H u s)) (abs_nonneg _) zero_le_one
  simpa only [one_mul] using hmul

theorem abs_starredCrossYSummand_le
    {H : Finset ℕ} {y : (H → ℕ) → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hyBound : ∀ r, |y r| ≤ B)
    {u : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    (hu : u ∈ preSievedCommonTupleSupport H W R)
    (hs : s ∈ roughCrossTupleSupport H D R)
    (hstar : IsStarredCrossTuple H u s) :
    |crossMoebiusTupleTerm H s *
        (commonTotientProduct H u : ℝ) *
        leftCrossYFactor H y u s * rightCrossYFactor H y u s| ≤
      B ^ 2 / ((commonTotientProduct H u : ℝ) *
        (crossTotientProduct H s : ℝ) ^ 2) := by
  let U : ℝ := commonTotientProduct H u
  let S : ℝ := crossTotientProduct H s
  have hU : 0 < U := by
    change (0 : ℝ) < commonTotientProduct H u
    exact_mod_cast commonTotientProduct_pos_of_preSieved hu
  have hS : 0 < S := by
    change (0 : ℝ) < crossTotientProduct H s
    exact_mod_cast crossTotientProduct_pos_of_rough hs
  have hleft := abs_leftCrossYFactor_le hyBound hu hs hstar
  have hright := abs_rightCrossYFactor_le hyBound hu hs hstar
  change |crossMoebiusTupleTerm H s * U *
      leftCrossYFactor H y u s * rightCrossYFactor H y u s| ≤
    B ^ 2 / (U * S ^ 2)
  rw [abs_mul, abs_mul, abs_mul, abs_of_pos hU]
  calc
    |crossMoebiusTupleTerm H s| * U *
        |leftCrossYFactor H y u s| * |rightCrossYFactor H y u s| ≤
        1 * U * (B / (U * S)) * (B / (U * S)) := by
      gcongr
      · exact abs_crossMoebiusTupleTerm_le_one s
    _ = B ^ 2 / (U * S ^ 2) := by
      field_simp [hU.ne', hS.ne']

theorem abs_starredCrossYSummand_le_separated
    {H : Finset ℕ} {y : (H → ℕ) → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hyBound : ∀ r, |y r| ≤ B)
    {u : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    (hu : u ∈ preSievedCommonTupleSupport H W R)
    (hs : s ∈ roughCrossTupleSupport H D R)
    (hstar : IsStarredCrossTuple H u s) :
    |crossMoebiusTupleTerm H s *
        (commonTotientProduct H u : ℝ) *
        leftCrossYFactor H y u s * rightCrossYFactor H y u s| ≤
      B ^ 2 * crossTotientSquareWeight H s *
        ((1 : ℝ) / commonTotientProduct H u) := by
  have hU : (commonTotientProduct H u : ℝ) ≠ 0 := by
    exact_mod_cast (commonTotientProduct_pos_of_preSieved hu).ne'
  have hS : (crossTotientProduct H s : ℝ) ≠ 0 := by
    exact_mod_cast (crossTotientProduct_pos_of_rough hs).ne'
  calc
    |crossMoebiusTupleTerm H s *
        (commonTotientProduct H u : ℝ) *
        leftCrossYFactor H y u s * rightCrossYFactor H y u s| ≤
        B ^ 2 / ((commonTotientProduct H u : ℝ) *
          (crossTotientProduct H s : ℝ) ^ 2) :=
      abs_starredCrossYSummand_le hB hyBound hu hs hstar
    _ = B ^ 2 * crossTotientSquareWeight H s *
        ((1 : ℝ) / commonTotientProduct H u) := by
      unfold crossTotientSquareWeight
      field_simp [hU, hS]

end BoundedGaps.Maynard
