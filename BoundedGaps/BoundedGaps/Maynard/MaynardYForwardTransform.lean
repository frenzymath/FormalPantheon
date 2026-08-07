import BoundedGaps.Maynard.MaynardYMobiusInterval

noncomputable section

/-!
# Maynard's finite lambda-to-Y transform

This file defines the forward transform complementary to
`maynardCoefficientFromY` and proves the finite normalization needed before
Möbius cancellation.
-/

namespace BoundedGaps.Maynard

open scoped ArithmeticFunction.Moebius BigOperators

def IsSupportedMaynardY
    (H : Finset ℕ) (R W : ℕ) (y : (H → ℕ) → ℝ) : Prop :=
  ∀ e, y e ≠ 0 → IsMaynardDivisorTuple H R W e

def maynardYFromCoefficients
    (H : Finset ℕ) (R : ℕ) (lambda : (H → ℕ) → ℝ)
    (r : H → ℕ) : ℝ := by
  classical
  exact
    (∏ h : H, (ArithmeticFunction.moebius (r h) : ℝ) *
        Nat.totient (r h)) *
      ∑ d ∈ maynardDivisorTupleBox H R,
        if ∀ h : H, r h ∣ d h then
          lambda d / (divisorTupleProduct H d : ℝ)
        else 0

theorem divisorTupleProduct_pos_of_mem_box
    {H : Finset ℕ} {R : ℕ} {d : H → ℕ}
    (hd : d ∈ maynardDivisorTupleBox H R) :
    0 < divisorTupleProduct H d := by
  unfold divisorTupleProduct
  apply Finset.prod_pos
  intro h _
  exact (mem_maynardDivisorTupleBox_iff.mp hd h).1

theorem IsMaynardDivisorTuple.mem_maynardDivisorTupleBox
    {H : Finset ℕ} {R W : ℕ} {d : H → ℕ}
    (hd : IsMaynardDivisorTuple H R W d) :
    d ∈ maynardDivisorTupleBox H R := by
  apply mem_maynardDivisorTupleBox_iff.mpr
  intro h
  have hprodPos : 0 < divisorTupleProduct H d :=
    Nat.pos_of_ne_zero hd.2.2.ne_zero
  have hcoordPos : 0 < d h :=
    Nat.pos_of_ne_zero (hd.coordinate_squarefree h).ne_zero
  have hcoordLe : d h ≤ divisorTupleProduct H d :=
    Nat.le_of_dvd hprodPos (divisorTupleCoordinate_dvd_product d h)
  exact ⟨hcoordPos, lt_of_le_of_lt hcoordLe hd.1⟩

theorem maynardCoefficientFromY_div_product_eq_sum
    {H : Finset ℕ} {R W : ℕ} {y : (H → ℕ) → ℝ}
    (hy : IsSupportedMaynardY H R W y)
    {d : H → ℕ} (hd : d ∈ maynardDivisorTupleBox H R) :
    maynardCoefficientFromY H R W y d /
        (divisorTupleProduct H d : ℝ) =
      ∑ e ∈ maynardDivisorTupleBox H R,
        if divisorTupleProduct H e < R ∧ (∀ h : H, d h ∣ e h) then
          (∏ h : H, (ArithmeticFunction.moebius (d h) : ℝ)) *
            (y e / ∏ h : H, (Nat.totient (e h) : ℝ))
        else 0 := by
  classical
  let D : ℝ := divisorTupleProduct H d
  let muD : ℝ := ∏ h : H, (ArithmeticFunction.moebius (d h) : ℝ)
  have hDposNat : 0 < divisorTupleProduct H d :=
    divisorTupleProduct_pos_of_mem_box hd
  have hDne : D ≠ 0 := by
    change (divisorTupleProduct H d : ℝ) ≠ 0
    exact_mod_cast hDposNat.ne'
  have houter :
      (∏ h : H, (ArithmeticFunction.moebius (d h) : ℝ) * d h) =
        muD * D := by
    dsimp [muD, D]
    rw [Finset.prod_mul_distrib]
    simp [divisorTupleProduct]
  by_cases hcop : Nat.Coprime (divisorTupleProduct H d) W
  · rw [maynardCoefficientFromY, if_pos hcop, houter]
    change (muD * D * _) / D = _
    have hcancel (S : ℝ) : muD * D * S / D = muD * S := by
      field_simp
    rw [hcancel]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    by_cases hcond : divisorTupleProduct H e < R ∧
        (∀ h : H, d h ∣ e h)
    · simp only [if_pos hcond]
      rfl
    · simp only [if_neg hcond, mul_zero]
  · rw [maynardCoefficientFromY, if_neg hcop, zero_div]
    symm
    apply Finset.sum_eq_zero
    intro e he
    by_cases hcond : divisorTupleProduct H e < R ∧
        (∀ h : H, d h ∣ e h)
    · rw [if_pos hcond]
      by_cases hye : y e = 0
      · simp [hye]
      · have heSupport := hy e hye
        have hprod : divisorTupleProduct H d ∣ divisorTupleProduct H e := by
          unfold divisorTupleProduct
          exact Finset.prod_dvd_prod_of_dvd d e (fun h _ => hcond.2 h)
        exact False.elim
          (hcop (Nat.Coprime.of_dvd_left hprod heSupport.2.1))
    · rw [if_neg hcond]

theorem filter_maynardBox_between_eq_upperDivisorTupleInterval
    {H : Finset ℕ} {R W : ℕ} {r e : H → ℕ}
    (he : IsMaynardDivisorTuple H R W e) :
    (maynardDivisorTupleBox H R).filter
        (fun d => (∀ h : H, r h ∣ d h) ∧ (∀ h : H, d h ∣ e h)) =
      upperDivisorTupleInterval H r e := by
  classical
  ext d
  rw [Finset.mem_filter]
  simp only [upperDivisorTupleInterval, Fintype.mem_piFinset]
  constructor
  · rintro ⟨hdBox, hrd, hde⟩ h
    apply Finset.mem_filter.mpr
    exact ⟨Nat.mem_divisors.mpr
      ⟨hde h, (he.coordinate_squarefree h).ne_zero⟩, hrd h⟩
  · intro hdInterval
    have hrd : ∀ h : H, r h ∣ d h := fun h =>
      (Finset.mem_filter.mp (hdInterval h)).2
    have hde : ∀ h : H, d h ∣ e h := fun h =>
      Nat.dvd_of_mem_divisors (Finset.mem_filter.mp (hdInterval h)).1
    refine ⟨mem_maynardDivisorTupleBox_iff.mpr ?_, hrd, hde⟩
    intro h
    have hePos : 0 < e h := Nat.pos_of_ne_zero
      (he.coordinate_squarefree h).ne_zero
    have hdPos : 0 < d h := Nat.pos_of_dvd_of_pos (hde h) hePos
    have heProdPos : 0 < divisorTupleProduct H e :=
      Nat.pos_of_ne_zero he.2.2.ne_zero
    have heLe : e h ≤ divisorTupleProduct H e :=
      Nat.le_of_dvd heProdPos (divisorTupleCoordinate_dvd_product e h)
    have hdLe : d h ≤ e h := Nat.le_of_dvd hePos (hde h)
    exact ⟨hdPos, lt_of_le_of_lt (hdLe.trans heLe) he.1⟩

theorem sum_box_tupleMoebius_between
    {H : Finset ℕ} {R W : ℕ} {r e : H → ℕ}
    (hr : IsMaynardDivisorTuple H R W r)
    (he : IsMaynardDivisorTuple H R W e) :
    (∑ d ∈ maynardDivisorTupleBox H R,
        if (∀ h : H, r h ∣ d h) ∧ (∀ h : H, d h ∣ e h) then
          ∏ h : H, ArithmeticFunction.moebius (d h)
        else 0) =
      if r = e then ∏ h : H, ArithmeticFunction.moebius (r h) else 0 := by
  classical
  by_cases hre : ∀ h : H, r h ∣ e h
  · rw [← Finset.sum_filter]
    rw [filter_maynardBox_between_eq_upperDivisorTupleInterval he]
    exact sum_tupleMoebius_upperDivisorTupleInterval he.2.2
      (fun h => Nat.pos_of_ne_zero (hr.coordinate_squarefree h).ne_zero) hre
  · have hne : r ≠ e := by
      intro h
      subst e
      exact hre (fun h => dvd_refl (r h))
    rw [if_neg hne]
    apply Finset.sum_eq_zero
    intro d hd
    rw [if_neg]
    rintro ⟨hrd, hde⟩
    exact hre (fun h => dvd_trans (hrd h) (hde h))

theorem sum_box_tupleMoebius_between_real
    {H : Finset ℕ} {R W : ℕ} {r e : H → ℕ}
    (hr : IsMaynardDivisorTuple H R W r)
    (he : IsMaynardDivisorTuple H R W e) :
    (∑ d ∈ maynardDivisorTupleBox H R,
        if (∀ h : H, r h ∣ d h) ∧ (∀ h : H, d h ∣ e h) then
          ∏ h : H, (ArithmeticFunction.moebius (d h) : ℝ)
        else 0) =
      if r = e then
        ∏ h : H, (ArithmeticFunction.moebius (r h) : ℝ) else 0 := by
  exact_mod_cast sum_box_tupleMoebius_between hr he

theorem sum_box_tupleMoebius_weighted_between
    {H : Finset ℕ} {R W : ℕ} {r e : H → ℕ}
    (hr : IsMaynardDivisorTuple H R W r)
    (he : IsMaynardDivisorTuple H R W e) (c : ℝ) :
    (∑ d ∈ maynardDivisorTupleBox H R,
        if ∀ h : H, r h ∣ d h then
          if divisorTupleProduct H e < R ∧ (∀ h : H, d h ∣ e h) then
            (∏ h : H, (ArithmeticFunction.moebius (d h) : ℝ)) * c
          else 0
        else 0) =
      if r = e then
        (∏ h : H, (ArithmeticFunction.moebius (r h) : ℝ)) * c else 0 := by
  classical
  calc
    (∑ d ∈ maynardDivisorTupleBox H R,
        if ∀ h : H, r h ∣ d h then
          if divisorTupleProduct H e < R ∧ (∀ h : H, d h ∣ e h) then
            (∏ h : H, (ArithmeticFunction.moebius (d h) : ℝ)) * c
          else 0
        else 0) =
        ∑ d ∈ maynardDivisorTupleBox H R,
          (if (∀ h : H, r h ∣ d h) ∧ (∀ h : H, d h ∣ e h) then
            ∏ h : H, (ArithmeticFunction.moebius (d h) : ℝ)
          else 0) * c := by
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hrd : ∀ h : H, r h ∣ d h
      · by_cases hde : ∀ h : H, d h ∣ e h
        · rw [if_pos hrd, if_pos ⟨he.1, hde⟩, if_pos ⟨hrd, hde⟩]
        · rw [if_pos hrd, if_neg (fun h => hde h.2),
            if_neg (fun h => hde h.2)]
          simp
      · rw [if_neg hrd, if_neg (fun h => hrd h.1)]
        simp
    _ = (∑ d ∈ maynardDivisorTupleBox H R,
          if (∀ h : H, r h ∣ d h) ∧ (∀ h : H, d h ∣ e h) then
            ∏ h : H, (ArithmeticFunction.moebius (d h) : ℝ)
          else 0) * c := by
      rw [Finset.sum_mul]
    _ = if r = e then
          (∏ h : H, (ArithmeticFunction.moebius (r h) : ℝ)) * c else 0 := by
      rw [sum_box_tupleMoebius_between_real hr he]
      by_cases hdiag : r = e <;> simp [hdiag]

theorem maynardYFromCoefficients_maynardCoefficientFromY
    {H : Finset ℕ} {R W : ℕ} {y : (H → ℕ) → ℝ}
    (hy : IsSupportedMaynardY H R W y)
    {r : H → ℕ} (hr : IsMaynardDivisorTuple H R W r) :
    maynardYFromCoefficients H R
        (maynardCoefficientFromY H R W y) r = y r := by
  classical
  let muR : ℝ := ∏ h : H, (ArithmeticFunction.moebius (r h) : ℝ)
  let phiR : ℝ := ∏ h : H, (Nat.totient (r h) : ℝ)
  have hrBox : r ∈ maynardDivisorTupleBox H R :=
    hr.mem_maynardDivisorTupleBox
  have hnormalized :
      (∑ d ∈ maynardDivisorTupleBox H R,
          if ∀ h : H, r h ∣ d h then
            maynardCoefficientFromY H R W y d /
              (divisorTupleProduct H d : ℝ)
          else 0) =
        ∑ d ∈ maynardDivisorTupleBox H R,
          if ∀ h : H, r h ∣ d h then
            ∑ e ∈ maynardDivisorTupleBox H R,
              if divisorTupleProduct H e < R ∧
                  (∀ h : H, d h ∣ e h) then
                (∏ h : H, (ArithmeticFunction.moebius (d h) : ℝ)) *
                  (y e / ∏ h : H, (Nat.totient (e h) : ℝ))
              else 0
          else 0 := by
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hrd : ∀ h : H, r h ∣ d h
    · rw [if_pos hrd, if_pos hrd]
      exact maynardCoefficientFromY_div_product_eq_sum hy hd
    · rw [if_neg hrd, if_neg hrd]
  have hdistributed :
      (∑ d ∈ maynardDivisorTupleBox H R,
          if ∀ h : H, r h ∣ d h then
            ∑ e ∈ maynardDivisorTupleBox H R,
              if divisorTupleProduct H e < R ∧
                  (∀ h : H, d h ∣ e h) then
                (∏ h : H, (ArithmeticFunction.moebius (d h) : ℝ)) *
                  (y e / ∏ h : H, (Nat.totient (e h) : ℝ))
              else 0
          else 0) =
        ∑ d ∈ maynardDivisorTupleBox H R,
          ∑ e ∈ maynardDivisorTupleBox H R,
            if ∀ h : H, r h ∣ d h then
              if divisorTupleProduct H e < R ∧
                  (∀ h : H, d h ∣ e h) then
                (∏ h : H, (ArithmeticFunction.moebius (d h) : ℝ)) *
                  (y e / ∏ h : H, (Nat.totient (e h) : ℝ))
              else 0
            else 0 := by
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hrd : ∀ h : H, r h ∣ d h
    · rw [if_pos hrd]
      apply Finset.sum_congr rfl
      intro e he
      rw [if_pos hrd]
    · rw [if_neg hrd]
      symm
      apply Finset.sum_eq_zero
      intro e he
      rw [if_neg hrd]
  have hcollapsed :
      (∑ e ∈ maynardDivisorTupleBox H R,
          ∑ d ∈ maynardDivisorTupleBox H R,
            if ∀ h : H, r h ∣ d h then
              if divisorTupleProduct H e < R ∧
                  (∀ h : H, d h ∣ e h) then
                (∏ h : H, (ArithmeticFunction.moebius (d h) : ℝ)) *
                  (y e / ∏ h : H, (Nat.totient (e h) : ℝ))
              else 0
            else 0) =
        ∑ e ∈ maynardDivisorTupleBox H R,
          if r = e then
            (∏ h : H, (ArithmeticFunction.moebius (r h) : ℝ)) *
              (y e / ∏ h : H, (Nat.totient (e h) : ℝ))
          else 0 := by
    apply Finset.sum_congr rfl
    intro e heBox
    by_cases hye : y e = 0
    · simp [hye]
    · exact sum_box_tupleMoebius_weighted_between hr (hy e hye)
        (y e / ∏ h : H, (Nat.totient (e h) : ℝ))
  have hsingle :
      (∑ e ∈ maynardDivisorTupleBox H R,
          if r = e then
            (∏ h : H, (ArithmeticFunction.moebius (r h) : ℝ)) *
              (y e / ∏ h : H, (Nat.totient (e h) : ℝ))
          else 0) = muR * (y r / phiR) := by
    rw [Finset.sum_eq_single r]
    · simp [muR, phiR]
    · intro e he hne
      rw [if_neg (Ne.symm hne)]
    · intro hnot
      exact False.elim (hnot hrBox)
  have hprefactor :
      (∏ h : H, (ArithmeticFunction.moebius (r h) : ℝ) *
          Nat.totient (r h)) = muR * phiR := by
    dsimp [muR, phiR]
    exact Finset.prod_mul_distrib
  have hmuSq : muR * muR = 1 := by
    dsimp [muR]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro h hh
    have hsq := (squarefree_iff_moebius_sq_eq_one (r h)).mp
      (hr.coordinate_squarefree h)
    exact_mod_cast (by simpa [pow_two] using hsq)
  have hphiNe : phiR ≠ 0 := by
    apply ne_of_gt
    dsimp [phiR]
    apply Finset.prod_pos
    intro h hh
    exact_mod_cast Nat.totient_pos.mpr
      (Nat.pos_of_ne_zero (hr.coordinate_squarefree h).ne_zero)
  unfold maynardYFromCoefficients
  rw [hnormalized, hdistributed, Finset.sum_comm, hcollapsed, hsingle,
    hprefactor]
  calc
    (muR * phiR) * (muR * (y r / phiR)) =
        (muR * muR) * (phiR / phiR) * y r := by ring
    _ = y r := by rw [hmuSq, div_self hphiNe]; ring

theorem isSupportedMaynardY_maynardYValue
    (H : Finset ℕ) (R W : ℕ) (F : (H → ℝ) → ℝ) :
    IsSupportedMaynardY H R W (maynardYValue H R W F) := by
  intro e hne
  unfold maynardYValue at hne
  by_cases he : divisorTupleProduct H e < R ∧
      Nat.Coprime (divisorTupleProduct H e) W ∧
      Squarefree (divisorTupleProduct H e)
  · exact he
  · simp [he] at hne

theorem maynardYFromCoefficients_maynardCoefficient
    (H : Finset ℕ) (R W : ℕ) (F : (H → ℝ) → ℝ)
    {r : H → ℕ} (hr : IsMaynardDivisorTuple H R W r) :
    maynardYFromCoefficients H R (maynardCoefficient H R W F) r =
      maynardYValue H R W F r := by
  have hcoeff : maynardCoefficient H R W F =
      maynardCoefficientFromY H R W (maynardYValue H R W F) := by
    funext d
    exact maynardCoefficient_eq_fromYValue H R W F d
  rw [hcoeff]
  exact maynardYFromCoefficients_maynardCoefficientFromY
    (isSupportedMaynardY_maynardYValue H R W F) hr

end BoundedGaps.Maynard
