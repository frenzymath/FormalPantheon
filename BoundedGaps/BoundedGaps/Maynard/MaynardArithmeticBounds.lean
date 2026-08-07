import BoundedGaps.Arithmetic.SquarefreeReciprocalCoefficient
import BoundedGaps.Maynard.MaynardWeights
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Elementary arithmetic bounds for Maynard coefficients

This module begins the source-strength finite coefficient estimate used in
Maynard2013v3, Proposition `MainProp` (source lines 201--216). The first
lemma isolates the squarefree reciprocal-totient inequality. The next lemmas
sum the divisor envelope and bound it by a square of the harmonic logarithmic
envelope. The final lemmas give a fixed-dimensional positive product-tuple
count with the corresponding harmonic logarithmic power.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators ArithmeticFunction.Moebius

theorem squarefree_moebius_sq_div_totient_le
    {n : ℕ} (hn : Squarefree n) :
    |(ArithmeticFunction.moebius n : ℝ)| ^ 2 /
        (Nat.totient n : ℝ) ≤ (n.divisors.card : ℝ) / n := by
  have hmu : (ArithmeticFunction.moebius n : ℝ) ^ 2 = 1 := by
    exact_mod_cast (squarefree_iff_moebius_sq_eq_one n).mp hn
  rw [sq_abs, hmu, one_div]
  exact inv_totient_le_card_divisors_div hn

private def positiveProductPairs (R : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 R) ×ˢ (Finset.Icc 1 R)).filter
    (fun dm => dm.1 * dm.2 ≤ R)

theorem sum_card_divisors_div_le_reciprocal_sq (R : ℕ) :
    ∑ n ∈ Finset.Icc 1 R, (n.divisors.card : ℝ) / n ≤
      (∑ d ∈ Finset.Icc 1 R, (d : ℝ)⁻¹) ^ 2 := by
  calc
    ∑ n ∈ Finset.Icc 1 R, (n.divisors.card : ℝ) / n =
        ∑ n ∈ Finset.Icc 1 R, ∑ _d ∈ n.divisors, (n : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
    _ = ∑ x ∈ (Finset.Icc 1 R).sigma (fun n => n.divisors),
        (x.1 : ℝ)⁻¹ := by
      rw [Finset.sum_sigma']
    _ = ∑ dm ∈ positiveProductPairs R,
        ((dm.1 * dm.2 : ℕ) : ℝ)⁻¹ := by
      refine Finset.sum_bij'
        (fun x _ => (x.2, x.1 / x.2))
        (fun dm _ => ⟨dm.1 * dm.2, dm.1⟩) ?_ ?_ ?_ ?_ ?_
      · intro x hx
        have hmem := Finset.mem_sigma.mp hx
        have hn := Finset.mem_Icc.mp hmem.1
        have hdvd := (Nat.mem_divisors.mp hmem.2).1
        have hnpos : 0 < x.1 := zero_lt_one.trans_le hn.1
        have hdpos : 0 < x.2 := Nat.pos_of_dvd_of_pos hdvd hnpos
        have hdn : x.2 ≤ x.1 := Nat.le_of_dvd hnpos hdvd
        have hqpos : 0 < x.1 / x.2 := Nat.div_pos hdn hdpos
        have hprod : x.2 * (x.1 / x.2) = x.1 :=
          Nat.mul_div_cancel' hdvd
        simp only [positiveProductPairs, Finset.mem_filter,
          Finset.mem_product]
        exact ⟨⟨Finset.mem_Icc.mpr ⟨hdpos, hdn.trans hn.2⟩,
          Finset.mem_Icc.mpr
            ⟨hqpos, (Nat.div_le_self _ _).trans hn.2⟩⟩,
          hprod.trans_le hn.2⟩
      · intro dm hdm
        simp only [positiveProductPairs, Finset.mem_filter,
          Finset.mem_product] at hdm
        have hdmem := Finset.mem_Icc.mp hdm.1.1
        have hmmem := Finset.mem_Icc.mp hdm.1.2
        have hdpos : 0 < dm.1 := zero_lt_one.trans_le hdmem.1
        have hmpos : 0 < dm.2 := zero_lt_one.trans_le hmmem.1
        simp only [Finset.mem_sigma]
        exact ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hdpos hmpos, hdm.2⟩,
          Nat.mem_divisors.mpr ⟨Nat.dvd_mul_right _ _,
            (Nat.mul_pos hdpos hmpos).ne'⟩⟩
      · intro x hx
        have hmem := Finset.mem_sigma.mp hx
        have hdvd := (Nat.mem_divisors.mp hmem.2).1
        apply Sigma.ext
        · exact Nat.mul_div_cancel' hdvd
        · simp
      · intro dm hdm
        simp only [positiveProductPairs, Finset.mem_filter,
          Finset.mem_product] at hdm
        have hdmem := Finset.mem_Icc.mp hdm.1.1
        have hdpos : 0 < dm.1 := zero_lt_one.trans_le hdmem.1
        apply Prod.ext
        · rfl
        · exact Nat.mul_div_cancel_left _ hdpos
      · intro x hx
        have hmem := Finset.mem_sigma.mp hx
        have hdvd := (Nat.mem_divisors.mp hmem.2).1
        rw [Nat.mul_div_cancel' hdvd]
    _ ≤ ∑ dm ∈ (Finset.Icc 1 R) ×ˢ (Finset.Icc 1 R),
        ((dm.1 * dm.2 : ℕ) : ℝ)⁻¹ := by
      rw [positiveProductPairs, Finset.sum_filter]
      apply Finset.sum_le_sum
      intro dm hdm
      split_ifs
      · exact le_rfl
      · positivity
    _ = (∑ d ∈ Finset.Icc 1 R, (d : ℝ)⁻¹) ^ 2 := by
      rw [Finset.sum_product]
      simp_rw [Nat.cast_mul, mul_inv]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
      ring

theorem sum_card_divisors_div_le_harmonic_sq (R : ℕ) :
    ∑ n ∈ Finset.Icc 1 R, (n.divisors.card : ℝ) / n ≤
      ((harmonic R : ℚ) : ℝ) ^ 2 := by
  rw [harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  exact sum_card_divisors_div_le_reciprocal_sq R

theorem sum_card_divisors_div_le_one_add_log_sq (R : ℕ) :
    ∑ n ∈ Finset.Icc 1 R, (n.divisors.card : ℝ) / n ≤
      (1 + Real.log R) ^ 2 := by
  refine (sum_card_divisors_div_le_harmonic_sq R).trans ?_
  have hnonneg : 0 ≤ ((harmonic R : ℚ) : ℝ) := by
    by_cases hR : R = 0
    · simp [hR, harmonic]
    · rw [harmonic_eq_sum_Icc]
      simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      exact Finset.sum_nonneg fun n _ => inv_nonneg.mpr (Nat.cast_nonneg n)
  have hle : ((harmonic R : ℚ) : ℝ) ≤ 1 + Real.log R :=
    harmonic_le_one_add_log R
  exact (sq_le_sq₀ hnonneg (hnonneg.trans hle)).2 hle

noncomputable def positiveProductTuples (ι : Type*) [Fintype ι] (R : ℕ) :
    Finset (ι → ℕ) := by
  classical
  exact (Fintype.piFinset (fun _ : ι => Finset.Icc 1 R)).filter
    (fun d => ∏ i, d i ≤ R)

theorem mem_positiveProductTuples_iff
    {ι : Type*} [Fintype ι] {R : ℕ} {d : ι → ℕ} :
    d ∈ positiveProductTuples ι R ↔
      (∀ i, d i ∈ Finset.Icc 1 R) ∧ ∏ i, d i ≤ R := by
  classical
  simp [positiveProductTuples]

theorem card_positiveProductTuples_le (ι : Type*) [Fintype ι] (R : ℕ) :
    ((positiveProductTuples ι R).card : ℝ) ≤
      (R : ℝ) * ((harmonic R : ℚ) : ℝ) ^ Fintype.card ι := by
  classical
  let box : Finset (ι → ℕ) :=
    Fintype.piFinset (fun _ : ι => Finset.Icc 1 R)
  let H : ℝ := ∑ d ∈ Finset.Icc 1 R, (d : ℝ)⁻¹
  have hcard : ((positiveProductTuples ι R).card : ℝ) =
      ∑ d ∈ positiveProductTuples ι R, (1 : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    simp
  have hboxpos : ∀ d ∈ box, 0 < (∏ i, (d i : ℝ)) := by
    intro d hd
    apply Finset.prod_pos
    intro i hi
    have hdi := (Fintype.mem_piFinset.mp
      (show d ∈ Fintype.piFinset (fun _ : ι => Finset.Icc 1 R) by
        simpa [box] using hd)) i
    have hdi' := Finset.mem_Icc.mp hdi
    exact_mod_cast hdi'.1
  have hbound :
      (∑ d ∈ positiveProductTuples ι R, (1 : ℝ)) ≤
        ∑ d ∈ box, (R : ℝ) / (∏ i, (d i : ℝ)) := by
    rw [show positiveProductTuples ι R =
      box.filter (fun d => ∏ i, d i ≤ R) by
        simp [positiveProductTuples, box], Finset.sum_filter]
    apply Finset.sum_le_sum
    intro d hd
    split_ifs with hp
    · have hdpos := hboxpos d hd
      rw [one_le_div hdpos]
      exact_mod_cast hp
    · positivity
  calc
    ((positiveProductTuples ι R).card : ℝ) =
        ∑ d ∈ positiveProductTuples ι R, (1 : ℝ) := hcard
    _ ≤ ∑ d ∈ box, (R : ℝ) / (∏ i, (d i : ℝ)) := hbound
    _ = (R : ℝ) * ∑ d ∈ box, ((∏ i, (d i : ℝ))⁻¹) := by
      simp_rw [div_eq_mul_inv]
      rw [Finset.mul_sum]
    _ = (R : ℝ) * H ^ Fintype.card ι := by
      congr 1
      dsimp [box, H]
      simp_rw [← Finset.prod_inv_distrib]
      rw [Finset.sum_prod_piFinset (Finset.Icc 1 R)
        (fun _ d => (d : ℝ)⁻¹)]
      simp [Finset.prod_const]
    _ = (R : ℝ) * ((harmonic R : ℚ) : ℝ) ^ Fintype.card ι := by
      congr 1
      dsimp [H]
      rw [harmonic_eq_sum_Icc]
      simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

theorem card_positiveProductTuples_le_one_add_log (ι : Type*) [Fintype ι]
    (R : ℕ) :
    ((positiveProductTuples ι R).card : ℝ) ≤
      (R : ℝ) * (1 + Real.log R) ^ Fintype.card ι := by
  refine (card_positiveProductTuples_le ι R).trans ?_
  have hnonneg : 0 ≤ ((harmonic R : ℚ) : ℝ) := by
    by_cases hR : R = 0
    · simp [hR, harmonic]
    · rw [harmonic_eq_sum_Icc]
      simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      exact Finset.sum_nonneg fun n _ => inv_nonneg.mpr (Nat.cast_nonneg n)
  have hle : ((harmonic R : ℚ) : ℝ) ≤ 1 + Real.log R :=
    harmonic_le_one_add_log R
  exact mul_le_mul_of_nonneg_left
    ((pow_le_pow_left₀ hnonneg hle _)) (by positivity)

set_option maxHeartbeats 800000 in
theorem abs_maynardCoefficient_le_log_envelope
    (H : Finset ℕ) (R W : ℕ) (F : (H → ℝ) → ℝ)
    (d : H → ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ x, |F x| ≤ B)
    (hd : d ∈ maynardDivisorTupleSupport H R W) :
    |maynardCoefficient H R W F d| ≤
      (R : ℝ) * B * (1 + Real.log R) ^ (2 * Fintype.card H) := by
  classical
  let box : Finset (H → ℕ) := maynardDivisorTupleBox H R
  have hbox : d ∈ box := (mem_maynardDivisorTupleSupport_iff.mp hd).1
  have hprod_pos : 0 < divisorTupleProduct H d := by
    unfold divisorTupleProduct
    apply Finset.prod_pos
    intro h _
    exact_mod_cast ((mem_maynardDivisorTupleBox_iff.mp hbox) h).1
  have hprod_lt : divisorTupleProduct H d < R :=
    (isMaynardDivisorTuple_of_mem_support hd).1
  have houter :
      |∏ h : H, (ArithmeticFunction.moebius (d h) : ℝ) * d h| ≤
        (divisorTupleProduct H d : ℝ) := by
    calc
      |∏ h : H, (ArithmeticFunction.moebius (d h) : ℝ) * d h| ≤
          ∏ h : H, (d h : ℝ) := by
        rw [Finset.abs_prod]
        apply Finset.prod_le_prod
        · intro h _
          exact abs_nonneg _
        · intro h _
          have hdh : (0 : ℝ) ≤ d h := by positivity
          calc
            |(ArithmeticFunction.moebius (d h) : ℝ) * d h| =
                |(ArithmeticFunction.moebius (d h) : ℝ)| * |(d h : ℝ)| :=
              abs_mul _ _
            _ = |(ArithmeticFunction.moebius (d h) : ℝ)| * (d h : ℝ) := by
              rw [abs_of_nonneg hdh]
            _ ≤ 1 * (d h : ℝ) :=
              mul_le_mul_of_nonneg_right (by
                rcases ArithmeticFunction.moebius_eq_or (d h) with h | h | h <;>
                  simp [h]) hdh
            _ = (d h : ℝ) := one_mul _
      _ = (divisorTupleProduct H d : ℝ) := by
        simp [divisorTupleProduct]
  have hcop : Nat.Coprime (divisorTupleProduct H d) W :=
    (isMaynardDivisorTuple_of_mem_support hd).2.1
  have hinner :
      |∑ r ∈ box,
          if divisorTupleProduct H r < R ∧
              (∀ h : H, d h ∣ r h) ∧
              Nat.Coprime (divisorTupleProduct H r) W then
            ((ArithmeticFunction.moebius (divisorTupleProduct H r) : ℝ) ^ 2 /
              ∏ h : H, (Nat.totient (r h) : ℝ)) *
              F (fun h : H => Real.log (r h) / Real.log R)
          else 0| ≤
      B * (1 + Real.log R) ^ (2 * Fintype.card H) := by
    let fullbox : Finset (H → ℕ) :=
      Fintype.piFinset (fun _ : H => Finset.Icc 1 R)
    let L : ℝ := 1 + Real.log R
    have hsubset : box ⊆ fullbox := by
      intro r hr
      apply Fintype.mem_piFinset.mpr
      intro h
      have hrh := (mem_maynardDivisorTupleBox_iff.mp hr) h
      exact Finset.mem_Icc.mpr ⟨hrh.1, hrh.2.le⟩
    have hweight_nonneg : ∀ r ∈ fullbox, 0 ≤
        ∏ h : H, ((r h).divisors.card : ℝ) / r h := by
      intro r hr
      apply Finset.prod_nonneg
      intro h _
      positivity
    have hterm : ∀ r ∈ box,
        |if divisorTupleProduct H r < R ∧
            (∀ h : H, d h ∣ r h) ∧
            Nat.Coprime (divisorTupleProduct H r) W then
          ((ArithmeticFunction.moebius (divisorTupleProduct H r) : ℝ) ^ 2 /
            ∏ h : H, (Nat.totient (r h) : ℝ)) *
            F (fun h : H => Real.log (r h) / Real.log R)
          else 0| ≤
          B * ∏ h : H, ((r h).divisors.card : ℝ) / r h := by
      intro r hr
      by_cases hcond : divisorTupleProduct H r < R ∧
          (∀ h : H, d h ∣ r h) ∧
          Nat.Coprime (divisorTupleProduct H r) W
      · rw [if_pos hcond, abs_mul]
        by_cases hsq : Squarefree (divisorTupleProduct H r)
        · have hmu :
              (ArithmeticFunction.moebius (divisorTupleProduct H r) : ℝ) ^ 2 = 1 := by
            exact_mod_cast (squarefree_iff_moebius_sq_eq_one _).mp hsq
          have hden_pos : 0 < ∏ h : H, (Nat.totient (r h) : ℝ) := by
            apply Finset.prod_pos
            intro h _
            apply Nat.cast_pos.mpr
            apply Nat.totient_pos.mpr
            exact Nat.zero_lt_of_lt
              ((mem_maynardDivisorTupleBox_iff.mp hr) h).1
          have hfrac :
              |(ArithmeticFunction.moebius (divisorTupleProduct H r) : ℝ) ^ 2 /
                ∏ h : H, (Nat.totient (r h) : ℝ)| ≤
                ∏ h : H, ((r h).divisors.card : ℝ) / r h := by
            rw [hmu, abs_div, abs_of_pos hden_pos]
            simp only [abs_one]
            rw [one_div]
            rw [← Finset.prod_inv_distrib]
            apply Finset.prod_le_prod
            · intro h _
              positivity
            · intro h _
              exact inv_totient_le_card_divisors_div
                (hsq.squarefree_of_dvd (divisorTupleCoordinate_dvd_product r h))
          calc
            |(ArithmeticFunction.moebius (divisorTupleProduct H r) : ℝ) ^ 2 /
                ∏ h : H, (Nat.totient (r h) : ℝ)| *
                |F (fun h : H => Real.log (r h) / Real.log R)| ≤
                (∏ h : H, ((r h).divisors.card : ℝ) / r h) * B :=
              calc
                |(ArithmeticFunction.moebius (divisorTupleProduct H r) : ℝ) ^ 2 /
                    ∏ h : H, (Nat.totient (r h) : ℝ)| *
                    |F (fun h : H => Real.log (r h) / Real.log R)| ≤
                    (∏ h : H, ((r h).divisors.card : ℝ) / r h) *
                      |F (fun h : H => Real.log (r h) / Real.log R)| :=
                  mul_le_mul_of_nonneg_right hfrac (abs_nonneg _)
                _ ≤ (∏ h : H, ((r h).divisors.card : ℝ) / r h) * B :=
                  by
                    have hw : 0 ≤
                        ∏ h : H, ((r h).divisors.card : ℝ) / r h := by
                      apply Finset.prod_nonneg
                      intro h _
                      positivity
                    exact mul_le_mul_of_nonneg_left
                      (hF (fun h : H => Real.log (r h) / Real.log R)) hw
            _ = B * ∏ h : H, ((r h).divisors.card : ℝ) / r h := by
              rw [mul_comm]
        · have hmu : ArithmeticFunction.moebius (divisorTupleProduct H r) = 0 :=
            ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
          have hw : 0 ≤ ∏ h : H, ((r h).divisors.card : ℝ) / r h := by
            apply Finset.prod_nonneg
            intro h _
            positivity
          have hfrac_zero :
              |(ArithmeticFunction.moebius (divisorTupleProduct H r) : ℝ) ^ 2 /
                ∏ h : H, (Nat.totient (r h) : ℝ)| = 0 := by
            rw [hmu]
            norm_num
          rw [hfrac_zero, zero_mul]
          exact mul_nonneg hB hw
      · rw [if_neg hcond]
        have hw : 0 ≤ ∏ h : H, ((r h).divisors.card : ℝ) / r h := by
          apply Finset.prod_nonneg
          intro h _
          positivity
        rw [abs_zero]
        exact mul_nonneg hB hw
    have hsum :
        (∑ r ∈ box, ∏ h : H, ((r h).divisors.card : ℝ) / r h) ≤
          L ^ (2 * Fintype.card H) := by
      calc
        (∑ r ∈ box, ∏ h : H, ((r h).divisors.card : ℝ) / r h) ≤
            ∑ r ∈ fullbox, ∏ h : H, ((r h).divisors.card : ℝ) / r h :=
          Finset.sum_le_sum_of_subset_of_nonneg hsubset
            (fun r hr _ => hweight_nonneg r hr)
        _ = ∏ h : H, ∑ n ∈ Finset.Icc 1 R,
            ((n.divisors.card : ℝ) / n) := by
          rw [Finset.sum_prod_piFinset (Finset.Icc 1 R)
            (fun _ n => ((n.divisors.card : ℝ) / n))]
        _ ≤ ∏ h : H, L ^ 2 := by
          apply Finset.prod_le_prod
          · intro h _
            apply Finset.sum_nonneg
            intro n _
            positivity
          · intro h _
            exact sum_card_divisors_div_le_one_add_log_sq R
        _ = L ^ (2 * Fintype.card H) := by
          rw [Finset.prod_const, Finset.card_univ]
          rw [← pow_mul]
    calc
      |∑ r ∈ box,
          if divisorTupleProduct H r < R ∧
              (∀ h : H, d h ∣ r h) ∧
              Nat.Coprime (divisorTupleProduct H r) W then
            ((ArithmeticFunction.moebius (divisorTupleProduct H r) : ℝ) ^ 2 /
              ∏ h : H, (Nat.totient (r h) : ℝ)) *
              F (fun h : H => Real.log (r h) / Real.log R)
          else 0| ≤
          ∑ r ∈ box, |if divisorTupleProduct H r < R ∧
              (∀ h : H, d h ∣ r h) ∧
              Nat.Coprime (divisorTupleProduct H r) W then
            ((ArithmeticFunction.moebius (divisorTupleProduct H r) : ℝ) ^ 2 /
              ∏ h : H, (Nat.totient (r h) : ℝ)) *
              F (fun h : H => Real.log (r h) / Real.log R)
          else 0| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r ∈ box, B * ∏ h : H, ((r h).divisors.card : ℝ) / r h :=
        Finset.sum_le_sum (fun r hr => hterm r hr)
      _ = B * ∑ r ∈ box, ∏ h : H, ((r h).divisors.card : ℝ) / r h := by
        rw [Finset.mul_sum]
      _ ≤ B * L ^ (2 * Fintype.card H) :=
        mul_le_mul_of_nonneg_left hsum hB
      _ = B * (1 + Real.log R) ^ (2 * Fintype.card H) := by
        rfl
  rw [maynardCoefficient, if_pos hcop, abs_mul]
  calc
    |∏ h : H, (ArithmeticFunction.moebius (d h) : ℝ) * d h| *
          |∑ r ∈ box,
            if divisorTupleProduct H r < R ∧
                (∀ h : H, d h ∣ r h) ∧
                Nat.Coprime (divisorTupleProduct H r) W then
              ((ArithmeticFunction.moebius (divisorTupleProduct H r) : ℝ) ^ 2 /
                ∏ h : H, (Nat.totient (r h) : ℝ)) *
                F (fun h : H => Real.log (r h) / Real.log R)
            else 0| ≤
        (divisorTupleProduct H d : ℝ) *
          (B * (1 + Real.log R) ^ (2 * Fintype.card H)) := by
      exact mul_le_mul houter hinner (abs_nonneg _) (by positivity)
    _ ≤ (R : ℝ) * B * (1 + Real.log R) ^ (2 * Fintype.card H) := by
      calc
        (divisorTupleProduct H d : ℝ) *
            (B * (1 + Real.log R) ^ (2 * Fintype.card H)) ≤
            (R : ℝ) * (B * (1 + Real.log R) ^ (2 * Fintype.card H)) := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast hprod_lt.le
          · exact mul_nonneg hB (by positivity)
        _ = (R : ℝ) * B * (1 + Real.log R) ^ (2 * Fintype.card H) := by ring

end BoundedGaps.Maynard
