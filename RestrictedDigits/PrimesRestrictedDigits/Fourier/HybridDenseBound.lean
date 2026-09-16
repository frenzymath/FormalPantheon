import PrimesRestrictedDigits.Fourier.HybridConstants
import PrimesRestrictedDigits.Fourier.HybridCircleCounting
import PrimesRestrictedDigits.Fourier.HybridResidueCounting
import PrimesRestrictedDigits.Fourier.FirstMomentL1
import Mathlib.Data.Int.Interval

/-!
# Dense-regime hybrid estimate

The dense branch retains residue multiplicities instead of identifying aligned
integers modulo the decimal grid.  The finite packing argument is performed on
`UnitAddCircle`, with a constant center for each residue window.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

private theorem dist_coe_real_le_abs_sub (x y : Real) :
    dist ((x : Real) : UnitAddCircle) ((y : Real) : UnitAddCircle) <= |x - y| := by
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub]
  simpa [Real.norm_eq_abs] using
    (QuotientAddGroup.norm_mk_le_norm
      (S := AddSubgroup.zmultiples (1 : Real)) (m := x - y))

private theorem circle_eq_of_int_modEq_div
    {N b r : Int} (hmod : Int.ModEq N b r) (hN : (0 : Int) < N) :
    (((b : Real) / (N : Real)) : UnitAddCircle) =
      (((r : Real) / (N : Real)) : UnitAddCircle) := by
  rcases Int.modEq_iff_add_fac.mp hmod with ⟨t, ht⟩
  have hquot : (r : Real) / (N : Real) =
      (b : Real) / (N : Real) + (t : Real) := by
    rw [ht]
    push_cast
    field_simp
  rw [hquot, AddCircle.coe_add]
  have htzero : ((t : Real) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    refine ⟨t, ?_⟩
    simp [zsmul_eq_mul]
  rw [htzero, add_zero]

private theorem sum_int_Ico_firstMoment_le
    (digit : Fin 10) (length : Nat) :
    (∑ r ∈ Finset.Ico (0 : Int) (10 ^ length : Int),
      normalizedPaddedDigitFourierMagnitudeAt digit length
        ((r : Real) / ((10 ^ length : Nat) : Real))) <=
      20000 * (((10 ^ length : Nat) : Real) ^ largeSieveAlpha) := by
  have hgrid := firstMomentShiftedFrequencySum_le digit length 0
  have hsum :
      (∑ r ∈ Finset.Ico (0 : Int) (10 ^ length : Int),
        normalizedPaddedDigitFourierMagnitudeAt digit length
          ((r : Real) / ((10 ^ length : Nat) : Real))) =
        ∑ n ∈ Finset.range (10 ^ length),
          normalizedPaddedDigitFourierMagnitudeAt digit length
            ((n : Real) / ((10 ^ length : Nat) : Real)) := by
    have htoNat : (10 ^ length : Int).toNat = 10 ^ length := by
      have h : ((10 ^ length : Int).toNat : Int) = (10 ^ length : Int) :=
        Int.natCast_toNat_eq_self.mpr (by positivity)
      exact_mod_cast h
    rw [Int.Ico_eq_finset_map]
    simp only [sub_zero, htoNat, Finset.sum_map]
    simp [Function.Embedding.trans_apply, Nat.castEmbedding_apply]
  rw [hsum]
  simpa only [← Fin.sum_univ_eq_sum_range, Nat.cast_pow, Nat.cast_ofNat,
    add_zero, zero_add, largeSieveAlpha] using hgrid

private theorem sum_alignedGridSum_le_of_residueFiber_sum_le
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (digit : Fin 10) (length : Nat) (E : Real) (base : ι -> Real)
    {K : Real} (hK : 0 <= K)
    (hfiber : ∀ r ∈ Finset.Ico (0 : Int) (10 ^ length : Int),
      (∑ i ∈ s,
        ((alignedGridResidueFiber length E (base i) r).card : Real)) <= K) :
    (∑ i ∈ s, alignedGridSum digit length E (base i)) <=
      K * (20000 * (((10 ^ length : Nat) : Real) ^ largeSieveAlpha)) := by
  classical
  have hrewrite (i : ι) :
      alignedGridSum digit length E (base i) =
        ∑ r ∈ Finset.Ico (0 : Int) (10 ^ length : Int),
          (alignedGridResidueFiber length E (base i) r).card *
            normalizedPaddedDigitFourierMagnitudeAt digit length
              ((r : Real) / ((10 ^ length : Nat) : Real)) := by
    exact alignedGridSum_eq_sum_residueFibers digit length E (base i)
  have hsumExchange :
      (∑ i ∈ s, alignedGridSum digit length E (base i)) =
        ∑ r ∈ Finset.Ico (0 : Int) (10 ^ length : Int),
          ∑ i ∈ s,
            (alignedGridResidueFiber length E (base i) r).card *
              normalizedPaddedDigitFourierMagnitudeAt digit length
                ((r : Real) / ((10 ^ length : Nat) : Real)) := by
    simp_rw [hrewrite]
    rw [Finset.sum_comm]
  have hinner (r : Int) (hr : r ∈ Finset.Ico (0 : Int) (10 ^ length : Int)) :
      (∑ i ∈ s,
        (alignedGridResidueFiber length E (base i) r).card *
          normalizedPaddedDigitFourierMagnitudeAt digit length
            ((r : Real) / ((10 ^ length : Nat) : Real))) <=
        K * normalizedPaddedDigitFourierMagnitudeAt digit length
          ((r : Real) / ((10 ^ length : Nat) : Real)) := by
    have hweight := normalizedPaddedDigitFourierMagnitudeAt_nonneg digit length
      ((r : Real) / ((10 ^ length : Nat) : Real))
    calc
      (∑ i ∈ s,
          (alignedGridResidueFiber length E (base i) r).card *
            normalizedPaddedDigitFourierMagnitudeAt digit length
              ((r : Real) / ((10 ^ length : Nat) : Real))) =
          (∑ i ∈ s, ((alignedGridResidueFiber length E (base i) r).card : Real)) *
            normalizedPaddedDigitFourierMagnitudeAt digit length
              ((r : Real) / ((10 ^ length : Nat) : Real)) := by
        rw [Finset.sum_mul]
      _ <= K * normalizedPaddedDigitFourierMagnitudeAt digit length
          ((r : Real) / ((10 ^ length : Nat) : Real)) := by
        exact mul_le_mul_of_nonneg_right (hfiber r hr) hweight
  calc
    (∑ i ∈ s, alignedGridSum digit length E (base i)) =
        ∑ r ∈ Finset.Ico (0 : Int) (10 ^ length : Int),
          ∑ i ∈ s,
            (alignedGridResidueFiber length E (base i) r).card *
              normalizedPaddedDigitFourierMagnitudeAt digit length
                ((r : Real) / ((10 ^ length : Nat) : Real)) := hsumExchange
    _ <= ∑ r ∈ Finset.Ico (0 : Int) (10 ^ length : Int),
        K * normalizedPaddedDigitFourierMagnitudeAt digit length
          ((r : Real) / ((10 ^ length : Nat) : Real)) := by
      exact Finset.sum_le_sum fun r hr => hinner r hr
    _ = K * (∑ r ∈ Finset.Ico (0 : Int) (10 ^ length : Int),
        normalizedPaddedDigitFourierMagnitudeAt digit length
          ((r : Real) / ((10 ^ length : Nat) : Real))) := by
      rw [Finset.mul_sum]
    _ <= K * (20000 * (((10 ^ length : Nat) : Real) ^ largeSieveAlpha)) := by
      apply mul_le_mul_of_nonneg_left (sum_int_Ico_firstMoment_le digit length) hK

private theorem circleDist_residue_le_of_mem
    {length : Nat} {E x : Real} (hE : 0 <= E)
    (hx : x ∈ Set.Icc (0 : Real) 1) {r b : Int}
    (hb : b ∈ alignedGridResidueFiber length E x r) :
    dist ((x : Real) : UnitAddCircle)
        (((r : Real) / ((10 ^ length : Nat) : Real) : Real) : UnitAddCircle) <=
      E / ((10 ^ length : Nat) : Real) := by
  have hwindow := (mem_alignedGridResidueFiber_iff.mp hb).1
  have hwindow' := (mem_alignedGridWindow_iff_of_mem_Icc hE hx (b := b)).mp hwindow
  have hmod := (mem_alignedGridResidueFiber_iff.mp hb).2
  have hcircle :
      (((b : Real) / ((10 ^ length : Nat) : Real) : Real) : UnitAddCircle) =
        (((r : Real) / ((10 ^ length : Nat) : Real) : Real) : UnitAddCircle) := by
    exact circle_eq_of_int_modEq_div hmod
      (by positivity : (0 : Int) < 10 ^ length)
  calc
    dist ((x : Real) : UnitAddCircle)
        (((r : Real) / ((10 ^ length : Nat) : Real) : Real) : UnitAddCircle) =
      dist ((x : Real) : UnitAddCircle)
        (((b : Real) / ((10 ^ length : Nat) : Real) : Real) : UnitAddCircle) := by
          rw [hcircle]
    _ <= |x - (b : Real) / ((10 ^ length : Nat) : Real)| :=
      dist_coe_real_le_abs_sub _ _
    _ = |(b : Real) / ((10 ^ length : Nat) : Real) - x| := by
      rw [abs_sub_comm]
    _ <= E / ((10 ^ length : Nat) : Real) := hwindow'

private theorem alignedGridResidueFiber_card_le_five
    (length : Nat) (E x : Real) (r : Int) (hE : 1 <= E)
    (hsmall : E <= ((10 ^ length : Nat) : Real) / 2) :
    ((alignedGridResidueFiber length E x r).card : Real) <= 5 := by
  have hY0 : 0 < ((10 ^ length : Nat) : Real) := by positivity
  have hY1 : (1 : Real) <= ((10 ^ length : Nat) : Real) := by
    have hNat : 1 ≤ 10 ^ length := Nat.one_le_pow length 10 (by norm_num)
    exact_mod_cast hNat
  have hceil0 : 0 <= E := by linarith
  have hceil := Nat.ceil_lt_add_one hceil0
  have hceil_le : (Nat.ceil E : Real) <= 2 * E := by linarith
  have hnum : 2 * (Nat.ceil E : Real) + 1 <=
      3 * ((10 ^ length : Nat) : Real) := by nlinarith
  have hquot :
      (2 * (Nat.ceil E : Real) + 1) /
          ((10 ^ length : Nat) : Real) <= 3 := by
    apply (div_le_iff₀ hY0).mpr
    nlinarith
  have hbound :
      2 + (2 * (Nat.ceil E : Real) + 1) /
          ((10 ^ length : Nat) : Real) <= 5 := by linarith
  exact le_of_lt ((alignedGridResidueFiber_card_lt length E x r).trans_le hbound)

private theorem alignedGridResidueFiber_card_le_ten_density
    (length : Nat) (E x : Real) (r : Int) (hE : 1 <= E)
    (hlarge : ((10 ^ length : Nat) : Real) / 2 < E) :
    ((alignedGridResidueFiber length E x r).card : Real) <=
      10 * E / ((10 ^ length : Nat) : Real) := by
  have hY0 : 0 < ((10 ^ length : Nat) : Real) := by positivity
  have hceil0 : 0 <= E := by linarith
  have hceil := Nat.ceil_lt_add_one hceil0
  have hrewrite :
      2 + (2 * (Nat.ceil E : Real) + 1) /
          ((10 ^ length : Nat) : Real) =
        (2 * ((10 ^ length : Nat) : Real) +
          (2 * (Nat.ceil E : Real) + 1)) /
            ((10 ^ length : Nat) : Real) := by field_simp
  have hbound :
      2 + (2 * (Nat.ceil E : Real) + 1) /
          ((10 ^ length : Nat) : Real) <
        10 * E / ((10 ^ length : Nat) : Real) := by
    rw [hrewrite]
    apply (div_lt_div_iff₀ hY0 hY0).mpr
    nlinarith
  exact le_of_lt ((alignedGridResidueFiber_card_lt length E x r).trans hbound)

private theorem sum_residueFiber_card_le
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (length : Nat) (E : Real) (base : ι -> Real)
    {L : Real} (hL : 1 <= L) (hE : 1 <= E)
    (hbase : ∀ i ∈ s, base i ∈ Set.Icc (0 : Real) 1)
    (hseparated : ∀ i ∈ s, ∀ j ∈ s, i ≠ j ->
      1 / L <= dist ((base i : Real) : UnitAddCircle)
        ((base j : Real) : UnitAddCircle))
    (hdense : ((10 ^ length : Nat) : Real) <= 10 * L * E)
    (r : Int) :
    (∑ i ∈ s,
      ((alignedGridResidueFiber length E (base i) r).card : Real)) <=
      220 * L * E / ((10 ^ length : Nat) : Real) := by
  classical
  let Y : Real := ((10 ^ length : Nat) : Real)
  let density : Real := L * E / Y
  let circleBase : ι -> UnitAddCircle := fun i => (base i : UnitAddCircle)
  let z : UnitAddCircle := ((r : Real) / Y : Real)
  let near : Finset ι := indicesInClosedBall s circleBase z (E / Y)
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hE0 : 0 <= E := by linarith
  have hdensity : 1 / 10 <= density := by
    dsimp [density, Y]
    apply (le_div_iff₀ (show 0 < ((10 ^ length : Nat) : Real) by positivity)).mpr
    nlinarith [hdense]
  have hdelta : 0 <= E / Y := by positivity
  have hnearSubset : near ⊆ s := by
    intro i hi
    exact (mem_indicesInClosedBall_iff.mp hi).1
  have hnear_of_card_nezero (i : ι) (hi : i ∈ s)
      (hcard : (alignedGridResidueFiber length E (base i) r).card ≠ 0) :
      i ∈ near := by
    obtain ⟨b, hb⟩ := Finset.card_ne_zero.mp hcard
    apply mem_indicesInClosedBall_iff.mpr
    refine ⟨hi, ?_⟩
    rw [Metric.mem_closedBall]
    dsimp [near, circleBase, z, Y]
    exact circleDist_residue_le_of_mem hE0 (hbase i hi) hb
  have hzero (i : ι) (hi : i ∈ s) (hin : i ∉ near) :
      ((alignedGridResidueFiber length E (base i) r).card : Real) = 0 := by
    have hcard : (alignedGridResidueFiber length E (base i) r).card = 0 := by
      by_contra hne
      exact hin (hnear_of_card_nezero i hi hne)
    simp [hcard]
  by_cases hsmall : E <= Y / 2
  · have hpack := card_filter_closedBall_le_of_pairwise_circleDist
      s circleBase hL hdelta
      (fun i hi j hj hij => by
        simpa [circleBase] using hseparated i hi j hj hij) z
    have hcardSum :
        (∑ i ∈ s,
          ((alignedGridResidueFiber length E (base i) r).card : Real)) =
        ∑ i ∈ near,
          ((alignedGridResidueFiber length E (base i) r).card : Real) := by
      symm
      exact Finset.sum_subset hnearSubset (fun i hi hin => hzero i hi hin)
    calc
      (∑ i ∈ s,
        ((alignedGridResidueFiber length E (base i) r).card : Real)) =
          ∑ i ∈ near,
            ((alignedGridResidueFiber length E (base i) r).card : Real) := hcardSum
      _ <= ∑ _i ∈ near, (5 : Real) := by
        apply Finset.sum_le_sum
        intro i hi
        exact alignedGridResidueFiber_card_le_five length E (base i) r hE hsmall
      _ = (near.card : Real) * 5 := by simp
      _ <= (4 * (1 + (E / Y) * L)) * 5 :=
        mul_le_mul_of_nonneg_right hpack (by norm_num)
      _ = 20 * (1 + density) := by dsimp [density]; ring
      _ <= 220 * density := by nlinarith
      _ = 220 * L * E / ((10 ^ length : Nat) : Real) := by
        dsimp [density, Y]
        ring
  · have hlarge : Y / 2 < E := lt_of_not_ge hsmall
    have hcardTotal := card_le_two_mul_of_pairwise_circleDist s circleBase hL
      (fun i hi j hj hij => by
        simpa [circleBase] using hseparated i hi j hj hij)
    calc
      (∑ i ∈ s,
        ((alignedGridResidueFiber length E (base i) r).card : Real)) <=
          ∑ i ∈ s, 10 * E / Y := by
        apply Finset.sum_le_sum
        intro i hi
        simpa [Y] using alignedGridResidueFiber_card_le_ten_density
          length E (base i) r hE (by simpa [Y] using hlarge)
      _ = (s.card : Real) * (10 * E / Y) := by simp
      _ <= (2 * L) * (10 * E / Y) :=
        mul_le_mul_of_nonneg_right hcardTotal (by positivity)
      _ = 20 * density := by dsimp [density]; ring
      _ <= 220 * density := by
        have hdensity0 : 0 <= density := by linarith
        nlinarith
      _ = 220 * L * E / ((10 ^ length : Nat) : Real) := by
        dsimp [density, Y]
        ring

theorem sum_alignedGridSum_dense_le
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (digit : Fin 10) (length : Nat) (base : ι -> Real)
    {L E : Real} (hL : 1 <= L) (hE : 1 <= E)
    (hbase : ∀ i ∈ s, base i ∈ Set.Icc (0 : Real) 1)
    (hseparated : ∀ i ∈ s, ∀ j ∈ s, i ≠ j ->
      1 / L <= dist ((base i : Real) : UnitAddCircle)
        ((base j : Real) : UnitAddCircle))
    (hdense : ((10 ^ length : Nat) : Real) <= 10 * L * E) :
    (∑ i ∈ s, alignedGridSum digit length E (base i)) <=
      4400000 * L * E *
        (((10 ^ length : Nat) : Real) ^ (-largeSieveSigma)) := by
  classical
  let Y : Real := ((10 ^ length : Nat) : Real)
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hK : 0 <= 220 * L * E / Y := by positivity
  have htotal := sum_alignedGridSum_le_of_residueFiber_sum_le s digit length E base
    hK (fun r _ => by
      simpa [Y] using sum_residueFiber_card_le s length E base hL hE hbase
        hseparated hdense r)
  calc
    (∑ i ∈ s, alignedGridSum digit length E (base i)) <=
        (220 * L * E / Y) *
          (20000 * Y ^ largeSieveAlpha) := htotal
    _ = 4400000 * L * E * Y ^ (-largeSieveSigma) := by
      have hpower : Y ^ largeSieveAlpha / Y = Y ^ (-largeSieveSigma) := by
        calc
          Y ^ largeSieveAlpha / Y = Y ^ largeSieveAlpha / Y ^ (1 : Real) := by
            rw [Real.rpow_one]
          _ = Y ^ (largeSieveAlpha - 1) :=
            (Real.rpow_sub hY largeSieveAlpha 1).symm
          _ = Y ^ (-largeSieveSigma) := by
            congr 1
            linarith [largeSieveAlpha_add_sigma]
      calc
        (220 * L * E / Y) * (20000 * Y ^ largeSieveAlpha) =
            4400000 * L * E * (Y ^ largeSieveAlpha / Y) := by ring
        _ = 4400000 * L * E * Y ^ (-largeSieveSigma) := by rw [hpower]
    _ = 4400000 * L * E *
        (((10 ^ length : Nat) : Real) ^ (-largeSieveSigma)) := by rfl

end

end PrimesRestrictedDigits
