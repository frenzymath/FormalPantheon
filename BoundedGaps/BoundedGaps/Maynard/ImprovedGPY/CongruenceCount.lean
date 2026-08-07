import BoundedGaps.Maynard.ImprovedGPY.SieveSums
import BoundedGaps.Maynard.ImprovedGPY.Congruence
import BoundedGaps.Maynard.ImprovedGPY.TupleSupport
import BoundedGaps.Maynard.Distribution
import Mathlib.Data.Int.CardIntervalMod

noncomputable section

/-!
# LCM normalization for the S1 congruence system

Maynard2013v3, Section 5, in the proof of `lmm:S1Expression1` (source lines
273--277), replaces the two divisibility conditions at each shift by the
least common multiple `[d_i,e_i]`.  This file records that finite arithmetic
step before adding the pre-sieving modulus or applying CRT.
-/

namespace BoundedGaps.Maynard

open scoped Function
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The coordinate modulus obtained from an ordered divisor-tuple pair. -/
def divisorTupleLcm (H : Finset ℕ) (d e : H → ℕ) : H → ℕ :=
  fun h => Nat.lcm (d h) (e h)

def negativeShiftResidue (m h : ℕ) : ℕ :=
  m - h % m

theorem negativeShiftResidue_add_dvd
    (m h : ℕ) (hm : 0 < m) :
    m ∣ negativeShiftResidue m h + h := by
  refine ⟨h / m + 1, ?_⟩
  have hr : h % m ≤ m := (Nat.mod_lt h hm).le
  unfold negativeShiftResidue
  calc
    m - h % m + h = m - h % m + (h % m + m * (h / m)) := by
      rw [Nat.mod_add_div]
    _ = m + m * (h / m) := by omega
    _ = m * (h / m + 1) := by ring

theorem modEq_negativeShiftResidue_iff_dvd_add
    (m h n : ℕ) (hm : 0 < m) :
    n ≡ negativeShiftResidue m h [MOD m] ↔ m ∣ n + h := by
  have hres : negativeShiftResidue m h + h ≡ 0 [MOD m] :=
    Nat.modEq_zero_iff_dvd.mpr (negativeShiftResidue_add_dvd m h hm)
  constructor
  · intro hn
    exact Nat.modEq_zero_iff_dvd.mp ((hn.add_right h).trans hres)
  · intro hn
    have hsum : n + h ≡ negativeShiftResidue m h + h [MOD m] :=
      (Nat.modEq_zero_iff_dvd.mpr hn).trans hres.symm
    exact Nat.ModEq.add_right_cancel' h hsum

def divisorTupleResidue (H : Finset ℕ) (d e : H → ℕ) : H → ℕ :=
  fun h => negativeShiftResidue (divisorTupleLcm H d e h) h.1

def IsCrossCoordinateCoprime (H : Finset ℕ) (d e : H → ℕ) : Prop :=
  ∀ {a b : H}, a ≠ b →
    Nat.Coprime (d a) (e b) ∧ Nat.Coprime (e a) (d b)

theorem coprime_lcm_lcm_of_four
    {a b c d : ℕ}
    (hac : Nat.Coprime a c) (had : Nat.Coprime a d)
    (hbc : Nat.Coprime b c) (hbd : Nat.Coprime b d) :
    Nat.Coprime (Nat.lcm a b) (Nat.lcm c d) := by
  have ha : Nat.Coprime a (c * d) := hac.mul_right had
  have hb : Nat.Coprime b (c * d) := hbc.mul_right hbd
  have hp : Nat.Coprime (a * b) (c * d) := ha.mul_left hb
  exact Nat.Coprime.of_dvd (Nat.lcm_dvd_mul a b) (Nat.lcm_dvd_mul c d) hp

theorem divisorTuplePairCondition_iff_lcm_dvd
    (H : Finset ℕ) (n : ℕ) (d e : H → ℕ) :
    divisorTuplePairCondition H n d e ↔
      ∀ h : H, divisorTupleLcm H d e h ∣ n + h.1 := by
  constructor
  · rintro ⟨hd, he⟩ h
    exact Nat.lcm_dvd (hd h) (he h)
  · intro hlcm
    refine ⟨?_, ?_⟩
    · intro h
      exact (Nat.lcm_dvd_iff.mp (hlcm h)).1
    · intro h
      exact (Nat.lcm_dvd_iff.mp (hlcm h)).2

theorem divisorTupleLcm_pos_of_isMaynard
    {H : Finset ℕ} {R W : ℕ} {d e : H → ℕ}
    (hd : IsMaynardDivisorTuple H R W d)
    (he : IsMaynardDivisorTuple H R W e) (h : H) :
    0 < divisorTupleLcm H d e h := by
  apply Nat.pos_of_ne_zero
  exact Nat.lcm_ne_zero (hd.coordinate_squarefree h).ne_zero
    (he.coordinate_squarefree h).ne_zero

theorem divisorTuplePairCondition_iff_modEq_residue
    {H : Finset ℕ} {R W : ℕ} {d e : H → ℕ}
    (hd : IsMaynardDivisorTuple H R W d)
    (he : IsMaynardDivisorTuple H R W e) (n : ℕ) :
    divisorTuplePairCondition H n d e ↔
      ∀ h : H, n ≡ divisorTupleResidue H d e h
        [MOD divisorTupleLcm H d e h] := by
  rw [divisorTuplePairCondition_iff_lcm_dvd]
  constructor
  · intro hdiv h
    exact (modEq_negativeShiftResidue_iff_dvd_add
      (divisorTupleLcm H d e h) h.1 n
      (divisorTupleLcm_pos_of_isMaynard hd he h)).mpr (hdiv h)
  · intro hmod h
    exact (modEq_negativeShiftResidue_iff_dvd_add
      (divisorTupleLcm H d e h) h.1 n
      (divisorTupleLcm_pos_of_isMaynard hd he h)).mp (hmod h)

theorem divisorTuplePairCondition_iff_modEq_residue_list
    {H : Finset ℕ} {R W : ℕ} {d e : H → ℕ}
    (hd : IsMaynardDivisorTuple H R W d)
    (he : IsMaynardDivisorTuple H R W e) (n : ℕ) :
    divisorTuplePairCondition H n d e ↔
      ∀ h ∈ H.attach.toList,
        n ≡ divisorTupleResidue H d e h [MOD divisorTupleLcm H d e h] := by
  simpa using divisorTuplePairCondition_iff_modEq_residue hd he n

theorem intervalModEq_card_formula
    (a b q c : ℕ) (hq : 0 < q) :
    ((Finset.Ico a b).filter (fun n => n ≡ c [MOD q])).card =
      max (⌈(b - c) / (q : ℚ)⌉ - ⌈(a - c) / (q : ℚ)⌉) 0 := by
  exact Nat.Ico_filter_modEq_card a b hq c

def intervalModEqCardError (a b q c : ℕ) : ℝ :=
  ((Finset.Ico a b).filter (fun n => n ≡ c [MOD q])).card -
    ((b : ℝ) - a) / q

theorem intervalModEq_card_eq_length_div_add_error
    (a b q c : ℕ) :
    (((Finset.Ico a b).filter (fun n => n ≡ c [MOD q])).card : ℝ) =
      ((b : ℝ) - a) / q + intervalModEqCardError a b q c := by
  unfold intervalModEqCardError
  ring

theorem intervalModEqCardError_abs_le_one
    (a b q c : ℕ) (hab : a ≤ b) (hq : 0 < q) :
    |intervalModEqCardError a b q c| ≤ 1 := by
  let x : ℚ := ((b : ℚ) - c) / q
  let y : ℚ := ((a : ℚ) - c) / q
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  have hxy : y ≤ x := by
    dsimp [x, y]
    apply div_le_div_of_nonneg_right
    · exact sub_le_sub_right (by exact_mod_cast hab) _
    · exact hqQ.le
  have hceil : (⌈y⌉ : ℤ) ≤ ⌈x⌉ := Int.ceil_mono hxy
  have hdiff : 0 ≤ (⌈x⌉ : ℤ) - ⌈y⌉ := sub_nonneg.mpr hceil
  have hcardZ :
      (((Finset.Ico a b).filter (fun n => n ≡ c [MOD q])).card : ℤ) =
        (⌈x⌉ : ℤ) - ⌈y⌉ := by
    simpa [x, y, max_eq_left hdiff] using
      (intervalModEq_card_formula a b q c hq)
  have hcardR :
      (((Finset.Ico a b).filter (fun n => n ≡ c [MOD q])).card : ℝ) =
        (((⌈x⌉ : ℤ) - ⌈y⌉ : ℤ) : ℝ) := by
    exact_mod_cast hcardZ
  have hxl : x ≤ (⌈x⌉ : ℤ) := Int.le_ceil x
  have hxu : (⌈x⌉ : ℤ) < x + 1 := Int.ceil_lt_add_one x
  have hyl : y ≤ (⌈y⌉ : ℤ) := Int.le_ceil y
  have hyu : (⌈y⌉ : ℤ) < y + 1 := Int.ceil_lt_add_one y
  have hlowQ : -1 < ((⌈x⌉ : ℚ) - ⌈y⌉) - (x - y) := by
    linarith
  have huppQ : ((⌈x⌉ : ℚ) - ⌈y⌉) - (x - y) < 1 := by
    linarith
  have hlowR : -1 <
      (((⌈x⌉ : ℤ) - ⌈y⌉ : ℤ) : ℝ) - ((x - y : ℚ) : ℝ) := by
    exact_mod_cast hlowQ
  have huppR :
      (((⌈x⌉ : ℤ) - ⌈y⌉ : ℤ) : ℝ) - ((x - y : ℚ) : ℝ) < 1 := by
    exact_mod_cast huppQ
  unfold intervalModEqCardError
  rw [hcardR]
  have hxy_cast : ((x - y : ℚ) : ℝ) = ((b : ℝ) - a) / q := by
    dsimp [x, y]
    push_cast
    field_simp
    ring
  rw [← hxy_cast]
  rw [abs_le]
  constructor <;> linarith

theorem doublingIntervalModEq_card_decomposition
    (N q c : ℕ) (hq : 0 < q) :
    ∃ err : ℝ, |err| ≤ 1 ∧
      (((Finset.Ico N (2 * N)).filter (fun n => n ≡ c [MOD q])).card : ℝ) =
        (N : ℝ) / q + err := by
  refine ⟨intervalModEqCardError N (2 * N) q c, ?_, ?_⟩
  · exact intervalModEqCardError_abs_le_one N (2 * N) q c (by omega) hq
  · rw [intervalModEq_card_eq_length_div_add_error]
    congr 1
    push_cast
    ring

def IsPreSievedModuliCompatible (W : ℕ) (m : ι → ℕ) (l : List ι) : Prop :=
  (∀ i ∈ l, Nat.Coprime W (m i)) ∧
    l.Pairwise (Nat.Coprime on m)

def preSievedModulusList (l : List ι) : List (Option ι) :=
  none :: l.map some

def preSievedModulus (W : ℕ) (m : ι → ℕ) : Option ι → ℕ
  | none => W
  | some i => m i

def preSievedResidue (v : ℕ) (a : ι → ℕ) : Option ι → ℕ
  | none => v
  | some i => a i

theorem preSievedModulusList_prod
    (W : ℕ) (m : ι → ℕ) (l : List ι) :
    ((preSievedModulusList l).map (preSievedModulus W m)).prod =
      W * (l.map m).prod := by
  simp only [preSievedModulusList, List.map_cons, List.prod_cons,
    preSievedModulus]
  congr 1
  rw [List.map_map]
  simp [Function.comp_def, preSievedModulus]

def divisorPairModulus (H : Finset ℕ) (W : ℕ) (d e : H → ℕ) : ℕ :=
  W * ∏ h : H, divisorTupleLcm H d e h

theorem preSievedDivisorPairModulus_eq
    (H : Finset ℕ) (W : ℕ) (d e : H → ℕ) :
    ((preSievedModulusList H.attach.toList).map
      (preSievedModulus W (divisorTupleLcm H d e))).prod =
        divisorPairModulus H W d e := by
  classical
  simp [preSievedModulusList_prod, divisorPairModulus]

theorem preSievedModulusList_pairwise
    (W : ℕ) (m : ι → ℕ) (l : List ι)
    (hcompat : IsPreSievedModuliCompatible W m l) :
    (preSievedModulusList l).Pairwise
      (Nat.Coprime on preSievedModulus W m) := by
  apply List.pairwise_cons.mpr
  constructor
  · intro i hi
    rcases List.mem_map.mp hi with ⟨j, hj, rfl⟩
    exact hcompat.1 j hj
  · rw [List.pairwise_map]
    exact hcompat.2

theorem modEq_preSieved_crt_iff
    {ι : Type*} (a m : ι → ℕ) (l : List ι)
    (W v z : ℕ) (hcompat : IsPreSievedModuliCompatible W m l) :
    z ≡
        (Nat.chineseRemainderOfList (preSievedResidue v a)
          (preSievedModulus W m) (preSievedModulusList l)
          (preSievedModulusList_pairwise W m l hcompat) : ℕ)
        [MOD ((preSievedModulusList l).map (preSievedModulus W m)).prod] ↔
      z ≡ v [MOD W] ∧ ∀ i ∈ l, z ≡ a i [MOD m i] := by
  simpa [preSievedModulusList, preSievedModulus, preSievedResidue] using
    (modEq_crt_iff (preSievedResidue v a) (preSievedModulus W m)
      (preSievedModulusList l)
      (preSievedModulusList_pairwise W m l hcompat) z)

theorem isMaynardDivisorTuple_pair_lcm_compatible
    {H : Finset ℕ} {R W : ℕ} {d e : H → ℕ}
    (hd : IsMaynardDivisorTuple H R W d)
    (he : IsMaynardDivisorTuple H R W e)
    (hcross : IsCrossCoordinateCoprime H d e) :
    IsPreSievedModuliCompatible W (divisorTupleLcm H d e) H.attach.toList := by
  classical
  refine ⟨?_, ?_⟩
  · intro h hh
    have hWd : Nat.Coprime W (d h) := (hd.coordinate_coprime_W h).symm
    have hWe : Nat.Coprime W (e h) := (he.coordinate_coprime_W h).symm
    have hWprod : Nat.Coprime W (d h * e h) := hWd.mul_right hWe
    exact Nat.Coprime.of_dvd_right (Nat.lcm_dvd_mul (d h) (e h)) hWprod
  · apply List.Nodup.pairwise_of_forall_ne H.attach.nodup_toList
    intro a ha b hb hab
    have hdd : Nat.Coprime (d a) (d b) := hd.coordinates_coprime hab
    have hee : Nat.Coprime (e a) (e b) := he.coordinates_coprime hab
    obtain ⟨hde, hed⟩ := hcross hab
    exact coprime_lcm_lcm_of_four hdd hde hed hee

noncomputable def divisorPairCrtResidue
    (H : Finset ℕ) (R W v : ℕ) (d e : H → ℕ)
    (hd : IsMaynardDivisorTuple H R W d)
    (he : IsMaynardDivisorTuple H R W e)
    (hcross : IsCrossCoordinateCoprime H d e) : ℕ :=
  Nat.chineseRemainderOfList
    (preSievedResidue v (divisorTupleResidue H d e))
    (preSievedModulus W (divisorTupleLcm H d e))
    (preSievedModulusList H.attach.toList)
    (preSievedModulusList_pairwise W (divisorTupleLcm H d e)
      H.attach.toList
      (isMaynardDivisorTuple_pair_lcm_compatible hd he hcross))

theorem modEq_divisorPairCrtResidue_iff
    {H : Finset ℕ} {R W v : ℕ} {d e : H → ℕ}
    (hd : IsMaynardDivisorTuple H R W d)
    (he : IsMaynardDivisorTuple H R W e)
    (hcross : IsCrossCoordinateCoprime H d e) (n : ℕ) :
    n ≡ divisorPairCrtResidue H R W v d e hd he hcross
        [MOD divisorPairModulus H W d e] ↔
      n ≡ v [MOD W] ∧ divisorTuplePairCondition H n d e := by
  rw [← preSievedDivisorPairModulus_eq]
  unfold divisorPairCrtResidue
  rw [modEq_preSieved_crt_iff
    (divisorTupleResidue H d e) (divisorTupleLcm H d e)
    H.attach.toList W v n
    (isMaynardDivisorTuple_pair_lcm_compatible hd he hcross)]
  rw [← divisorTuplePairCondition_iff_modEq_residue_list hd he n]

theorem divisorPairModulus_pos
    {H : Finset ℕ} {R W : ℕ} {d e : H → ℕ}
    (hW : 0 < W) (hd : IsMaynardDivisorTuple H R W d)
    (he : IsMaynardDivisorTuple H R W e) :
    0 < divisorPairModulus H W d e := by
  unfold divisorPairModulus
  apply Nat.mul_pos hW
  apply Finset.prod_pos
  intro h hh
  exact divisorTupleLcm_pos_of_isMaynard hd he h

theorem divisorPairModulus_le_mul_divisorTupleProducts
    {H : Finset ℕ} {R W : ℕ} {d e : H → ℕ}
    (hd : IsMaynardDivisorTuple H R W d)
    (he : IsMaynardDivisorTuple H R W e) :
    divisorPairModulus H W d e ≤
      W * divisorTupleProduct H d * divisorTupleProduct H e := by
  unfold divisorPairModulus
  have hprod :
      (∏ h : H, divisorTupleLcm H d e h) ≤
        ∏ h : H, (d h * e h) := by
    apply Finset.prod_le_prod'
    intro h hh
    apply Nat.le_of_dvd
    · exact Nat.mul_pos
        (Nat.pos_of_ne_zero (hd.coordinate_squarefree h).ne_zero)
        (Nat.pos_of_ne_zero (he.coordinate_squarefree h).ne_zero)
    · exact Nat.lcm_dvd_mul _ _
  calc
    W * ∏ h : H, divisorTupleLcm H d e h ≤
        W * ∏ h : H, (d h * e h) := Nat.mul_le_mul_left W hprod
    _ = W * divisorTupleProduct H d * divisorTupleProduct H e := by
      rw [Finset.prod_mul_distrib]
      simp only [divisorTupleProduct]
      ring

theorem divisorPairModulus_mem_Icc_of_cutoff
    {H : Finset ℕ} {θ : ℝ} {x R W : ℕ} {d e : H → ℕ}
    (hW : 0 < W)
    (hd : IsMaynardDivisorTuple H R W d)
    (he : IsMaynardDivisorTuple H R W e)
    (hcut : W * divisorTupleProduct H d * divisorTupleProduct H e ≤
      modulusCutoff θ x) :
    divisorPairModulus H W d e ∈ Finset.Icc 1 (modulusCutoff θ x) := by
  simp only [Finset.mem_Icc]
  constructor
  · have hpos := divisorPairModulus_pos hW hd he
    omega
  · exact (divisorPairModulus_le_mul_divisorTupleProducts hd he).trans hcut

theorem divisorPairModulus_lt_W_mul_R_sq
    {H : Finset ℕ} {R W : ℕ} {d e : H → ℕ}
    (hW : 0 < W)
    (hd : IsMaynardDivisorTuple H R W d)
    (he : IsMaynardDivisorTuple H R W e) :
    divisorPairModulus H W d e < W * R * R := by
  have hdprod_pos : 0 < divisorTupleProduct H d := by
    unfold divisorTupleProduct
    apply Finset.prod_pos
    intro h hh
    exact Nat.pos_of_ne_zero (hd.coordinate_squarefree h).ne_zero
  have heprod_pos : 0 < divisorTupleProduct H e := by
    unfold divisorTupleProduct
    apply Finset.prod_pos
    intro h hh
    exact Nat.pos_of_ne_zero (he.coordinate_squarefree h).ne_zero
  have hprod :
      divisorTupleProduct H d * divisorTupleProduct H e < R * R := by
    have hleft := Nat.mul_lt_mul_of_pos_right hd.1 heprod_pos
    have hRpos : 0 < R := lt_trans hdprod_pos hd.1
    have hright := Nat.mul_lt_mul_of_pos_left he.1 hRpos
    exact hleft.trans hright
  have hbound := divisorPairModulus_le_mul_divisorTupleProducts hd he
  have hscaled :
      W * (divisorTupleProduct H d * divisorTupleProduct H e) < W * (R * R) :=
    Nat.mul_lt_mul_of_pos_left hprod hW
  calc
    divisorPairModulus H W d e ≤
        W * (divisorTupleProduct H d * divisorTupleProduct H e) := by
      simpa [Nat.mul_assoc] using hbound
    _ < W * (R * R) := hscaled
    _ = W * R * R := by ring

theorem divisorPairModulus_mem_Icc_of_W_mul_R_sq
    {H : Finset ℕ} {θ : ℝ} {x R W : ℕ} {d e : H → ℕ}
    (hW : 0 < W)
    (hd : IsMaynardDivisorTuple H R W d)
    (he : IsMaynardDivisorTuple H R W e)
    (hcut : W * R * R ≤ modulusCutoff θ x) :
    divisorPairModulus H W d e ∈ Finset.Icc 1 (modulusCutoff θ x) := by
  apply divisorPairModulus_mem_Icc_of_cutoff hW hd he
  calc
    W * divisorTupleProduct H d * divisorTupleProduct H e ≤ W * R * R := by
      have hproducts :=
        Nat.mul_le_mul (Nat.le_of_lt hd.1) (Nat.le_of_lt he.1)
      simpa [Nat.mul_assoc] using Nat.mul_le_mul_left W hproducts
    _ ≤ modulusCutoff θ x := hcut

theorem compatibleDivisorPair_card_formula
    {H : Finset ℕ} {R W v : ℕ} {d e : H → ℕ}
    (hW : 0 < W) (hd : IsMaynardDivisorTuple H R W d)
    (he : IsMaynardDivisorTuple H R W e)
    (hcross : IsCrossCoordinateCoprime H d e) (a b : ℕ) :
    (((Finset.Ico a b).filter (fun n =>
      n ≡ v [MOD W] ∧ divisorTuplePairCondition H n d e)).card : ℤ) =
      max
        (⌈(b - divisorPairCrtResidue H R W v d e hd he hcross) /
            (divisorPairModulus H W d e : ℚ)⌉ -
          ⌈(a - divisorPairCrtResidue H R W v d e hd he hcross) /
            (divisorPairModulus H W d e : ℚ)⌉)
        0 := by
  have hq : 0 < divisorPairModulus H W d e :=
    divisorPairModulus_pos hW hd he
  simpa only [← modEq_divisorPairCrtResidue_iff hd he hcross] using
    intervalModEq_card_formula a b (divisorPairModulus H W d e)
      (divisorPairCrtResidue H R W v d e hd he hcross) hq

theorem compatibleDivisorPair_card_decomposition
    {H : Finset ℕ} {R W v : ℕ} {d e : H → ℕ}
    (hW : 0 < W) (hd : IsMaynardDivisorTuple H R W d)
    (he : IsMaynardDivisorTuple H R W e)
    (hcross : IsCrossCoordinateCoprime H d e) (N : ℕ) :
    ∃ err : ℝ, |err| ≤ 1 ∧
      (((Finset.Ico N (2 * N)).filter (fun n =>
        n ≡ v [MOD W] ∧ divisorTuplePairCondition H n d e)).card : ℝ) =
        (N : ℝ) / divisorPairModulus H W d e + err := by
  obtain ⟨err, herr, hcount⟩ :=
    doublingIntervalModEq_card_decomposition N
      (divisorPairModulus H W d e)
      (divisorPairCrtResidue H R W v d e hd he hcross)
      (divisorPairModulus_pos hW hd he)
  refine ⟨err, herr, ?_⟩
  have hset :
      (Finset.Ico N (2 * N)).filter (fun n =>
        n ≡ v [MOD W] ∧ divisorTuplePairCondition H n d e) =
      (Finset.Ico N (2 * N)).filter (fun n =>
        n ≡ divisorPairCrtResidue H R W v d e hd he hcross
          [MOD divisorPairModulus H W d e]) := by
    ext n
    simp only [Finset.mem_filter]
    exact and_congr_right (fun _ =>
      (modEq_divisorPairCrtResidue_iff hd he hcross n).symm)
  rw [hset]
  exact hcount

theorem compatibleDivisorPair_indicator_sum_eq_card_mul
    {H : Finset ℕ} {R W v : ℕ} {d e : H → ℕ}
    (hd : IsMaynardDivisorTuple H R W d)
    (he : IsMaynardDivisorTuple H R W e)
    (hcross : IsCrossCoordinateCoprime H d e)
    (a b : ℕ) (x : ℝ) :
    (∑ n ∈ Finset.Ico a b,
      if n ≡ v [MOD W] ∧ divisorTuplePairCondition H n d e
      then x else 0) =
        (((Finset.Ico a b).filter (fun n =>
          n ≡ divisorPairCrtResidue H R W v d e hd he hcross
            [MOD divisorPairModulus H W d e])).card : ℝ) * x := by
  classical
  simp_rw [← modEq_divisorPairCrtResidue_iff hd he hcross]
  rw [← Finset.sum_filter]
  simp

end BoundedGaps.Maynard
