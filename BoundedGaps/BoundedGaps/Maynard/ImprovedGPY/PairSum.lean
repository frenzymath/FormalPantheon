import BoundedGaps.Maynard.ImprovedGPY.SieveSums
import BoundedGaps.Maynard.ImprovedGPY.CongruenceCount
import Mathlib.Data.Nat.Dist

noncomputable section

/-!
# The compatible finite S1 pair sum

Maynard2013v3, Section 5, in the proof of `lmm:S1Expression1` (source lines
277--297), restricts the expanded pair sum to compatible divisor tuples.  The
restriction is justified by the small-prime modulus `W`; this file records the
finite version with that separation hypothesis explicit.
-/

namespace BoundedGaps.Maynard

open scoped BigOperators
local instance (p : Prop) : Decidable p := Classical.propDecidable p

def CoversShiftDifferencePrimes (H : Finset ℕ) (W : ℕ) : Prop :=
  ∀ {a b : H}, a ≠ b → ∀ p, p.Prime →
    p ∣ Nat.dist a.1 b.1 → p ∣ W

def ShiftDiameterBound (H : Finset ℕ) (D₀ : ℕ) : Prop :=
  ∀ {a b : H}, a ≠ b → Nat.dist a.1 b.1 ≤ D₀

theorem coversShiftDifferencePrimes_of_diameter
    {H : Finset ℕ} {D₀ : ℕ} (hdiam : ShiftDiameterBound H D₀) :
    CoversShiftDifferencePrimes H (primorial D₀) := by
  intro a b hab p hp hpd
  apply hp.dvd_primorial_iff.mpr
  have habval : a.1 ≠ b.1 := by
    intro heq
    apply hab
    exact Subtype.ext heq
  exact le_trans (Nat.le_of_dvd (Nat.dist_pos_of_ne habval) hpd) (hdiam hab)

theorem engelsmaTuple_shiftDiameterBound :
    ShiftDiameterBound BoundedGaps.engelsmaTuple 600 := by
  intro a b hab
  have ha := BoundedGaps.engelsmaTuple_le_six_hundred a.property
  have hb := BoundedGaps.engelsmaTuple_le_six_hundred b.property
  unfold Nat.dist
  omega

theorem engelsmaTuple_coversShiftDifferencePrimes :
    CoversShiftDifferencePrimes BoundedGaps.engelsmaTuple (primorial 600) :=
  coversShiftDifferencePrimes_of_diameter engelsmaTuple_shiftDiameterBound

def compatibleDivisorPairInnerSum
    (H : Finset ℕ)
    (v W N : ℕ) (lambda : (H → ℕ) → ℝ)
    (d e : H → ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico N (2 * N),
    if n ≡ v [MOD W] ∧ divisorTuplePairCondition H n d e
    then lambda d * lambda e else 0

def compatibleDivisorPairSieveSum
    (H : Finset ℕ) (D : Finset (H → ℕ))
    (v W N : ℕ) (lambda : (H → ℕ) → ℝ) : ℝ :=
  ∑ d ∈ D, ∑ e ∈ D.filter (fun e => IsCrossCoordinateCoprime H d e),
    compatibleDivisorPairInnerSum H v W N lambda d e

def compatibleDivisorPairCardSum
    (H : Finset ℕ) (D : Finset (H → ℕ))
    (v W N : ℕ) (lambda : (H → ℕ) → ℝ) : ℝ :=
  ∑ d ∈ D, ∑ e ∈ D.filter (fun e => IsCrossCoordinateCoprime H d e),
    (((Finset.Ico N (2 * N)).filter (fun n =>
      n ≡ v [MOD W] ∧ divisorTuplePairCondition H n d e)).card : ℝ) *
        (lambda d * lambda e)

def compatibleDivisorPairCountError
    (H : Finset ℕ) (v W N : ℕ) (d e : H → ℕ) : ℝ :=
  (((Finset.Ico N (2 * N)).filter (fun n =>
    n ≡ v [MOD W] ∧ divisorTuplePairCondition H n d e)).card : ℝ) -
      (N : ℝ) / divisorPairModulus H W d e

def compatibleDivisorPairMainSum
    (H : Finset ℕ) (D : Finset (H → ℕ))
    (W N : ℕ) (lambda : (H → ℕ) → ℝ) : ℝ :=
  ∑ d ∈ D, ∑ e ∈ D.filter (fun e => IsCrossCoordinateCoprime H d e),
    (N : ℝ) / divisorPairModulus H W d e * (lambda d * lambda e)

def compatibleDivisorPairErrorSum
    (H : Finset ℕ) (D : Finset (H → ℕ))
    (v W N : ℕ) (lambda : (H → ℕ) → ℝ) : ℝ :=
  ∑ d ∈ D, ∑ e ∈ D.filter (fun e => IsCrossCoordinateCoprime H d e),
    compatibleDivisorPairCountError H v W N d e * (lambda d * lambda e)

def compatibleDivisorPairCoefficientMass
    (H : Finset ℕ) (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) : ℝ :=
  ∑ d ∈ D, ∑ e ∈ D.filter (fun e => IsCrossCoordinateCoprime H d e),
    |lambda d * lambda e|

theorem compatibleDivisorPairCoefficientMass_le_card_sq_mul
    {H : Finset ℕ} {D : Finset (H → ℕ)}
    {lambda : (H → ℕ) → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hbound : ∀ d ∈ D, |lambda d| ≤ L) :
    compatibleDivisorPairCoefficientMass H D lambda ≤
      (D.card : ℝ)^2 * L^2 := by
  classical
  unfold compatibleDivisorPairCoefficientMass
  have hterm : ∀ d ∈ D, ∀ e ∈ D.filter
      (fun e => IsCrossCoordinateCoprime H d e),
      |lambda d * lambda e| ≤ L ^ 2 := by
    intro d hd e he
    obtain ⟨heD, _⟩ := Finset.mem_filter.mp he
    rw [abs_mul]
    calc
      |lambda d| * |lambda e| ≤ L * L :=
        mul_le_mul (hbound d hd) (hbound e heD) (abs_nonneg _) hL
      _ = L ^ 2 := by ring
  calc
    ∑ d ∈ D, ∑ e ∈ D.filter
        (fun e => IsCrossCoordinateCoprime H d e), |lambda d * lambda e|
        ≤ ∑ d ∈ D, ∑ e ∈ D.filter
            (fun e => IsCrossCoordinateCoprime H d e), L ^ 2 := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro e he
      exact hterm d hd e he
    _ = ∑ d ∈ D, ((D.filter
          (fun e => IsCrossCoordinateCoprime H d e)).card : ℝ) * L ^ 2 := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_const]
      simp [nsmul_eq_mul]
    _ ≤ ∑ d ∈ D, (D.card : ℝ) * L ^ 2 := by
      apply Finset.sum_le_sum
      intro d hd
      apply mul_le_mul_of_nonneg_right
      · have hcard := Finset.card_filter_le D
          (fun e => IsCrossCoordinateCoprime H d e)
        exact_mod_cast hcard
      · exact sq_nonneg L
    _ = (D.card : ℝ)^2 * L^2 := by
      rw [Finset.sum_const]
      simp [nsmul_eq_mul]
      ring

theorem compatibleDivisorPairCountError_abs_le_one
    {H : Finset ℕ} {R W v N : ℕ} {d e : H → ℕ}
    (hW : 0 < W) (hd : IsMaynardDivisorTuple H R W d)
    (he : IsMaynardDivisorTuple H R W e)
    (hcross : IsCrossCoordinateCoprime H d e) :
    |compatibleDivisorPairCountError H v W N d e| ≤ 1 := by
  obtain ⟨err, herr, hcard⟩ :=
    compatibleDivisorPair_card_decomposition hW hd he hcross N
  have herr_eq : compatibleDivisorPairCountError H v W N d e = err := by
    unfold compatibleDivisorPairCountError
    rw [hcard]
    ring
  rw [herr_eq]
  exact herr

theorem compatibleDivisorPairCardSum_eq_main_add_error
    {H : Finset ℕ} {D : Finset (H → ℕ)}
    {lambda : (H → ℕ) → ℝ} {N v W : ℕ} :
    compatibleDivisorPairCardSum H D v W N lambda =
      compatibleDivisorPairMainSum H D W N lambda +
        compatibleDivisorPairErrorSum H D v W N lambda := by
  classical
  unfold compatibleDivisorPairCardSum compatibleDivisorPairMainSum
    compatibleDivisorPairErrorSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  unfold compatibleDivisorPairCountError
  ring

theorem abs_compatibleDivisorPairErrorSum_le_coefficientMass
    {H : Finset ℕ} {D : Finset (H → ℕ)}
    {lambda : (H → ℕ) → ℝ} {N v W R : ℕ}
    (hW : 0 < W) (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d) :
    |compatibleDivisorPairErrorSum H D v W N lambda| ≤
      compatibleDivisorPairCoefficientMass H D lambda := by
  classical
  unfold compatibleDivisorPairErrorSum compatibleDivisorPairCoefficientMass
  calc
    |∑ d ∈ D, ∑ e ∈ D.filter
        (fun e => IsCrossCoordinateCoprime H d e),
        compatibleDivisorPairCountError H v W N d e *
          (lambda d * lambda e)|
        ≤ ∑ d ∈ D, |∑ e ∈ D.filter
            (fun e => IsCrossCoordinateCoprime H d e),
            compatibleDivisorPairCountError H v W N d e *
              (lambda d * lambda e)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ D, ∑ e ∈ D.filter
          (fun e => IsCrossCoordinateCoprime H d e),
          |compatibleDivisorPairCountError H v W N d e *
            (lambda d * lambda e)| := by
      apply Finset.sum_le_sum
      intro d hd_mem
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ D, ∑ e ∈ D.filter
          (fun e => IsCrossCoordinateCoprime H d e),
          |lambda d * lambda e| := by
      apply Finset.sum_le_sum
      intro d hd_mem
      apply Finset.sum_le_sum
      intro e he_mem
      obtain ⟨he_memD, hcross⟩ := Finset.mem_filter.mp he_mem
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (compatibleDivisorPairCountError_abs_le_one (v := v) (N := N) hW
          (hD d hd_mem) (hD e he_memD) hcross)
        (abs_nonneg (lambda d * lambda e))

theorem isCrossCoordinateCoprime_of_pairCondition
    {H : Finset ℕ} {R W : ℕ} {d e : H → ℕ}
    (hd : IsMaynardDivisorTuple H R W d)
    (he : IsMaynardDivisorTuple H R W e)
    (hcoverage : CoversShiftDifferencePrimes H W) {n : ℕ}
    (hpair : divisorTuplePairCondition H n d e) :
    IsCrossCoordinateCoprime H d e := by
  intro a b hab
  constructor
  · by_contra hnot
    obtain ⟨p, hp, hpa, hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
    have hpa' : p ∣ n + a.1 := dvd_trans hpa (hpair.1 a)
    have hpb' : p ∣ n + b.1 := dvd_trans hpb (hpair.2 b)
    have hdist : p ∣ Nat.dist a.1 b.1 := by
      by_cases hab' : a.1 ≤ b.1
      · have hsub : p ∣ (n + b.1) - (n + a.1) := Nat.dvd_sub hpb' hpa'
        rw [Nat.dist_eq_sub_of_le hab']
        simpa [Nat.add_sub_add_left] using hsub
      · have hle : b.1 ≤ a.1 := le_of_not_ge hab'
        have hsub : p ∣ (n + a.1) - (n + b.1) := Nat.dvd_sub hpa' hpb'
        rw [Nat.dist_comm a.1 b.1, Nat.dist_eq_sub_of_le hle]
        simpa [Nat.add_sub_add_left] using hsub
    have hpW : p ∣ W := hcoverage hab p hp hdist
    have hpcop : Nat.Coprime p W :=
      (hd.coordinate_coprime_W a).coprime_dvd_left hpa
    exact (hp.coprime_iff_not_dvd.mp hpcop) hpW
  · by_contra hnot
    obtain ⟨p, hp, hpa, hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
    have hpa' : p ∣ n + a.1 := dvd_trans hpa (hpair.2 a)
    have hpb' : p ∣ n + b.1 := dvd_trans hpb (hpair.1 b)
    have hdist : p ∣ Nat.dist a.1 b.1 := by
      by_cases hab' : a.1 ≤ b.1
      · have hsub : p ∣ (n + b.1) - (n + a.1) := Nat.dvd_sub hpb' hpa'
        rw [Nat.dist_eq_sub_of_le hab']
        simpa [Nat.add_sub_add_left] using hsub
      · have hle : b.1 ≤ a.1 := le_of_not_ge hab'
        have hsub : p ∣ (n + a.1) - (n + b.1) := Nat.dvd_sub hpa' hpb'
        rw [Nat.dist_comm a.1 b.1, Nat.dist_eq_sub_of_le hle]
        simpa [Nat.add_sub_add_left] using hsub
    have hpW : p ∣ W := hcoverage hab p hp hdist
    have hpcop : Nat.Coprime p W :=
      (he.coordinate_coprime_W a).coprime_dvd_left hpa
    exact (hp.coprime_iff_not_dvd.mp hpcop) hpW

theorem sieveWeightSum_preSieved_eq_compatibleDivisorPairSieveSum
    {H : Finset ℕ} {D : Finset (H → ℕ)}
    {lambda : (H → ℕ) → ℝ} {N v W R : ℕ}
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (hcoverage : CoversShiftDifferencePrimes H W) :
    sieveWeightSum N (preSievedSquareDivisorWeight H D lambda v W) =
      compatibleDivisorPairSieveSum H D v W N lambda := by
  classical
  unfold compatibleDivisorPairSieveSum compatibleDivisorPairInnerSum
  rw [sieveWeightSum_preSieved_eq_pair_indicator]
  apply Finset.sum_congr rfl
  intro d hd_mem
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he_mem
  by_cases hcross : IsCrossCoordinateCoprime H d e
  · simp [hcross]
  · have hd := hD d hd_mem
    have he := hD e he_mem
    have hinner :
        (∑ n ∈ Finset.Ico N (2 * N),
          if n ≡ v [MOD W] ∧ divisorTuplePairCondition H n d e
          then lambda d * lambda e else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have hfalse : ¬(n ≡ v [MOD W] ∧ divisorTupleCondition H n d ∧
          divisorTupleCondition H n e) := by
        intro hcond
        exact hcross (isCrossCoordinateCoprime_of_pairCondition hd he
          hcoverage hcond.2)
      simp [divisorTuplePairCondition, hfalse]
    simp [hcross, hinner]

theorem compatibleDivisorPairSieveSum_eq_cardSum
    {H : Finset ℕ} {D : Finset (H → ℕ)}
    {lambda : (H → ℕ) → ℝ} {N v W R : ℕ}
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d) :
    compatibleDivisorPairSieveSum H D v W N lambda =
      compatibleDivisorPairCardSum H D v W N lambda := by
  classical
  unfold compatibleDivisorPairSieveSum compatibleDivisorPairCardSum
    compatibleDivisorPairInnerSum
  apply Finset.sum_congr rfl
  intro d hd_mem
  apply Finset.sum_congr rfl
  intro e he_mem
  obtain ⟨he_memD, hcross⟩ := Finset.mem_filter.mp he_mem
  have hd := hD d hd_mem
  have he := hD e he_memD
  have hcard :
      ((Finset.Ico N (2 * N)).filter (fun n =>
        n ≡ divisorPairCrtResidue H R W v d e hd he hcross
          [MOD divisorPairModulus H W d e])).card =
        ((Finset.Ico N (2 * N)).filter (fun n =>
          n ≡ v [MOD W] ∧ divisorTuplePairCondition H n d e)).card := by
    apply congrArg Finset.card
    ext n
    simp only [Finset.mem_filter]
    exact and_congr_right (fun _ =>
      (modEq_divisorPairCrtResidue_iff hd he hcross n))
  rw [compatibleDivisorPair_indicator_sum_eq_card_mul
    hd he hcross N (2 * N) (lambda d * lambda e)]
  rw [hcard]

theorem sieveWeightSum_preSieved_eq_compatibleDivisorPairCardSum
    {H : Finset ℕ} {D : Finset (H → ℕ)}
    {lambda : (H → ℕ) → ℝ} {N v W R : ℕ}
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (hcoverage : CoversShiftDifferencePrimes H W) :
    sieveWeightSum N (preSievedSquareDivisorWeight H D lambda v W) =
      compatibleDivisorPairCardSum H D v W N lambda := by
  exact (sieveWeightSum_preSieved_eq_compatibleDivisorPairSieveSum
    hD hcoverage).trans (compatibleDivisorPairSieveSum_eq_cardSum hD)

theorem sieveWeightSum_preSieved_eq_compatibleDivisorPairMainSum_add_error
    {H : Finset ℕ} {D : Finset (H → ℕ)}
    {lambda : (H → ℕ) → ℝ} {N v W R : ℕ}
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (hcoverage : CoversShiftDifferencePrimes H W) :
    sieveWeightSum N (preSievedSquareDivisorWeight H D lambda v W) =
      compatibleDivisorPairMainSum H D W N lambda +
        compatibleDivisorPairErrorSum H D v W N lambda := by
  rw [sieveWeightSum_preSieved_eq_compatibleDivisorPairCardSum
    hD hcoverage]
  exact compatibleDivisorPairCardSum_eq_main_add_error

theorem abs_sieveWeightSum_preSieved_sub_main_le_coefficientMass
    {H : Finset ℕ} {D : Finset (H → ℕ)}
    {lambda : (H → ℕ) → ℝ} {N v W R : ℕ}
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (hcoverage : CoversShiftDifferencePrimes H W) (hW : 0 < W) :
    |sieveWeightSum N (preSievedSquareDivisorWeight H D lambda v W) -
        compatibleDivisorPairMainSum H D W N lambda| ≤
      compatibleDivisorPairCoefficientMass H D lambda := by
  rw [sieveWeightSum_preSieved_eq_compatibleDivisorPairMainSum_add_error
    hD hcoverage]
  have herr := abs_compatibleDivisorPairErrorSum_le_coefficientMass
    (lambda := lambda) hW hD (v := v) (N := N)
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using herr

theorem abs_sieveWeightSum_preSieved_sub_main_le_card_sq_mul
    {H : Finset ℕ} {D : Finset (H → ℕ)}
    {lambda : (H → ℕ) → ℝ} {N v W R : ℕ} {L : ℝ}
    (hD : ∀ d ∈ D, IsMaynardDivisorTuple H R W d)
    (hcoverage : CoversShiftDifferencePrimes H W) (hW : 0 < W)
    (hL : 0 ≤ L) (hbound : ∀ d ∈ D, |lambda d| ≤ L) :
    |sieveWeightSum N (preSievedSquareDivisorWeight H D lambda v W) -
        compatibleDivisorPairMainSum H D W N lambda| ≤
      (D.card : ℝ)^2 * L^2 := by
  exact (abs_sieveWeightSum_preSieved_sub_main_le_coefficientMass
    hD hcoverage hW).trans
    (compatibleDivisorPairCoefficientMass_le_card_sq_mul hL hbound)

end BoundedGaps.Maynard
