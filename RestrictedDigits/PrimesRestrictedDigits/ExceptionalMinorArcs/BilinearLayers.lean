import PrimesRestrictedDigits.ExceptionalMinorArcs.BilinearPhase
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Find

/-!
# Dyadic width layers for the exceptional bilinear estimate

The source suppresses both the terminal dyadic bucket and the averaging constant. This file
records the finite layer family and the exact pigeonhole step used in repaired Lemma 13.1.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

/-- There are `4 * length + 1` dyadic widths, indexed from zero. -/
def bilinearLayerCount (length : Nat) : Nat :=
  4 * length + 1

/-- The ascending dyadic widths `2^j * N / 10^length`. -/
noncomputable def bilinearLayerWidth
    (length : Nat) (N : Real) (j : Nat) : Real :=
  (2 : Real) ^ j * N / ((10 ^ length : Nat) : Real)

theorem bilinearLayerCount_pos (length : Nat) :
    0 < bilinearLayerCount length := by
  simp [bilinearLayerCount]

@[simp]
theorem mem_range_bilinearLayerCount_iff
    {length j : Nat} :
    j ∈ Finset.range (bilinearLayerCount length) ↔ j <= 4 * length := by
  simp [bilinearLayerCount]

theorem bilinearLayerWidth_pos
    {length : Nat} {N : Real} (hN : 0 < N) (j : Nat) :
    0 < bilinearLayerWidth length N j := by
  rw [bilinearLayerWidth]
  exact div_pos (mul_pos (by positivity) hN) (by positivity)

@[simp]
theorem bilinearLayerWidth_zero (length : Nat) (N : Real) :
    bilinearLayerWidth length N 0 =
      N / ((10 ^ length : Nat) : Real) := by
  simp [bilinearLayerWidth]

theorem bilinearLayerWidth_succ
    (length : Nat) (N : Real) (j : Nat) :
    bilinearLayerWidth length N (j + 1) =
      2 * bilinearLayerWidth length N j := by
  simp only [bilinearLayerWidth, pow_succ]
  ring

/-- Every dyadic layer is at least the base width `N / 10^length`. -/
theorem bilinearLayerWidth_zero_le
    {length : Nat} {N : Real} (hN : 0 <= N) (j : Nat) :
    N / ((10 ^ length : Nat) : Real) <=
      bilinearLayerWidth length N j := by
  have hpow : (1 : Real) <= 2 ^ j := one_le_pow₀ (by norm_num)
  have hX : (0 : Real) < ((10 ^ length : Nat) : Real) := by positivity
  rw [bilinearLayerWidth]
  apply div_le_div_of_nonneg_right _ hX.le
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hpow hN

/-- The final width is at least one once `N >= 1`; thus it captures every
nearest-integer distance, including the endpoint `1 / 2`. -/
theorem one_le_bilinearLayerWidth_terminal
    {length : Nat} {N : Real} (hN : 1 <= N) :
    1 <= bilinearLayerWidth length N (4 * length) := by
  let X : Real := ((10 ^ length : Nat) : Real)
  have hX : 0 < X := by dsimp only [X]; positivity
  have hpowNat : 10 ^ length <= 2 ^ (4 * length) := by
    calc
      10 ^ length <= 16 ^ length := Nat.pow_le_pow_left (by norm_num) _
      _ = (2 ^ 4) ^ length := by norm_num
      _ = 2 ^ (4 * length) := by rw [pow_mul]
  have hpowReal : X <= (2 : Real) ^ (4 * length) := by
    dsimp only [X]
    exact_mod_cast hpowNat
  rw [bilinearLayerWidth]
  apply (le_div_iff₀ hX).2
  calc
    1 * X <= (2 : Real) ^ (4 * length) * 1 := by
      simpa only [one_mul, mul_one] using hpowReal
    _ <= (2 : Real) ^ (4 * length) * N := by
      exact mul_le_mul_of_nonneg_left hN (by positivity)

/-- Pointwise layer-cake domination of the zero-safe kernel. The use of the
least captured layer makes the factor two and all endpoint conventions
explicit. -/
theorem cappedNearestIntegerKernel_le_bilinearLayerSum
    {length : Nat} {N : Real} (hN : 1 <= N) (theta : Real) :
    cappedNearestIntegerKernel
        (((10 ^ length : Nat) : Real) / N) theta <=
      2 * ∑ j ∈ Finset.range (bilinearLayerCount length),
        if nearestIntegerDistance theta <= bilinearLayerWidth length N j then
          1 / bilinearLayerWidth length N j
        else 0 := by
  let X : Real := ((10 ^ length : Nat) : Real)
  let L : Real := X / N
  let d := nearestIntegerDistance theta
  let delta : Nat -> Real := bilinearLayerWidth length N
  have hX : 0 < X := by dsimp only [X]; positivity
  have hNPos : 0 < N := zero_lt_one.trans_le hN
  have hL : 0 < L := div_pos hX hNPos
  have hdNonneg : 0 <= d := nearestIntegerDistance_nonneg theta
  have hterminal : d <= delta (4 * length) := by
    calc
      d <= 1 / 2 := nearestIntegerDistance_le_half theta
      _ <= 1 := by norm_num
      _ <= delta (4 * length) :=
        one_le_bilinearLayerWidth_terminal hN
  have hexists : ∃ j : Nat, d <= delta j := ⟨4 * length, hterminal⟩
  let j := Nat.find hexists
  have hjCaptured : d <= delta j := Nat.find_spec hexists
  have hjBound : j <= 4 * length := Nat.find_min' hexists hterminal
  have hjMem : j ∈ Finset.range (bilinearLayerCount length) :=
    mem_range_bilinearLayerCount_iff.mpr hjBound
  have hdeltaPos (k : Nat) : 0 < delta k :=
    bilinearLayerWidth_pos hNPos k
  have hsumNonneg :
      0 <= ∑ k ∈ Finset.range (bilinearLayerCount length),
        if d <= delta k then 1 / delta k else 0 := by
    apply Finset.sum_nonneg
    intro k hk
    split_ifs
    · exact one_div_nonneg.mpr (hdeltaPos k).le
    · exact le_rfl
  have hjTerm :
      1 / delta j <=
        ∑ k ∈ Finset.range (bilinearLayerCount length),
          if d <= delta k then 1 / delta k else 0 := by
    calc
      1 / delta j = if d <= delta j then 1 / delta j else 0 := by
        simp [hjCaptured]
      _ <= ∑ k ∈ Finset.range (bilinearLayerCount length),
          if d <= delta k then 1 / delta k else 0 := by
        exact Finset.single_le_sum
          (s := Finset.range (bilinearLayerCount length))
          (f := fun k => if d <= delta k then 1 / delta k else 0)
          (fun k hk => by
            split_ifs
            · exact one_div_nonneg.mpr (hdeltaPos k).le
            · exact le_rfl) hjMem
  change cappedNearestIntegerKernel L theta <=
    2 * ∑ k ∈ Finset.range (bilinearLayerCount length),
      if d <= delta k then 1 / delta k else 0
  have hjDef : j = Nat.find hexists := rfl
  rcases j with _ | k
  · have hrecip : 1 / delta 0 = L := by
      dsimp only [delta, L, X]
      rw [bilinearLayerWidth_zero]
      field_simp
    calc
      cappedNearestIntegerKernel L theta <= L :=
        cappedNearestIntegerKernel_le hL.le theta
      _ = 1 / delta 0 := hrecip.symm
      _ <= ∑ i ∈ Finset.range (bilinearLayerCount length),
          if d <= delta i then 1 / delta i else 0 := hjTerm
      _ <= 2 * ∑ i ∈ Finset.range (bilinearLayerCount length),
          if d <= delta i then 1 / delta i else 0 := by linarith
  · have hprevious : ¬d <= delta k := by
      apply Nat.find_min hexists
      rw [← hjDef]
      exact Nat.lt_succ_self k
    have hdPos : 0 < d := (hdeltaPos k).trans (lt_of_not_ge hprevious)
    have hdeltaSucc : delta (k + 1) = 2 * delta k :=
      bilinearLayerWidth_succ length N k
    have hwidthLt : delta (k + 1) < 2 * d := by
      rw [hdeltaSucc]
      exact mul_lt_mul_of_pos_left (lt_of_not_ge hprevious) (by norm_num)
    have hinvLt : 1 / d < 2 / delta (k + 1) := by
      apply (div_lt_div_iff₀ hdPos (hdeltaPos (k + 1))).2
      simpa only [one_mul] using hwidthLt
    calc
      cappedNearestIntegerKernel L theta <= d⁻¹ := by
        exact cappedNearestIntegerKernel_le_inv hL hdPos
      _ = 1 / d := by rw [inv_eq_one_div]
      _ <= 2 / delta (k + 1) := hinvLt.le
      _ = 2 * (1 / delta (k + 1)) := by ring
      _ <= 2 * ∑ i ∈ Finset.range (bilinearLayerCount length),
          if d <= delta i then 1 / delta i else 0 := by
        exact mul_le_mul_of_nonneg_left hjTerm (by norm_num)

/-- If the sum of `D` normalized layer counts exceeds the source threshold,
one layer has density at least `K / (20 * D)`. -/
theorem exists_bilinearRichLayer
    {D : Nat} (hD : 0 < D) (count width : Fin D -> Real)
    (hwidth : ∀ j, 0 < width j) {K N : Real}
    (hsum : K * N ^ 2 / 20 < ∑ j, count j / width j) :
    ∃ j : Fin D,
      width j * N ^ 2 * (K / (20 * D)) <= count j := by
  let average : Real := K * N ^ 2 / (20 * D)
  have hDReal : (D : Real) ≠ 0 := by exact_mod_cast hD.ne'
  have haverage : (D : Real) * average = K * N ^ 2 / 20 := by
    dsimp only [average]
    field_simp
  have hsumAverage :
      ∑ _j : Fin D, average <= ∑ j : Fin D, count j / width j := by
    simpa [haverage] using hsum.le
  let j0 : Fin D := ⟨0, hD⟩
  have huniv : (Finset.univ : Finset (Fin D)).Nonempty :=
    ⟨j0, Finset.mem_univ _⟩
  obtain ⟨j, _hj, hj⟩ :=
    Finset.exists_le_of_sum_le huniv hsumAverage
  refine ⟨j, ?_⟩
  have hmul := (le_div_iff₀ (hwidth j)).1 hj
  dsimp only [average] at hmul
  calc
    width j * N ^ 2 * (K / (20 * D)) =
        K * N ^ 2 / (20 * D) * width j := by ring
    _ <= count j := hmul

end PrimesRestrictedDigits
