import PrimesRestrictedDigits.MajorArcs.M2Absorption
import PrimesRestrictedDigits.MajorArcs.Region
import PrimesRestrictedDigits.SieveAsymptotics.TypeIICubeFamily
import Mathlib.Data.Fin.Tuple.Finset

/-!
# Bounded natural grid for Type II cubes

This is the exact finite half-open grid used in the proof of Proposition 7.2. The
ceiling-minus-one anchor preserves the source `Ioc` endpoints. Its exact cardinality absorbs
the anchor-count term.
-/

open scoped BigOperators

namespace PrimesRestrictedDigits

noncomputable section

/-- The minimal number of side intervals needed to cover `(0,1]` at positive
width `delta`. -/
noncomputable def typeIINaturalCubeGridSide (delta : Real) : Nat :=
  Nat.ceil delta⁻¹

/-- The minimal finite Cartesian grid of natural Type II cube anchors. -/
noncomputable def typeIINaturalCubeGrid (k : Nat) (delta : Real) :
    Finset (Fin k -> Nat) :=
  Fintype.piFinset fun _ : Fin k =>
    Finset.range (typeIINaturalCubeGridSide delta)

/-- The unique half-open grid anchor assigned to a positive projected point. -/
noncomputable def typeIICeilingCubeAnchor {k : Nat}
    (delta : Real) (x : Fin k -> Real) : Fin k -> Nat :=
  fun i => Nat.ceil (x i / delta) - 1

@[simp] theorem mem_typeIINaturalCubeGrid
    {k : Nat} {delta : Real} {anchor : Fin k -> Nat} :
    anchor ∈ typeIINaturalCubeGrid k delta <->
      ∀ i, anchor i < typeIINaturalCubeGridSide delta := by
  simp [typeIINaturalCubeGrid]

@[simp] theorem card_typeIINaturalCubeGrid (k : Nat) (delta : Real) :
    (typeIINaturalCubeGrid k delta).card =
      typeIINaturalCubeGridSide delta ^ k := by
  simp [typeIINaturalCubeGrid]

/-- Ceiling-minus-one puts every positive coordinate in its exact half-open
cell. -/
theorem typeIICeilingCubeAnchor_point_mem_projectedLogBox
    {k : Nat} {delta : Real} {x : Fin k -> Real}
    (hdelta : 0 < delta) (hx0 : ∀ i, 0 < x i) :
    x ∈ projectedLogBox
      (scaledNaturalCubeAnchor delta (typeIICeilingCubeAnchor delta x))
      delta := by
  intro i
  have hratio : 0 < x i / delta := div_pos (hx0 i) hdelta
  have hceilPos : 0 < Nat.ceil (x i / delta) := Nat.ceil_pos.mpr hratio
  have hceil := (Nat.ceil_eq_iff hceilPos.ne').mp rfl
  have hsucc : Nat.ceil (x i / delta) - 1 + 1 =
      Nat.ceil (x i / delta) := by omega
  constructor
  · simpa only [typeIICeilingCubeAnchor, scaledNaturalCubeAnchor] using
      ((lt_div_iff₀ hdelta).mp hceil.1)
  · have hupper : x i <= ((Nat.ceil (x i / delta) : Nat) : Real) * delta :=
      (div_le_iff₀ hdelta).mp hceil.2
    have hcastSucc :
        ((Nat.ceil (x i / delta) - 1 : Nat) : Real) + 1 =
          (Nat.ceil (x i / delta) : Real) := by
      exact_mod_cast hsucc
    rw [← hcastSucc] at hupper
    simpa only [typeIICeilingCubeAnchor, scaledNaturalCubeAnchor,
      add_mul, one_mul] using hupper

/-- A point of `(0,1]^k` has its ceiling anchor in the minimal grid. -/
theorem typeIICeilingCubeAnchor_mem_typeIINaturalCubeGrid
    {k : Nat} {delta : Real} {x : Fin k -> Real}
    (hdelta : 0 < delta) (hx0 : ∀ i, 0 < x i)
    (hx1 : ∀ i, x i <= 1) :
    typeIICeilingCubeAnchor delta x ∈ typeIINaturalCubeGrid k delta := by
  rw [mem_typeIINaturalCubeGrid]
  intro i
  have hratio : 0 < x i / delta := div_pos (hx0 i) hdelta
  have hceilPos : 0 < Nat.ceil (x i / delta) := Nat.ceil_pos.mpr hratio
  have hquotient : x i / delta <= 1 / delta :=
    (div_le_div_iff_of_pos_right hdelta).2 (hx1 i)
  have hceilLe : Nat.ceil (x i / delta) <= Nat.ceil (1 / delta) :=
    Nat.ceil_mono hquotient
  exact (Nat.sub_lt hceilPos (by omega : 0 < 1)).trans_le <| by
    simpa only [typeIINaturalCubeGridSide, one_div] using hceilLe

/-- Positive-width half-open cells containing the same point have the same
natural anchor. -/
theorem eq_of_mem_projectedLogBox_scaledNaturalCubeAnchor
    {k : Nat} {delta : Real} {x : Fin k -> Real}
    {u v : Fin k -> Nat} (hdelta : 0 < delta)
    (hu : x ∈ projectedLogBox (scaledNaturalCubeAnchor delta u) delta)
    (hv : x ∈ projectedLogBox (scaledNaturalCubeAnchor delta v) delta) :
    u = v := by
  funext i
  by_contra huv
  rcases lt_or_gt_of_ne huv with huvIndex | hvuIndex
  · have hindex : u i + 1 <= v i := by omega
    have hindexReal : ((u i + 1 : Nat) : Real) <= (v i : Real) := by
      exact_mod_cast hindex
    have hscaled := mul_le_mul_of_nonneg_right hindexReal hdelta.le
    have hend : scaledNaturalCubeAnchor delta u i + delta <=
        scaledNaturalCubeAnchor delta v i := by
      simpa [scaledNaturalCubeAnchor, Nat.cast_add, add_mul] using hscaled
    exact (not_lt_of_ge ((hu i).2.trans hend)) (hv i).1
  · have hindex : v i + 1 <= u i := by omega
    have hindexReal : ((v i + 1 : Nat) : Real) <= (u i : Real) := by
      exact_mod_cast hindex
    have hscaled := mul_le_mul_of_nonneg_right hindexReal hdelta.le
    have hend : scaledNaturalCubeAnchor delta v i + delta <=
        scaledNaturalCubeAnchor delta u i := by
      simpa [scaledNaturalCubeAnchor, Nat.cast_add, add_mul] using hscaled
    exact (not_lt_of_ge ((hv i).2.trans hend)) (hu i).1

/-- The minimal grid gives unique half-open coverage of `(0,1]^k`. -/
theorem existsUnique_typeIINaturalCubeGrid_anchor
    {k : Nat} {delta : Real} {x : Fin k -> Real}
    (hdelta : 0 < delta) (hx0 : ∀ i, 0 < x i)
    (hx1 : ∀ i, x i <= 1) :
    ∃! anchor : Fin k -> Nat,
      anchor ∈ typeIINaturalCubeGrid k delta ∧
        x ∈ projectedLogBox (scaledNaturalCubeAnchor delta anchor) delta := by
  refine ⟨typeIICeilingCubeAnchor delta x,
    ⟨typeIICeilingCubeAnchor_mem_typeIINaturalCubeGrid hdelta hx0 hx1,
      typeIICeilingCubeAnchor_point_mem_projectedLogBox hdelta hx0⟩, ?_⟩
  intro anchor hanchor
  exact eq_of_mem_projectedLogBox_scaledNaturalCubeAnchor hdelta
    hanchor.2 (typeIICeilingCubeAnchor_point_mem_projectedLogBox hdelta hx0)

/-- For width at most one, the real side length is at most `2 / delta`. -/
theorem typeIINaturalCubeGridSide_cast_le_two_div
    {delta : Real} (hdelta : 0 < delta) (hdeltaOne : delta <= 1) :
    (typeIINaturalCubeGridSide delta : Real) <= 2 / delta := by
  have hinvNonneg : 0 <= delta⁻¹ := inv_nonneg.mpr hdelta.le
  have hinvOne : 1 <= delta⁻¹ := (one_le_inv₀ hdelta).2 hdeltaOne
  have hceil : (typeIINaturalCubeGridSide delta : Real) < delta⁻¹ + 1 := by
    simpa only [typeIINaturalCubeGridSide] using
      Nat.ceil_lt_add_one hinvNonneg
  calc
    (typeIINaturalCubeGridSide delta : Real) <= delta⁻¹ + 1 := hceil.le
    _ <= delta⁻¹ + delta⁻¹ := add_le_add_right hinvOne _
    _ = 2 / delta := by rw [div_eq_mul_inv]; ring

/-- The exact grid card satisfies the source's coarse `(2 / delta)^k` bound. -/
theorem card_typeIINaturalCubeGrid_cast_le_two_div_pow
    (k : Nat) {delta : Real} (hdelta : 0 < delta)
    (hdeltaOne : delta <= 1) :
    ((typeIINaturalCubeGrid k delta).card : Real) <= (2 / delta) ^ k := by
  rw [card_typeIINaturalCubeGrid, Nat.cast_pow]
  exact pow_le_pow_left₀ (by positivity)
    (typeIINaturalCubeGridSide_cast_le_two_div hdelta hdeltaOne) k

/-- At positive decimal length, the log-log grid side is at most `log X`. -/
theorem typeIINaturalCubeGridSide_logLog_le_log
    {length : Nat} (hlength : 1 <= length) :
    (typeIINaturalCubeGridSide
        (majorArcM2LogLogDelta (10 ^ length)) : Real) <=
      Real.log (((10 ^ length : Nat) : Real)) := by
  let XNat : Nat := 10 ^ length
  let L : Real := Real.log (XNat : Real)
  have hL : 1 < L := by
    dsimp only [L, XNat]
    have htenLe : 10 <= 10 ^ length := by
      simpa using
        (Nat.pow_le_pow_right (by norm_num : 0 < (10 : Nat)) hlength)
    exact (Real.lt_log_iff_exp_lt (by positivity)).mpr <|
      Real.exp_one_lt_three.trans_le
        (by exact_mod_cast (show 3 <= 10 ^ length by omega))
  have hceil : ((Nat.ceil (Real.log L) : Nat) : Real) <
      Real.log L + 1 :=
    Nat.ceil_lt_add_one (Real.log_nonneg hL.le)
  have hlogUpper : Real.log L <= L - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  dsimp only [typeIINaturalCubeGridSide, majorArcM2LogLogDelta]
  rw [inv_inv]
  dsimp only [L, XNat] at hceil hlogUpper ⊢
  linarith

/-- The real card of the decimal log-log grid is at most `log(X)^k`. -/
theorem card_typeIINaturalCubeGrid_logLog_cast_le_log_pow
    {length k : Nat} (hlength : 1 <= length) :
    ((typeIINaturalCubeGrid k
        (majorArcM2LogLogDelta (10 ^ length))).card : Real) <=
      Real.log (((10 ^ length : Nat) : Real)) ^ k := by
  rw [card_typeIINaturalCubeGrid, Nat.cast_pow]
  exact pow_le_pow_left₀ (by positivity)
    (typeIINaturalCubeGridSide_logLog_le_log hlength) k

/--
Any subfamily of the decimal grid has its anchor-count term absorbed by the `delta` term.
-/
theorem typeIIAnchorFamily_logError_le_delta_logError
    {length k : Nat} (hlength : 1 <= length)
    (anchors : Finset (Fin k -> Nat))
    (hanchors : anchors ⊆ typeIINaturalCubeGrid k
      (majorArcM2LogLogDelta (10 ^ length)))
    (card : Real) (hcard : 0 <= card) :
    (anchors.card : Real) * card /
        Real.log (((10 ^ length : Nat) : Real)) ^ (k + 2) <=
      majorArcM2LogLogDelta (10 ^ length) * card /
        Real.log (((10 ^ length : Nat) : Real)) := by
  let XNat : Nat := 10 ^ length
  let L : Real := Real.log (XNat : Real)
  let delta : Real := majorArcM2LogLogDelta XNat
  have hL : 1 < L := by
    dsimp only [L, XNat]
    have htenLe : 10 <= 10 ^ length := by
      simpa using
        (Nat.pow_le_pow_right (by norm_num : 0 < (10 : Nat)) hlength)
    exact (Real.lt_log_iff_exp_lt (by positivity)).mpr <|
      Real.exp_one_lt_three.trans_le
        (by exact_mod_cast (show 3 <= 10 ^ length by omega))
  have hlogL : 0 < Real.log L := Real.log_pos hL
  have hlogLLe : Real.log L <= L :=
    (Real.log_le_sub_one_of_pos (by linarith : 0 < L)).trans (by linarith)
  have hdelta : delta = 1 / Real.log L := by
    dsimp only [delta, majorArcM2LogLogDelta, L]
    rw [one_div]
  have hinv : 1 / L <= delta := by
    rw [hdelta]
    exact one_div_le_one_div_of_le hlogL hlogLLe
  have hanchorCardNat := Finset.card_le_card hanchors
  have hanchorCard : (anchors.card : Real) <= L ^ k := by
    calc
      (anchors.card : Real) <=
          ((typeIINaturalCubeGrid k delta).card : Real) := by
        exact_mod_cast hanchorCardNat
      _ <= L ^ k := by
        simpa only [delta, L, XNat] using
          card_typeIINaturalCubeGrid_logLog_cast_le_log_pow
            (k := k) hlength
  have hfirst : (anchors.card : Real) * card / L ^ (k + 2) <=
      L ^ k * card / L ^ (k + 2) :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hanchorCard hcard) (by positivity)
  have heq : L ^ k * card / L ^ (k + 2) =
      (1 / L) * (card / L) := by
    field_simp [ne_of_gt hL]
    ring
  have hmul : (1 / L) * (card / L) <= delta * (card / L) :=
    mul_le_mul_of_nonneg_right hinv (by positivity)
  have hmul' : (1 / L) * (card / L) <= delta * card / L := by
    simpa [div_eq_mul_inv, mul_assoc] using hmul
  dsimp only [XNat, L, delta] at hfirst heq hmul' ⊢
  rw [heq] at hfirst
  exact hfirst.trans hmul'

end

end PrimesRestrictedDigits
