import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece0RowTFiberD873
import PrimesRestrictedDigits.SieveAsymptotics.SectionSixFirstLowCentralSmallI5P1Piece0RowFubiniD874
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
/-! # SectionSixFirstLowCentralSmallI5P1Piece0RowCompositionD875 -/

set_option autoImplicit false
set_option warningAsError true

open MeasureTheory Set
open scoped BigOperators

namespace PrimesRestrictedDigits
noncomputable section

/-!
# compose the generic t-fiber bound with the
row Fubini identity. The public theorem is deliberately row-local:
it ends at the explicit Q4 triangular primitive and makes no finite-row or
global cap claim.
-/

private abbrev G : Real := sectionSixFirstLowCentralSmallI5P1D807Gap
private abbrev H : Real → Real := sectionSixFirstLowCentralSmallI5P1D807H
private abbrev K : SectionSixP1AffineT → Real :=
  sectionSixFirstLowCentralSmallI5P1D809Kernel
private abbrev Q4 : Real → Real → Real :=
  sectionSixFirstLowCentralSmallI5P1D816Row0Q4
private abbrev Prim : Real → Real → Real :=
  sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive

def sectionSixFirstLowCentralSmallI5P1D875P0RowFactor (i : Fin 256) : Real :=
  sectionSixFirstLowCentralSmallI5P1D816Row0TailC /
      (sectionSixFirstLowCentralSmallI5P1D807Beta -
        sectionSixFirstLowCentralSmallI5P1D871P0RowUpper i) *
    (1 / G - 1 /
      (sectionSixFirstLowCentralSmallI5P1D871P0RowUpper i - G))

def sectionSixFirstLowCentralSmallI5P1D875P0RowMajorant (i : Fin 256) (d : Real) : Real :=
  sectionSixFirstLowCentralSmallI5P1D875P0RowFactor i *
    (Prim (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i) (H d)) ^ 2 / 2

private theorem interval_integral_mono_of_nonneg_left
    {f g : Real → Real} {a b : Real}
    (hab : a ≤ b)
    (hf : ∀ x ∈ Set.Ioc a b, 0 ≤ f x)
    (hg : IntervalIntegrable g volume a b)
    (hfg : ∀ x ∈ Set.Ioc a b, f x ≤ g x) :
    (∫ x in a..b, f x) ≤ ∫ x in a..b, g x := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  apply MeasureTheory.integral_mono_of_nonneg
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hf x hx
  · exact hg.1
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hfg x hx

private theorem row_d_bounds {i : Fin 256} {d : Real}
    (hd : d ∈ Set.Icc
      (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i)
      (sectionSixFirstLowCentralSmallI5P1D871P0RowUpper i)) :
    sectionSixFirstLowCentralSmallI5P1D807D0 ≤ d ∧
      d ≤ sectionSixFirstLowCentralSmallI5P1D807Ds := by
  have ho := sectionSixFirstLowCentralSmallI5P1D871_p0Row_endpoint_order i
  exact ⟨ho.1.trans hd.1, hd.2.trans ho.2.2⟩

private theorem row_h_nonneg {i : Fin 256} {d : Real}
    (hd : d ∈ Set.Icc
      (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i)
      (sectionSixFirstLowCentralSmallI5P1D871P0RowUpper i)) :
    0 ≤ H d := by
  have hdb := row_d_bounds hd
  rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
    ⟨hA, hBeta, hGap, hD0, hDs, hDr, hD1⟩
  unfold H sectionSixFirstLowCentralSmallI5P1D807H
  have hdle : d ≤ (29 / 200 : Real) := by simpa [hDs] using hdb.2
  rw [hBeta]
  norm_num [sectionSixFirstLowCentralSmallI5P1D807Square]
  linarith

private theorem row_gap_order {i : Fin 256} {d : Real}
    (hd : d ∈ Set.Icc
      (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i)
      (sectionSixFirstLowCentralSmallI5P1D871P0RowUpper i)) :
    G ≤ d - G := by
  have hdb := row_d_bounds hd
  rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
    ⟨hA, hBeta, hGap, hD0, hDs, hDr, hD1⟩
  change sectionSixFirstLowCentralSmallI5P1D807Gap ≤
    d - sectionSixFirstLowCentralSmallI5P1D807Gap
  rw [hGap]
  rw [hD0] at hdb
  linarith

private theorem row_point_mem_piece0 {i : Fin 256} {d r s t : Real}
    (hd : d ∈ Set.Icc
      (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i)
      (sectionSixFirstLowCentralSmallI5P1D871P0RowUpper i))
    (hr : r ∈ Set.Icc 0 (H d))
    (hs : s ∈ Set.Icc 0 r)
    (ht : t ∈ Set.Icc G (d - G)) :
    (((d, r), s), t) ∈ sectionSixFirstLowCentralSmallI5P1D807Piece0 := by
  have hdb := row_d_bounds hd
  change d ∈ Set.Icc sectionSixFirstLowCentralSmallI5P1D807D0
      sectionSixFirstLowCentralSmallI5P1D807Ds ∧
    r ∈ Set.Icc 0 (sectionSixFirstLowCentralSmallI5P1D807H d) ∧
    s ∈ Set.Icc 0 r ∧ t ∈ Set.Icc
      sectionSixFirstLowCentralSmallI5P1D807Gap
      (d - sectionSixFirstLowCentralSmallI5P1D807Gap)
  exact ⟨hdb, hr, hs, ht⟩

private theorem t_integral_nonneg {i : Fin 256} {d r s : Real}
    (hd : d ∈ Set.Icc
      (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i)
      (sectionSixFirstLowCentralSmallI5P1D871P0RowUpper i))
    (hr : r ∈ Set.Icc 0 (H d))
    (hs : s ∈ Set.Icc 0 r) :
    0 ≤ (∫ t in G..(d - G), K (((d, r), s), t)) := by
  apply intervalIntegral.integral_nonneg (row_gap_order hd)
  intro t ht
  exact sectionSixFirstLowCentralSmallI5P1D809_kernel_nonneg_piece (0 : Fin 3)
    (by simpa [K, sectionSixFirstLowCentralSmallI5P1D808Piece] using
      row_point_mem_piece0 hd hr hs ht)

private theorem row_lower_pos (i : Fin 256) :
    0 < sectionSixFirstLowCentralSmallI5P1D871P0RowLower i := by
  have ho := sectionSixFirstLowCentralSmallI5P1D871_p0Row_endpoint_order i
  rcases sectionSixFirstLowCentralSmallI5P1D807_constants with
    ⟨hA, hBeta, hGap, hD0, hDs, hDr, hD1⟩
  have hD0pos : 0 < sectionSixFirstLowCentralSmallI5P1D807D0 := by
    rw [hD0]
    norm_num
  exact hD0pos.trans_le ho.1

private theorem q4_primitive_zero (a : Real) : Prim a 0 = 0 := by
  simp [Prim, sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive,
    sectionSixFirstLowCentralSmallI5P1D814Q4Primitive]

private theorem q4_inner_eq_primitive {a r : Real} (ha : a ≠ 0) :
    (∫ s in (0 : Real)..r, Q4 a s) = Prim a r := by
  calc
    (∫ s in (0 : Real)..r, Q4 a s) =
        sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive a r -
          sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive a 0 := by
      simpa [Q4] using
        (sectionSixFirstLowCentralSmallI5P1D816_q4_interval_eq_primitive ha)
    _ = Prim a r := by
      rw [show sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive a 0 = 0 by
        simpa [Prim] using q4_primitive_zero a]
      simp [Prim]

private theorem row_q4_s_intervalIntegrable {i : Fin 256} {r : Real} :
    IntervalIntegrable
      (fun s : Real => sectionSixFirstLowCentralSmallI5P1D875P0RowFactor i * Q4
        (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i) r * Q4
          (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i) s)
      volume 0 r := by
  have hq := sectionSixFirstLowCentralSmallI5P1D816_q4_continuous
    (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i)
  exact ((continuous_const.mul continuous_const).mul
    (hq.comp continuous_id)).intervalIntegrable _ _

private theorem row_inner_le {i : Fin 256} {d r : Real}
    (hd : d ∈ Set.Icc
      (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i)
      (sectionSixFirstLowCentralSmallI5P1D871P0RowUpper i))
    (hr : r ∈ Set.Icc 0 (H d)) :
    (∫ s in (0 : Real)..r,
      ∫ t in G..(d - G), K (((d, r), s), t)) ≤
      ∫ s in (0 : Real)..r,
        sectionSixFirstLowCentralSmallI5P1D875P0RowFactor i * Q4
          (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i) r * Q4
          (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i) s := by
  apply interval_integral_mono_of_nonneg_left hr.1
  · intro s hs
    exact t_integral_nonneg hd hr ⟨le_of_lt hs.1, hs.2⟩
  · exact row_q4_s_intervalIntegrable
  · intro s hs
    have ho := sectionSixFirstLowCentralSmallI5P1D871_p0Row_endpoint_order i
    exact sectionSixFirstLowCentralSmallI5P1D873_p0Row_tFiber_le
      (hD0a := ho.1) (hab := ho.2.1) (hbDs := ho.2.2) hd hr
      ⟨le_of_lt hs.1, hs.2⟩

private theorem row_inner_le_primitive {i : Fin 256} {d r : Real}
    (hd : d ∈ Set.Icc
      (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i)
      (sectionSixFirstLowCentralSmallI5P1D871P0RowUpper i))
    (hr : r ∈ Set.Icc 0 (H d)) :
    (∫ s in (0 : Real)..r,
      ∫ t in G..(d - G), K (((d, r), s), t)) ≤
      sectionSixFirstLowCentralSmallI5P1D875P0RowFactor i * Q4
        (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i) r * Prim
        (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i) r := by
  calc
    (∫ s in (0 : Real)..r,
      ∫ t in G..(d - G), K (((d, r), s), t)) ≤
      ∫ s in (0 : Real)..r,
        sectionSixFirstLowCentralSmallI5P1D875P0RowFactor i * Q4
          (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i) r * Q4
          (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i) s :=
      row_inner_le hd hr
    _ = sectionSixFirstLowCentralSmallI5P1D875P0RowFactor i * Q4
          (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i) r * Prim
          (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i) r := by
      rw [intervalIntegral.integral_const_mul]
      rw [q4_inner_eq_primitive (ne_of_gt (row_lower_pos i))]

private theorem row_s_integral_nonneg {i : Fin 256} {d r : Real}
    (hd : d ∈ Set.Icc
      (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i)
      (sectionSixFirstLowCentralSmallI5P1D871P0RowUpper i))
    (hr : r ∈ Set.Icc 0 (H d)) :
    0 ≤ (∫ s in (0 : Real)..r,
      ∫ t in G..(d - G), K (((d, r), s), t)) := by
  apply intervalIntegral.integral_nonneg hr.1
  intro s hs
  exact t_integral_nonneg hd hr ⟨hs.1, hs.2⟩

private theorem row_rhs_r_intervalIntegrable {i : Fin 256} {d : Real} :
    IntervalIntegrable
      (fun r : Real => sectionSixFirstLowCentralSmallI5P1D875P0RowFactor i * Q4
        (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i) r * Prim
        (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i) r)
      volume 0 (H d) := by
  have hq := sectionSixFirstLowCentralSmallI5P1D816_q4_continuous
    (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i)
  have hp : Continuous (Prim
      (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i)) := by
    unfold Prim sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive
      sectionSixFirstLowCentralSmallI5P1D814Q4Primitive
    fun_prop
  exact ((continuous_const.mul (hq.comp continuous_id)).mul
    (hp.comp continuous_id)).intervalIntegrable _ _

private theorem row_fiber_le_majorant {i : Fin 256} {d : Real}
    (hd : d ∈ Set.Icc
      (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i)
      (sectionSixFirstLowCentralSmallI5P1D871P0RowUpper i)) :
    sectionSixFirstLowCentralSmallI5P1D874P0RowFiber i d ≤
      sectionSixFirstLowCentralSmallI5P1D875P0RowMajorant i d := by
  have hH := row_h_nonneg hd
  have houter := interval_integral_mono_of_nonneg_left hH
    (fun r hr => row_s_integral_nonneg hd ⟨le_of_lt hr.1, hr.2⟩)
    (row_rhs_r_intervalIntegrable (i := i) (d := d))
    (fun r hr => row_inner_le_primitive hd ⟨le_of_lt hr.1, hr.2⟩)
  calc
    sectionSixFirstLowCentralSmallI5P1D874P0RowFiber i d =
        ∫ r in (0 : Real)..H d,
          ∫ s in (0 : Real)..r,
            ∫ t in G..(d - G), K (((d, r), s), t) := rfl
    _ ≤ ∫ r in (0 : Real)..H d,
        sectionSixFirstLowCentralSmallI5P1D875P0RowFactor i * Q4
          (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i) r * Prim
          (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i) r := houter
    _ = sectionSixFirstLowCentralSmallI5P1D875P0RowMajorant i d := by
      have htri := sectionSixFirstLowCentralSmallI5P1D816_triangular_q4
        (a := sectionSixFirstLowCentralSmallI5P1D871P0RowLower i)
        (H := H d) (ne_of_gt (row_lower_pos i))
      have htri' :
          (∫ r in (0 : Real)..H d,
            Q4 (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i) r *
              Prim (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i) r) =
            Prim (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i) (H d) ^ 2 / 2 := by
        calc
          (∫ r in (0 : Real)..H d,
              Q4 (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i) r *
                Prim (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i) r) =
              ∫ r in (0 : Real)..H d,
                Q4 (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i) r *
                  (∫ s in (0 : Real)..r,
                    Q4 (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i) s) := by
            apply intervalIntegral.integral_congr
            intro r hr
            change Q4 (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i) r *
              Prim (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i) r =
              Q4 (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i) r *
                (∫ s in (0 : Real)..r,
                  Q4 (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i) s)
            rw [q4_inner_eq_primitive (ne_of_gt (row_lower_pos i))]
          _ = Prim (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i) (H d) ^ 2 / 2 := htri
      unfold sectionSixFirstLowCentralSmallI5P1D875P0RowMajorant
      rw [show (fun r : Real => sectionSixFirstLowCentralSmallI5P1D875P0RowFactor i * Q4
          (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i) r * Prim
          (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i) r) =
          (fun r => sectionSixFirstLowCentralSmallI5P1D875P0RowFactor i * (Q4
            (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i) r * Prim
            (sectionSixFirstLowCentralSmallI5P1D871P0RowLower i) r)) by
            funext r; ring]
      rw [intervalIntegral.integral_const_mul, htri']
      ring

private theorem row_majorant_continuous (i : Fin 256) :
    Continuous (sectionSixFirstLowCentralSmallI5P1D875P0RowMajorant i) := by
  unfold sectionSixFirstLowCentralSmallI5P1D875P0RowMajorant sectionSixFirstLowCentralSmallI5P1D875P0RowFactor Prim
    sectionSixFirstLowCentralSmallI5P1D816Row0Q4Primitive
    sectionSixFirstLowCentralSmallI5P1D814Q4Primitive H
    sectionSixFirstLowCentralSmallI5P1D807H
  fun_prop

theorem sectionSixFirstLowCentralSmallI5P1D875_p0Row_setIntegral_le_majorant (i : Fin 256) :
    (∫ z in sectionSixFirstLowCentralSmallI5P1D871P0RowSet i,
      sectionSixFirstLowCentralSmallI5P1D809Kernel z
      ∂(volume : Measure SectionSixP1AffineT)) ≤
      ∫ d in sectionSixFirstLowCentralSmallI5P1D871P0RowLower i..
        sectionSixFirstLowCentralSmallI5P1D871P0RowUpper i,
        sectionSixFirstLowCentralSmallI5P1D875P0RowMajorant i d := by
  rw [sectionSixFirstLowCentralSmallI5P1D874_p0Row_hIter i]
  have ho := sectionSixFirstLowCentralSmallI5P1D871_p0Row_endpoint_order i
  apply intervalIntegral.integral_mono_on ho.2.1
    (sectionSixFirstLowCentralSmallI5P1D874_p0Row_hFiberInt i)
    ((row_majorant_continuous i).intervalIntegrable _ _)
  intro d hd
  exact row_fiber_le_majorant hd


end
end PrimesRestrictedDigits
