import PrimesRestrictedDigits.ExceptionalMinorArcs.FactorTenLocalization
import PrimesRestrictedDigits.LatticeEstimates.HybridSums
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Decimal scales for the Lemma 14.3 decomposition

This reuses the exact factor-ten selector from the line estimates and adds the deterministic
positive-real error scale required by the five-dimensional cover in `MAYNARD-PRD-PUBLISHED`,
Lemma 14.3.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- The canonical natural factor-ten scale gives membership in the lattice
module's exact natural decade band. -/
theorem mem_latticeFactorTenBand_factorTenScale
    {n : Nat} (hn : 0 < n) :
    n ∈ latticeFactorTenBand (factorTenScale n) := by
  rw [mem_latticeFactorTenBand_iff]
  have hband := factorTenScale_band n hn
  have hlower : factorTenScale n < 10 * n := by
    have hlowerReal : (factorTenScale n : Real) < 10 * n := by
      nlinarith [hband.1]
    exact_mod_cast hlowerReal
  exact ⟨hn, by exact_mod_cast hband.2, hlower⟩

/-- The canonical scale is strictly less than ten times its positive input. -/
theorem factorTenScale_lt_ten_mul {n : Nat} (hn : 0 < n) :
    factorTenScale n < 10 * n :=
  (mem_latticeFactorTenBand_iff.mp
    (mem_latticeFactorTenBand_factorTenScale hn)).2.2

/-- A natural bounded by `10^k` has canonical decimal index at most `k`. -/
theorem factorTenIndex_le_of_le_ten_pow {n k : Nat} (hn : n <= 10 ^ k) :
    factorTenIndex n <= k := by
  exact (Nat.clog_le_iff_le_pow (by norm_num)).2 hn

/-- Multiplying five canonical upper scales loses strictly less than `10^5`. -/
theorem factorTenScale_five_product_lt
    {n1 n2 n3 n4 n5 : Nat}
    (h1 : 0 < n1) (h2 : 0 < n2) (h3 : 0 < n3)
    (h4 : 0 < n4) (h5 : 0 < n5) :
    factorTenScale n1 * factorTenScale n2 * factorTenScale n3 *
        factorTenScale n4 * factorTenScale n5 <
      100000 * (n1 * n2 * n3 * n4 * n5) := by
  have hs1 := factorTenScale_lt_ten_mul h1
  have hs2 := factorTenScale_lt_ten_mul h2
  have hs3 := factorTenScale_lt_ten_mul h3
  have hs4 := factorTenScale_lt_ten_mul h4
  have hs5 := factorTenScale_lt_ten_mul h5
  calc
    factorTenScale n1 * factorTenScale n2 * factorTenScale n3 *
        factorTenScale n4 * factorTenScale n5 <
      (10 * n1) * (10 * n2) * (10 * n3) * (10 * n4) * (10 * n5) := by
        gcongr
    _ = 100000 * (n1 * n2 * n3 * n4 * n5) := by ring

/-- The decimal exponent of the least power of ten above a positive real. -/
noncomputable def latticePositiveRealFactorTenExponent (T : Real) : Nat :=
  factorTenIndex (Nat.ceil T)

/-- The least power of ten above a positive real target. -/
noncomputable def latticePositiveRealFactorTenScale (T : Real) : Nat :=
  10 ^ latticePositiveRealFactorTenExponent T

/-- If `1<T`, the selected error scale lies in the exact interval
`[T,10*T)`. The strict upper bound uses `Nat.lt_ceil`, avoiding an extra
factor two from the coarse estimate `ceil T<T+1`. -/
theorem latticePositiveRealFactorTenScale_bounds
    {T : Real} (hT : 1 < T) :
    T <= (latticePositiveRealFactorTenScale T : Real) ∧
      (latticePositiveRealFactorTenScale T : Real) < 10 * T := by
  have hceilTwo : 1 < Nat.ceil T :=
    (Nat.lt_ceil (n := 1)).2 (by simpa only [Nat.cast_one] using hT)
  have hceilPos : 0 < Nat.ceil T := Nat.zero_lt_one.trans hceilTwo
  have hscaleMem := mem_latticeFactorTenBand_factorTenScale hceilPos
  have hscaleData := mem_latticeFactorTenBand_iff.mp hscaleMem
  have hlower : T <= (latticePositiveRealFactorTenScale T : Real) := by
    calc
      T <= (Nat.ceil T : Real) := Nat.le_ceil T
      _ <= (latticePositiveRealFactorTenScale T : Real) := by
        exact_mod_cast hscaleData.2.1
  have hePos : 0 < Nat.clog 10 (Nat.ceil T) :=
    Nat.clog_pos (by norm_num) hceilTwo
  have he : Nat.clog 10 (Nat.ceil T) =
      (Nat.clog 10 (Nat.ceil T)).pred + 1 := by
    simpa only [Nat.succ_eq_add_one] using
      (Nat.succ_pred_eq_of_pos hePos).symm
  have hpredNat : 10 ^ (Nat.clog 10 (Nat.ceil T)).pred < Nat.ceil T :=
    Nat.pow_pred_clog_lt_self (by norm_num) hceilTwo
  have hpredReal :
      ((10 ^ (Nat.clog 10 (Nat.ceil T)).pred : Nat) : Real) < T :=
    (Nat.lt_ceil (n := 10 ^ (Nat.clog 10 (Nat.ceil T)).pred)).1 hpredNat
  have hscaleNat : latticePositiveRealFactorTenScale T =
      10 ^ (Nat.clog 10 (Nat.ceil T)).pred * 10 := by
    calc
      latticePositiveRealFactorTenScale T = 10 ^ Nat.clog 10 (Nat.ceil T) := rfl
      _ = 10 ^ ((Nat.clog 10 (Nat.ceil T)).pred + 1) :=
        congrArg (10 ^ ·) he
      _ = 10 ^ (Nat.clog 10 (Nat.ceil T)).pred * 10 := by rw [pow_succ]
  refine ⟨hlower, ?_⟩
  calc
    (latticePositiveRealFactorTenScale T : Real) =
        ((10 ^ (Nat.clog 10 (Nat.ceil T)).pred : Nat) : Real) * 10 := by
      exact_mod_cast hscaleNat
    _ < T * 10 := by gcongr
    _ = 10 * T := by ring

/-- A real target below `10^k` has selected exponent at most `k`. -/
theorem latticePositiveRealFactorTenExponent_le
    {T : Real} {k : Nat} (hupper : T <= (10 ^ k : Nat)) :
    latticePositiveRealFactorTenExponent T <= k := by
  apply factorTenIndex_le_of_le_ten_pow
  apply (Nat.ceil_le).2
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using hupper

end

end PrimesRestrictedDigits
