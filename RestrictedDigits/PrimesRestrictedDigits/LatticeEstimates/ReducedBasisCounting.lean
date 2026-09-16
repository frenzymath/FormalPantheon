import PrimesRestrictedDigits.BasicEstimates.IntegerVectors
import PrimesRestrictedDigits.BasicEstimates.Lattices
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact counting constants for the rank-two lattice argument

These replace the hidden counting constants in `MAYNARD-PRD-PUBLISHED`, Lemma 14.1, pp.
199--200.
-/

noncomputable section

open scoped BigOperators

namespace PrimesRestrictedDigits

private theorem two_mul_ceil_add_one_le_five_mul
    {x : Real} (hx : 1 <= x) :
    (2 * (Nat.ceil x : Real) + 1) <= 5 * x := by
  have hx0 : 0 <= x := zero_le_one.trans hx
  have hceil : (Nat.ceil x : Real) <= 2 * x := by
    exact (Nat.ceil_lt_add_one hx0).le.trans (by linarith)
  linarith

/-- A rank-two integral basis coordinate box, with every basis norm at most
`B`, has cardinality times norm product at most `25*B^2`. -/
theorem card_mul_basis_norms_le
    {M : Type*} [AddCommGroup M] [Module Int M]
    (b : Module.Basis (Fin 2) Int M) (s : Finset M)
    (V : Fin 2 -> Real) (B : Real)
    (hV : forall i, 0 < V i) (hVB : forall i, V i <= B)
    (hs : forall x, x ∈ s -> forall i,
      ((|b.repr x i| : Int) : Real) * V i <= B) :
    (s.card : Real) * (V 0 * V 1) <= 25 * B ^ 2 := by
  let R : Fin 2 -> Nat := fun i => Nat.ceil (B / V i)
  have hRatio : forall i, 1 <= B / V i := by
    intro i
    exact (le_div_iff₀ (hV i)).2 (by simpa using hVB i)
  have hrepr : forall x, x ∈ s -> forall i,
      |b.repr x i| <= (R i : Int) := by
    intro x hx i
    have hcast : (((|b.repr x i| : Int) : Real)) <= B / V i :=
      (le_div_iff₀ (hV i)).2 (hs x hx i)
    have hceil : B / V i <= (R i : Real) :=
      Nat.le_ceil (B / V i)
    exact_mod_cast hcast.trans hceil
  have hcardNat : s.card <= ∏ i, (2 * R i + 1) :=
    card_le_prod_two_mul_add_one_of_basis_repr_le b R s hrepr
  have hcard : (s.card : Real) <=
      (2 * R 0 + 1 : Nat) * (2 * R 1 + 1 : Nat) := by
    exact_mod_cast (hcardNat.trans_eq (Fin.prod_univ_two _))
  have hfactor : forall i, ((2 * R i + 1 : Nat) : Real) <=
      5 * (B / V i) := by
    intro i
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
    exact two_mul_ceil_add_one_le_five_mul (hRatio i)
  have hproduct : (s.card : Real) <=
      (5 * (B / V 0)) * (5 * (B / V 1)) := by
    calc
      (s.card : Real) <=
          ((2 * R 0 + 1 : Nat) : Real) *
            ((2 * R 1 + 1 : Nat) : Real) := hcard
      _ <= (5 * (B / V 0)) * (5 * (B / V 1)) := by
        exact mul_le_mul (hfactor 0) (hfactor 1)
          (Nat.cast_nonneg _)
          (mul_nonneg (by norm_num) (zero_le_one.trans (hRatio 0)))
  calc
    (s.card : Real) * (V 0 * V 1) <=
        ((5 * (B / V 0)) * (5 * (B / V 1))) *
          (V 0 * V 1) := by
      exact mul_le_mul_of_nonneg_right hproduct
        (mul_nonneg (hV 0).le (hV 1).le)
    _ = 25 * B ^ 2 := by
      field_simp [(hV 0).ne', (hV 1).ne']
      ring

/-- The specialization used after the constant-three reduced-basis bound. -/
theorem card_mul_basis_norms_le_nine_hundred
    {M : Type*} [AddCommGroup M] [Module Int M]
    (b : Module.Basis (Fin 2) Int M) (s : Finset M)
    (V : Fin 2 -> Real) (N : Real)
    (hV : forall i, 0 < V i) (hVN : forall i, V i <= 6 * N)
    (hs : forall x, x ∈ s -> forall i,
      ((|b.repr x i| : Int) : Real) * V i <= 6 * N) :
    (s.card : Real) * (V 0 * V 1) <= 900 * N ^ 2 := by
  convert card_mul_basis_norms_le b s V (6 * N) hV hVN hs using 1; ring

/-- The cube of integer triples with coordinate absolute value at most `R`. -/
def integerVectorCube (R : Nat) : Finset (Fin 3 -> Int) :=
  Fintype.piFinset fun _ => Finset.Icc (-(R : Int)) (R : Int)

@[simp] theorem card_integerVectorCube (R : Nat) :
    (integerVectorCube R).card = (2 * R + 1) ^ 3 := by
  rw [show (integerVectorCube R).card =
      ∏ _i : Fin 3, (Finset.Icc (-(R : Int)) (R : Int)).card by
    simp [integerVectorCube]]
  have hcard : (Finset.Icc (-(R : Int)) (R : Int)).card = 2 * R + 1 := by
    rw [Int.card_Icc]
    have hcast :
        (R : Int) + 1 - (-(R : Int)) = ((2 * R + 1 : Nat) : Int) := by
      push_cast
      ring
    rw [hcast, Int.toNat_natCast]
  rw [Fin.prod_univ_three, hcard]
  ring

/-- Any finite set of integer triples of Euclidean norm at most `N` has at
most `27*N^3` elements when `N>=1`. -/
theorem card_real_le_twenty_seven_mul_cube
    (s : Finset (Fin 3 -> Int)) (N : Real) (hN : 1 <= N)
    (hs : forall z, z ∈ s -> ‖intVectorToEuclidean z‖ <= N) :
    (s.card : Real) <= 27 * N ^ 3 := by
  have hcoordinate : forall z, z ∈ s -> forall i,
      |z i| <= (Nat.floor N : Int) := by
    intro z hz i
    have hi := PiLp.norm_apply_le (intVectorToEuclidean z) i
    have hiReal : |((z i : Int) : Real)| <= N := by
      simpa [Real.norm_eq_abs] using hi.trans (hs z hz)
    have habsReal : ((z i).natAbs : Real) <= N := by
      simpa [Nat.cast_natAbs, Int.cast_abs] using hiReal
    have hfloor : (z i).natAbs <= Nat.floor N := Nat.le_floor habsReal
    have hfloorInt : ((z i).natAbs : Int) <= (Nat.floor N : Int) := by
      exact_mod_cast hfloor
    simpa [Int.natCast_natAbs] using hfloorInt
  have himage : s ⊆ integerVectorCube (Nat.floor N) := by
    intro z hz
    rw [integerVectorCube, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    simpa [abs_le] using hcoordinate z hz i
  have hcardNat : s.card <= (2 * Nat.floor N + 1) ^ 3 := by
    calc
      s.card <= (integerVectorCube (Nat.floor N)).card :=
        Finset.card_le_card himage
      _ = (2 * Nat.floor N + 1) ^ 3 := card_integerVectorCube _
  have hcard : (s.card : Real) <= (2 * Nat.floor N + 1 : Nat) ^ 3 := by
    exact_mod_cast hcardNat
  have hfloor : (Nat.floor N : Real) <= N := Nat.floor_le (by positivity)
  have hside : ((2 * Nat.floor N + 1 : Nat) : Real) <= 3 * N := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
    linarith
  calc
    (s.card : Real) <= (((2 * Nat.floor N + 1 : Nat) : Real) ^ 3) := hcard
    _ <= (3 * N) ^ 3 := by gcongr
    _ = 27 * N ^ 3 := by ring

end PrimesRestrictedDigits
