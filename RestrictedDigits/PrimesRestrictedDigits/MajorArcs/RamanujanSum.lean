import PrimesRestrictedDigits.MajorArcs.ResiduePhaseSum
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Ramanujan sums on reduced residues

This proves independently the signed Ramanujan-sum evaluation used in the M3
calculation on published p. 188.
-/

open scoped BigOperators ArithmeticFunction.Moebius
open Polynomial Finset

noncomputable section

namespace PrimesRestrictedDigits

/-- The signed complete phase sum over reduced residues modulo `q`. -/
noncomputable def majorArcRamanujanSum (q : Nat) (b : Int) : Complex :=
  ∑ r ∈ majorArcReducedResidues q,
    majorArcPhase ((b : Real) * (r : Real) / (q : Real))

private lemma image_stdAddChar_eq_nthRootsFinset (q : Nat) [NeZero q] :
    Finset.univ.image (fun a : ZMod q => ZMod.stdAddChar a) =
      nthRootsFinset q (1 : Complex) := by
  have hsubset :
      Finset.univ.image (fun a : ZMod q => ZMod.stdAddChar a) ⊆
        nthRootsFinset q (1 : Complex) := by
    intro xi hxi
    rw [Finset.mem_image] at hxi
    rcases hxi with ⟨a, _, rfl⟩
    rw [Polynomial.mem_nthRootsFinset (NeZero.pos q)]
    rw [← AddChar.map_nsmul_eq_pow]
    simp
  apply Finset.eq_of_subset_of_card_le hsubset
  have hprimitive := Complex.isPrimitiveRoot_exp q (NeZero.ne q)
  rw [hprimitive.card_nthRootsFinset]
  rw [Finset.card_image_of_injective _ ZMod.injective_stdAddChar]
  exact (ZMod.card q).ge

private lemma sum_stdAddChar_eq_ite (q : Nat) [NeZero q] :
    ∑ a : ZMod q, ZMod.stdAddChar a = if q = 1 then 1 else 0 := by
  by_cases hq : q = 1
  · subst q
    rw [if_pos rfl, Fintype.sum_unique]
    have hdefault : (default : ZMod 1) = 0 := Subsingleton.elim _ _
    calc
      ZMod.stdAddChar default = ZMod.stdAddChar 0 := congrArg _ hdefault
      _ = 1 := AddChar.map_zero_eq_one _
  · rw [if_neg hq, AddChar.sum_eq_ite]
    rw [if_neg]
    intro hzero
    letI : Nontrivial (ZMod q) := ZMod.nontrivial_iff.mpr hq
    have honezero : (1 : ZMod q) = 0 := by
      apply ZMod.injective_stdAddChar
      rw [hzero]
      simp
    exact one_ne_zero honezero

private lemma sum_nthRootsFinset_eq_ite (q : Nat) [NeZero q] :
    ∑ xi ∈ nthRootsFinset q (1 : Complex), xi =
      if q = 1 then 1 else 0 := by
  calc
    _ = ∑ xi ∈ Finset.univ.image (fun a : ZMod q => ZMod.stdAddChar a),
        xi := by
      rw [image_stdAddChar_eq_nthRootsFinset q]
    _ = ∑ a : ZMod q, ZMod.stdAddChar a := by
      rw [Finset.sum_image (ZMod.injective_stdAddChar.injOn)]
    _ = if q = 1 then 1 else 0 := sum_stdAddChar_eq_ite q

private lemma sum_primitiveRoots_eq_moebius (n : Nat) :
    ∑ zeta ∈ primitiveRoots n Complex, zeta =
      (ArithmeticFunction.moebius n : Complex) := by
  let F : ArithmeticFunction Complex :=
    ⟨fun m => ∑ zeta ∈ primitiveRoots m Complex, zeta, by simp⟩
  have hzetaF : (ArithmeticFunction.zeta : ArithmeticFunction Complex) * F =
      1 := by
    ext m
    rcases m.eq_zero_or_pos with rfl | hm
    · simp [F]
    · rw [ArithmeticFunction.coe_zeta_mul_apply,
        ArithmeticFunction.one_apply]
      change (∑ d ∈ m.divisors,
          ∑ zeta ∈ primitiveRoots d Complex, zeta) =
        if m = 1 then 1 else 0
      have hdisjoint :
          Set.PairwiseDisjoint (↑m.divisors)
            (fun d => primitiveRoots d Complex) := by
        intro d _ e _ hde
        exact IsPrimitiveRoot.disjoint hde
      rw [← Finset.sum_biUnion hdisjoint]
      rw [← IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots]
      letI : NeZero m := ⟨hm.ne'⟩
      exact sum_nthRootsFinset_eq_ite m
  have hF : F = (ArithmeticFunction.moebius : ArithmeticFunction Complex) := by
    calc
      F = 1 * F := (one_mul F).symm
      _ = ((ArithmeticFunction.moebius : ArithmeticFunction Complex) *
          (ArithmeticFunction.zeta : ArithmeticFunction Complex)) * F := by
        rw [ArithmeticFunction.coe_moebius_mul_coe_zeta]
      _ = (ArithmeticFunction.moebius : ArithmeticFunction Complex) *
          ((ArithmeticFunction.zeta : ArithmeticFunction Complex) * F) := by
        rw [mul_assoc]
      _ = (ArithmeticFunction.moebius : ArithmeticFunction Complex) := by
        rw [hzetaF, mul_one]
  have hvalue := congrArg (fun f : ArithmeticFunction Complex => f n) hF
  simpa [F] using hvalue

private lemma image_units_stdAddChar (q : Nat) [NeZero q] :
    (Finset.univ.filter (fun a : ZMod q => IsUnit a)).image
        (fun a => ZMod.stdAddChar a) = primitiveRoots q Complex := by
  ext xi
  rw [Finset.mem_image]
  rw [mem_primitiveRoots (NeZero.pos q)]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [Finset.mem_filter] at ha
    have hacast : IsUnit (a.val : ZMod q) := by
      simpa only [ZMod.natCast_zmod_val] using ha.2
    have hacoprime : Nat.Coprime a.val q :=
      (ZMod.isUnit_iff_coprime a.val q).mp hacast
    rw [← ZMod.natCast_zmod_val a]
    have hchar :
        ZMod.stdAddChar (a.val : ZMod q) =
          Complex.exp
            (2 * Real.pi * Complex.I * (a.val : Complex) / (q : Complex)) := by
      simpa only [Int.cast_natCast] using
        (ZMod.stdAddChar_coe (N := q) (a.val : Int))
    rw [hchar]
    apply (Complex.isPrimitiveRoot_iff _ q (NeZero.ne q)).mpr
    refine ⟨a.val, a.val_lt, hacoprime, ?_⟩
    congr 1
    ring
  · intro hxi
    rcases (Complex.isPrimitiveRoot_iff xi q (NeZero.ne q)).mp hxi with
      ⟨i, hi, hicoprime, hxiEq⟩
    refine ⟨(i : ZMod q), ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _,
        (ZMod.isUnit_iff_coprime i q).mpr hicoprime⟩
    · have hchar :
          ZMod.stdAddChar (i : ZMod q) =
            Complex.exp
              (2 * Real.pi * Complex.I * (i : Complex) / (q : Complex)) := by
        simpa only [Int.cast_natCast] using
          (ZMod.stdAddChar_coe (N := q) (i : Int))
      rw [hchar, ← hxiEq]
      congr 1
      ring

private lemma sum_zmodUnits_stdAddChar_eq_moebius
    (q : Nat) [NeZero q] :
    ∑ a ∈ Finset.univ.filter (fun a : ZMod q => IsUnit a),
        ZMod.stdAddChar a = (ArithmeticFunction.moebius q : Complex) := by
  calc
    _ = ∑ xi ∈
        (Finset.univ.filter (fun a : ZMod q => IsUnit a)).image
          (fun a => ZMod.stdAddChar a), xi := by
      rw [Finset.sum_image (ZMod.injective_stdAddChar.injOn)]
    _ = ∑ xi ∈ primitiveRoots q Complex, xi := by
      rw [image_units_stdAddChar q]
    _ = (ArithmeticFunction.moebius q : Complex) :=
      sum_primitiveRoots_eq_moebius q

private lemma sum_units_stdAddChar_mul_left
    (q : Nat) [NeZero q] (z : ZMod q) (hz : IsUnit z) :
    ∑ a ∈ Finset.univ.filter (fun a : ZMod q => IsUnit a),
        ZMod.stdAddChar (z * a) =
      ∑ a ∈ Finset.univ.filter (fun a : ZMod q => IsUnit a),
        ZMod.stdAddChar a := by
  let u : (ZMod q)ˣ := hz.unit
  have hu : (u : ZMod q) = z := hz.unit_spec
  rw [← hu]
  refine Finset.sum_equiv u.mulLeft ?_ ?_
  · intro a
    rw [Finset.mem_filter, Finset.mem_filter]
    constructor
    · intro ha
      exact ⟨Finset.mem_univ _, u.isUnit.mul ha.2⟩
    · intro ha
      exact ⟨Finset.mem_univ _, (IsUnit.mul_iff.mp ha.2).2⟩
  · intro a _
    rfl

private lemma intCast_isUnit_of_natAbs_coprime
    {q : Nat} (z : Int) (hz : Nat.Coprime z.natAbs q) :
    IsUnit (z : ZMod q) := by
  rcases Int.natAbs_eq z with hzpos | hzneg
  · rw [hzpos]
    simpa only [Int.cast_natCast] using
      (ZMod.isUnit_iff_coprime z.natAbs q).mpr hz
  · rw [hzneg]
    have hcast : (((-(z.natAbs : Int) : Int)) : ZMod q) =
        -(z.natAbs : ZMod q) := by
      norm_num
    rw [hcast]
    exact ((ZMod.isUnit_iff_coprime z.natAbs q).mpr hz).neg

private lemma sum_reducedResidues_eq_sum_zmodUnits
    (q : Nat) [NeZero q] (z : Int) :
    ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
        ZMod.stdAddChar ((z * (r : Int) : Int) : ZMod q) =
      ∑ a ∈ Finset.univ.filter (fun a : ZMod q => IsUnit a),
        ZMod.stdAddChar ((z : ZMod q) * a) := by
  refine Finset.sum_bij (fun r _ => (r : ZMod q)) ?_ ?_ ?_ ?_
  · intro r hr
    rw [Finset.mem_filter] at hr ⊢
    exact ⟨Finset.mem_univ _,
      (ZMod.isUnit_iff_coprime r q).mpr hr.2⟩
  · intro r hr s hs hrs
    rw [Finset.mem_filter] at hr hs
    have hval := congrArg ZMod.val hrs
    rw [ZMod.val_natCast_of_lt (Finset.mem_range.mp hr.1),
      ZMod.val_natCast_of_lt (Finset.mem_range.mp hs.1)] at hval
    exact hval
  · intro a ha
    rw [Finset.mem_filter] at ha
    have hacast : IsUnit (a.val : ZMod q) := by
      simpa only [ZMod.natCast_zmod_val] using ha.2
    refine ⟨a.val, ?_, ZMod.natCast_zmod_val a⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_range.mpr a.val_lt,
      (ZMod.isUnit_iff_coprime a.val q).mp hacast⟩
  · intro r _
    congr 1
    push_cast
    rfl

private theorem reducedResidueExponentialSum_eq_moebius
    (q : Nat) (hq : 0 < q) (z : Int)
    (hz : Nat.Coprime z.natAbs q) :
    ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
        Complex.exp (2 * (Real.pi : Complex) * Complex.I *
          ((z * (r : Int) : Int) : Complex) / (q : Complex)) =
      (ArithmeticFunction.moebius q : Complex) := by
  letI : NeZero q := ⟨hq.ne'⟩
  calc
    _ = ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
          ZMod.stdAddChar ((z * (r : Int) : Int) : ZMod q) := by
      apply Finset.sum_congr rfl
      intro r _
      exact (ZMod.stdAddChar_coe (N := q) (z * (r : Int))).symm
    _ = ∑ a ∈ Finset.univ.filter (fun a : ZMod q => IsUnit a),
          ZMod.stdAddChar ((z : ZMod q) * a) :=
      sum_reducedResidues_eq_sum_zmodUnits q z
    _ = ∑ a ∈ Finset.univ.filter (fun a : ZMod q => IsUnit a),
          ZMod.stdAddChar a :=
      sum_units_stdAddChar_mul_left q (z : ZMod q)
        (intCast_isUnit_of_natAbs_coprime z hz)
    _ = (ArithmeticFunction.moebius q : Complex) :=
      sum_zmodUnits_stdAddChar_eq_moebius q

/-- At a signed numerator coprime to a positive modulus, the Ramanujan sum is
the Moebius value of that modulus. -/
theorem majorArcRamanujanSum_eq_moebius
    {q : Nat} (hq : 0 < q) {b : Int}
    (hb : Nat.Coprime b.natAbs q) :
    majorArcRamanujanSum q b =
      ((ArithmeticFunction.moebius q : Int) : Complex) := by
  rw [majorArcRamanujanSum, majorArcReducedResidues]
  calc
    _ = ∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
          Complex.exp (2 * (Real.pi : Complex) * Complex.I *
            ((b * (r : Int) : Int) : Complex) / (q : Complex)) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [majorArcPhase]
      congr 1
      push_cast
      ring
    _ = ((ArithmeticFunction.moebius q : Int) : Complex) :=
      reducedResidueExponentialSum_eq_moebius q hq b hb

end PrimesRestrictedDigits
