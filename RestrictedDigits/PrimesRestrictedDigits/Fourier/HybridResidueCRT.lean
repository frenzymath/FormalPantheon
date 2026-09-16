import PrimesRestrictedDigits.Fourier.RationalCircleSpacing
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# CRT and mixed-radix carriers for the alternative hybrid bound

This file isolates the finite arithmetic in published Lemma 10.7 (pp. 180--
185).  The decimal factors are mixed-radix coordinates, not pairwise
coprime factors.  Reduced residues retain the zero residue at modulus one,
which is needed by the nonnegative source sums.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

/-! ## Mixed-radix coordinates -/

/-- A low digit followed by a high digit, with the low digit as the first
coordinate in the natural-number value. -/
def lowHighFinEquiv (m n : Nat) : Fin m × Fin n ≃ Fin (m * n) :=
  (Equiv.prodComm (Fin m) (Fin n)).trans <|
    (finProdFinEquiv (m := n) (n := m)).trans <|
      finCongr (Nat.mul_comm n m)

theorem lowHighFinEquiv_val (m n : Nat) (low : Fin m) (high : Fin n) :
    (lowHighFinEquiv m n (low, high)).val = low.val + m * high.val := by
  simp only [lowHighFinEquiv, Equiv.trans_apply, Equiv.prodComm_apply,
    finProdFinEquiv, finCongr_apply_coe]
  rfl

/-- The source's three decimal coordinates in low-radix order. -/
def mixedRadixTripleEquiv (d₁ d₂ d₃ : Nat) :
    (Fin d₁ × Fin d₂) × Fin d₃ ≃ Fin (d₁ * d₂ * d₃) :=
  ((lowHighFinEquiv d₁ d₂).prodCongr (Equiv.refl (Fin d₃))).trans
    (lowHighFinEquiv (d₁ * d₂) d₃)

theorem mixedRadixTripleEquiv_val (d₁ d₂ d₃ : Nat)
    (b₁ : Fin d₁) (b₂ : Fin d₂) (b₃ : Fin d₃) :
    (mixedRadixTripleEquiv d₁ d₂ d₃ ((b₁, b₂), b₃)).val =
      b₁.val + d₁ * b₂.val + d₁ * d₂ * b₃.val := by
  change (lowHighFinEquiv (d₁ * d₂) d₃
      (lowHighFinEquiv d₁ d₂ (b₁, b₂), b₃)).val = _
  rw [lowHighFinEquiv_val, lowHighFinEquiv_val]

theorem sum_mixedRadixTripleEquiv {M : Type*} [AddCommMonoid M]
    (d₁ d₂ d₃ : Nat) (f : Fin (d₁ * d₂ * d₃) → M) :
    (∑ x : (Fin d₁ × Fin d₂) × Fin d₃,
      f (mixedRadixTripleEquiv d₁ d₂ d₃ x)) = ∑ c, f c := by
  exact (mixedRadixTripleEquiv d₁ d₂ d₃).sum_comp f

/-! ## Zero-aware reduced residues -/

/-- Reduced residues represented by canonical `Fin` representatives. -/
def ReducedResidue (n : Nat) := {a : Fin n // a.val.Coprime n}

instance instFintypeReducedResidue (n : Nat) : Fintype (ReducedResidue n) := by
  dsimp [ReducedResidue]
  infer_instance

/-- The finite carrier used when a source sum is written over `Fin n`. -/
def reducedResidueCarrier (n : Nat) : Finset (Fin n) :=
  Finset.univ.filter (fun a => a.val.Coprime n)

theorem mem_reducedResidueCarrier_iff {n : Nat} {a : Fin n} :
    a ∈ reducedResidueCarrier n ↔ a.val.Coprime n := by
  simp [reducedResidueCarrier]

theorem zero_mem_reducedResidueCarrier_iff (n : Nat) (hn : 0 < n) :
    (⟨0, hn⟩ : Fin n) ∈ reducedResidueCarrier n ↔ n = 1 := by
  simp [reducedResidueCarrier, Nat.coprime_iff_gcd_eq_one]

private theorem coprime_of_modEq_left {z a n : Nat} (h : z ≡ a [MOD n])
    (ha : a.Coprime n) : z.Coprime n := by
  apply Nat.coprime_iff_gcd_eq_one.mpr
  calc
    z.gcd n = (z % n).gcd n := by
      rw [Nat.gcd_comm z n, Nat.gcd_rec]
    _ = (a % n).gcd n := by rw [h]
    _ = a.gcd n := by
      rw [← Nat.gcd_rec n a, Nat.gcd_comm]
    _ = 1 := ha.gcd_eq_one

/-! ## Chinese remaindering -/

def crtFinMap {n m : Nat} (hn : 0 < n) (hm : 0 < m) (hcop : n.Coprime m)
    (a : Fin n) (b : Fin m) : Fin (n * m) :=
  ⟨Nat.chineseRemainder hcop a.val b.val,
    Nat.chineseRemainder_lt_mul hcop a.val b.val hn.ne' hm.ne'⟩

def crtFinInv {n m : Nat} (hn : 0 < n) (hm : 0 < m)
    (x : Fin (n * m)) : Fin n × Fin m :=
  (⟨x.val % n, Nat.mod_lt _ hn⟩, ⟨x.val % m, Nat.mod_lt _ hm⟩)

theorem crtFinMap_inv {n m : Nat} (hn : 0 < n) (hm : 0 < m)
    (hcop : n.Coprime m) (a : Fin n) (b : Fin m) :
    crtFinInv hn hm (crtFinMap hn hm hcop a b) = (a, b) := by
  apply Prod.ext <;> apply Fin.ext
  · change (Nat.chineseRemainder hcop a.val b.val) % n = a.val
    have h := (Nat.chineseRemainder hcop a.val b.val).prop.1
    change (Nat.chineseRemainder hcop a.val b.val) % n = a.val % n at h
    exact h.trans (Nat.mod_eq_of_lt a.isLt)
  · change (Nat.chineseRemainder hcop a.val b.val) % m = b.val
    have h := (Nat.chineseRemainder hcop a.val b.val).prop.2
    change (Nat.chineseRemainder hcop a.val b.val) % m = b.val % m at h
    exact h.trans (Nat.mod_eq_of_lt b.isLt)

theorem crtFinMap_left_inv {n m : Nat} (hn : 0 < n) (hm : 0 < m)
    (hcop : n.Coprime m) (x : Fin (n * m)) :
    crtFinMap hn hm hcop (crtFinInv hn hm x).1 (crtFinInv hn hm x).2 = x := by
  apply Fin.ext
  exact (Nat.chineseRemainder_modEq_unique hcop
    (Nat.mod_modEq x.val n).symm (Nat.mod_modEq x.val m).symm).symm.eq_of_lt_of_lt
      (Nat.chineseRemainder_lt_mul hcop _ _ hn.ne' hm.ne') x.isLt

def crtFinEquiv {n m : Nat} (hn : 0 < n) (hm : 0 < m) (hcop : n.Coprime m) :
    Fin n × Fin m ≃ Fin (n * m) :=
  { toFun := fun x => crtFinMap hn hm hcop x.1 x.2
    invFun := crtFinInv hn hm
    left_inv := fun x => crtFinMap_inv hn hm hcop x.1 x.2
    right_inv := crtFinMap_left_inv hn hm hcop }

theorem crtFinEquiv_coprime_iff {n m : Nat} (hn : 0 < n) (hm : 0 < m)
    (hcop : n.Coprime m) (a : Fin n) (b : Fin m) :
    (crtFinEquiv hn hm hcop (a, b)).val.Coprime (n * m) ↔
      a.val.Coprime n ∧ b.val.Coprime m := by
  have hleft : (crtFinEquiv hn hm hcop (a, b)).val ≡ a.val [MOD n] := by
    simpa [crtFinEquiv, crtFinMap] using
      (Nat.chineseRemainder hcop a.val b.val).prop.1
  have hright : (crtFinEquiv hn hm hcop (a, b)).val ≡ b.val [MOD m] := by
    simpa [crtFinEquiv, crtFinMap] using
      (Nat.chineseRemainder hcop a.val b.val).prop.2
  rw [Nat.coprime_mul_iff_right]
  constructor
  · intro hz
    exact ⟨coprime_of_modEq_left hleft.symm hz.1,
      coprime_of_modEq_left hright.symm hz.2⟩
  · intro hab
    exact ⟨coprime_of_modEq_left hleft hab.1,
      coprime_of_modEq_left hright hab.2⟩

def reducedResidueCrtEquiv {n m : Nat} (hn : 0 < n) (hm : 0 < m)
    (hcop : n.Coprime m) :
    ReducedResidue n × ReducedResidue m ≃ ReducedResidue (n * m) :=
  (Equiv.subtypeProdEquivProd
      (p := fun a : Fin n => a.val.Coprime n)
      (q := fun b : Fin m => b.val.Coprime m)).symm.trans <|
    (crtFinEquiv hn hm hcop).subtypeEquiv (fun x =>
      (crtFinEquiv_coprime_iff hn hm hcop x.1 x.2).symm)

/-! ## Weighted source phases -/

def scaleFinMap {n k : Nat} (hn : 0 < n) (_hk : k.Coprime n) (a : Fin n) : Fin n :=
  ⟨(a.val * k) % n, Nat.mod_lt _ hn⟩

theorem scaleFinMap_injective {n k : Nat} (hn : 0 < n) (hk : k.Coprime n) :
    Function.Injective (scaleFinMap hn hk) := by
  intro a b hab
  apply Fin.ext
  have hmod : a.val * k ≡ b.val * k [MOD n] := by
    change (a.val * k) % n = (b.val * k) % n
    exact congrArg Fin.val hab
  have hcancel := hmod.cancel_right_of_coprime hk.symm.gcd_eq_one
  change a.val % n = b.val % n at hcancel
  simpa [Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] using hcancel

def scaleFinEquiv {n k : Nat} (hn : 0 < n) (hk : k.Coprime n) : Fin n ≃ Fin n :=
  Equiv.ofBijective (scaleFinMap hn hk)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨scaleFinMap_injective hn hk, rfl⟩)

def weightedCRTResidueEquiv {q d u v : Nat} (hq : 0 < q) (hd : 0 < d)
    (hu : (u * d).Coprime q) (hv : (v * q).Coprime d) :
    Fin q × Fin d ≃ Fin (q * d) :=
  ((scaleFinEquiv hq hu).prodCongr (scaleFinEquiv hd hv)).trans
    (crtFinEquiv hq hd ((hu.of_dvd_left (dvd_mul_left d u)).symm))

def weightedCRTResidue {q d u v : Nat} (hq : 0 < q) (hd : 0 < d)
    (hu : (u * d).Coprime q) (hv : (v * q).Coprime d)
    (a : Fin q) (b : Fin d) : Fin (q * d) :=
  weightedCRTResidueEquiv hq hd hu hv (a, b)

private theorem scaleFinMap_coprime_iff {n k : Nat} (hn : 0 < n)
    (hk : k.Coprime n) (a : Fin n) :
    (scaleFinMap hn hk a).val.Coprime n ↔ a.val.Coprime n := by
  constructor
  · intro h
    have hmul : (a.val * k).Coprime n := by
      apply coprime_of_modEq_left (Nat.mod_modEq (a.val * k) n).symm
      simpa [scaleFinMap] using h
    exact (Nat.coprime_mul_iff_left.mp hmul).1
  · intro h
    apply coprime_of_modEq_left (Nat.mod_modEq (a.val * k) n)
    simpa [scaleFinMap] using
      ((Nat.coprime_mul_iff_left).2 ⟨h, hk⟩)

theorem weightedCRTResidue_coprime_iff {q d u v : Nat}
    (hq : 0 < q) (hd : 0 < d)
    (hu : (u * d).Coprime q) (hv : (v * q).Coprime d)
    (a : Fin q) (b : Fin d) :
    (weightedCRTResidue hq hd hu hv a b).val.Coprime (q * d) ↔
      a.val.Coprime q ∧ b.val.Coprime d := by
  have hcrt := crtFinEquiv_coprime_iff hq hd
    ((hu.of_dvd_left (dvd_mul_left d u)).symm)
    (scaleFinMap hq hu a) (scaleFinMap hd hv b)
  simpa [weightedCRTResidue, weightedCRTResidueEquiv, Equiv.trans_apply,
    Equiv.prodCongr_apply, Prod.map, scaleFinEquiv] using
    (hcrt.trans (and_congr (scaleFinMap_coprime_iff hq hu a)
      (scaleFinMap_coprime_iff hd hv b)))

def weightedReducedResidueEquiv {q d u v : Nat}
    (hq : 0 < q) (hd : 0 < d)
    (hu : (u * d).Coprime q) (hv : (v * q).Coprime d) :
    ReducedResidue q × ReducedResidue d ≃ ReducedResidue (q * d) :=
  (Equiv.subtypeProdEquivProd
      (p := fun a : Fin q => a.val.Coprime q)
      (q := fun b : Fin d => b.val.Coprime d)).symm.trans <|
    (weightedCRTResidueEquiv hq hd hu hv).subtypeEquiv (fun x =>
      (weightedCRTResidue_coprime_iff hq hd hu hv x.1 x.2).symm)

theorem sum_weightedReducedResidueEquiv {M : Type*} [AddCommMonoid M]
    {q d u v : Nat} (hq : 0 < q) (hd : 0 < d)
    (hu : (u * d).Coprime q) (hv : (v * q).Coprime d)
    (f : ReducedResidue (q * d) → M) :
    (∑ x : ReducedResidue q × ReducedResidue d,
      f (weightedReducedResidueEquiv hq hd hu hv x)) =
      ∑ y, f y := by
  exact (weightedReducedResidueEquiv hq hd hu hv).sum_comp f

theorem weightedCRTResidue_val {q d u v : Nat} (hq : 0 < q) (hd : 0 < d)
    (hu : (u * d).Coprime q) (hv : (v * q).Coprime d) (a : Fin q) (b : Fin d) :
    (weightedCRTResidue hq hd hu hv a b).val =
      (u * a.val * d + v * b.val * q) % (q * d) := by
  let z := u * a.val * d + v * b.val * q
  have hleft0 : z ≡ a.val * (u * d) [MOD q] := by
    have hzero : v * b.val * q ≡ 0 [MOD q] := by
      apply Nat.modEq_zero_iff_dvd.mpr
      exact dvd_mul_left q (v * b.val)
    have hadd := (Nat.ModEq.refl (n := q) (a.val * (u * d))).add hzero
    convert hadd using 1
    all_goals simp [z, Nat.mul_comm, Nat.mul_left_comm]
  have hright0 : z ≡ b.val * (v * q) [MOD d] := by
    have hzero : u * a.val * d ≡ 0 [MOD d] := by
      apply Nat.modEq_zero_iff_dvd.mpr
      exact dvd_mul_left d (u * a.val)
    have hadd := hzero.add (Nat.ModEq.refl (n := d) (b.val * (v * q)))
    convert hadd using 1
    all_goals simp [z, Nat.mul_comm, Nat.mul_left_comm]
  have hleft : z ≡ (scaleFinMap hq hu a).val [MOD q] :=
    hleft0.trans (Nat.mod_modEq (a.val * (u * d)) q).symm
  have hright : z ≡ (scaleFinMap hd hv b).val [MOD d] :=
    hright0.trans (Nat.mod_modEq (b.val * (v * q)) d).symm
  have hcop : q.Coprime d := (hu.of_dvd_left (dvd_mul_left d u)).symm
  have huniq := Nat.chineseRemainder_modEq_unique hcop hleft hright
  have hmodEq :
      (Nat.chineseRemainder hcop (scaleFinMap hq hu a).val
          (scaleFinMap hd hv b).val : Nat) ≡ z % (q * d) [MOD q * d] :=
    huniq.symm.trans (Nat.mod_modEq z (q * d)).symm
  have hEq := hmodEq.eq_of_lt_of_lt
    (Nat.chineseRemainder_lt_mul hcop _ _ hq.ne' hd.ne')
    (Nat.mod_lt z (Nat.mul_pos hq hd))
  simpa [weightedCRTResidue, weightedCRTResidueEquiv, crtFinEquiv, crtFinMap,
    crtFinInv, scaleFinEquiv, scaleFinMap, z, Nat.ModEq,
    Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map] using hEq

private theorem unitAddCircle_natMod_div_eq {z M : Nat} (hM : 0 < M) :
    (((z % M : Nat) : Real) / (M : Real) : UnitAddCircle) =
      ((z : Real) / (M : Real) : UnitAddCircle) := by
  apply (QuotientAddGroup.eq_iff_sub_mem).2
  rw [AddSubgroup.mem_zmultiples_iff]
  refine ⟨-(z / M : Int), ?_⟩
  simp only [zsmul_eq_mul, mul_one, Int.cast_neg]
  change (-(z / M : Nat) : Real) =
    ((z % M : Nat) : Real) / (M : Real) - (z : Real) / (M : Real)
  have hdecomp := Nat.mod_add_div z M
  have hcast : (z : Real) = ((z % M : Nat) : Real) +
      (M : Real) * ((z / M : Nat) : Real) := by
    exact_mod_cast hdecomp.symm
  rw [hcast]
  field_simp [show (M : Real) ≠ 0 by exact_mod_cast hM.ne']
  ring

theorem weightedCRTResidue_unitAddCircle_eq {q d u v : Nat}
    (hq : 0 < q) (hd : 0 < d)
    (hu : (u * d).Coprime q) (hv : (v * q).Coprime d)
    (a : Fin q) (b : Fin d) :
    (((weightedCRTResidue hq hd hu hv a b).val : Real) /
        ((q * d : Nat) : Real) : UnitAddCircle) =
      (((u * a.val : Nat) : Real) / (q : Real) +
        ((v * b.val : Nat) : Real) / (d : Real) : UnitAddCircle) := by
  rw [weightedCRTResidue_val hq hd hu hv a b]
  let z := u * a.val * d + v * b.val * q
  calc
    ((((z % (q * d) : Nat) : Real) / ((q * d : Nat) : Real) : Real) :
        UnitAddCircle) =
        (((z : Real) / ((q * d : Nat) : Real) : Real) : UnitAddCircle) :=
      unitAddCircle_natMod_div_eq (Nat.mul_pos hq hd)
    _ = (((u * a.val : Nat) : Real) / (q : Real) +
        ((v * b.val : Nat) : Real) / (d : Real) : UnitAddCircle) := by
      congr 1
      dsimp [z]
      push_cast
      field_simp [show (q : Real) ≠ 0 by exact_mod_cast hq.ne',
        show (d : Real) ≠ 0 by exact_mod_cast hd.ne']

end
end PrimesRestrictedDigits
