import Waring.Analytic.WeilLocalEuler
import Waring.Analytic.WeilMonicFactors

/-!
# Coefficients of a finite Euler product

This file expands a finite product of geometric local Euler factors.  The
coefficient indices that survive are precisely the degree-weighted
multiplicity functions, hence (by unique factorization) the monic
polynomials of the requested degree.
-/

namespace Waring.Analytic

open Polynomial

namespace Weil

variable {K R : Type*} [Field K] [Fintype K] [CommRing R] {N n : Nat}

/-- Degree-weighted bounded irreducible multiplicities form a finite type. -/
noncomputable instance weightedFactorsFintype :
    Fintype
      {m : MonicIrreducibleLE K N →₀ Nat // monicFactorWeight m = n} := by
  classical
  exact (Finsupp.finite_of_nat_weight_eq
    (fun P : MonicIrreducibleLE K N ↦ P.poly.natDegree)
    (fun P ↦ P.natDegree_pos.ne') n).fintype

/-- The multiplicative weight attached to an irreducible multiplicity
function. -/
noncomputable def multiplicativeFactorWeight
    (w : MonicIrreducibleLE K N → R)
    (m : MonicIrreducibleLE K N →₀ Nat) : R :=
  ∏ P, w P ^ m P

/-- The finite product definition of `multiplicativeFactorWeight` is the
product over the multiplicity multiset. -/
theorem prod_map_toMultiset_eq_multiplicativeFactorWeight
    (w : MonicIrreducibleLE K N → R)
    (m : MonicIrreducibleLE K N →₀ Nat) :
    (m.toMultiset.map w).prod = multiplicativeFactorWeight w m := by
  rw [multiplicativeFactorWeight, ← Finsupp.prod_pow]
  induction m using Finsupp.induction with
  | zero => simp [Finsupp.toMultiset_zero]
  | @single_add P e f hP he ih =>
      rw [Finsupp.toMultiset_add, Multiset.map_add, Multiset.prod_add, ih]
      calc
        (Multiset.map w (Finsupp.toMultiset (Finsupp.single P e))).prod *
            f.prod (fun Q a ↦ w Q ^ a) =
            w P ^ e * f.prod (fun Q a ↦ w Q ^ a) := by
          rw [Finsupp.toMultiset_single, Multiset.map_nsmul,
            Multiset.map_singleton, Multiset.prod_nsmul,
            Multiset.prod_singleton]
        _ = (Finsupp.single P e).prod (fun Q a ↦ w Q ^ a) *
              f.prod (fun Q a ↦ w Q ^ a) := by
          rw [Finsupp.prod_single_index]
          exact pow_zero _
        _ = (Finsupp.single P e + f).prod (fun Q a ↦ w Q ^ a) := by
          symm
          exact Finsupp.prod_add_index' (fun _ ↦ pow_zero _)
            (fun _ _ _ ↦ pow_add _ _ _)

omit [Fintype K] in
/-- The formal-root weight of a product of monic polynomials is the product
of their formal-root weights. -/
theorem formalRootWeight_multiset_prod
    (character : AddChar K Complex) (b : Fin 5 → K)
    (s : Multiset K[X]) (hs : ∀ F ∈ s, F.Monic) :
    formalRootWeight character b s.prod =
      (s.map (formalRootWeight character b)).prod := by
  have hOne : formalRootWeight character b (1 : K[X]) = 1 := by
    rw [formalRootWeight]
    have hphase : formalRootPhase b (1 : K[X]) = 0 := by
      rw [formalRootPhase]
      apply Finset.sum_eq_zero
      intro i hi
      rw [formalRootPowerSum_one (Nat.succ_pos i.val)
        (Nat.succ_le_iff.mpr i.isLt), mul_zero]
    rw [hphase, character.map_zero_eq_one]
  induction s using Multiset.induction_on with
  | empty => simpa using hOne
  | cons F s ih =>
      have hF : F.Monic := hs F (Multiset.mem_cons_self F s)
      have hs' : ∀ G ∈ s, G.Monic := fun G hG ↦
        hs G (Multiset.mem_cons.mpr (Or.inr hG))
      have hsprod : s.prod.Monic := by
        simpa using Polynomial.monic_multiset_prod_of_monic s (fun G ↦ G) hs'
      rw [Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons,
        formalRootWeight_mul_of_monic character b hF hsprod, ih hs']

/-- Applying the formal-root weight to the polynomial represented by a
factor multiplicity gives its multiplicative factor weight. -/
theorem multiplicativeFactorWeight_formalRootWeight
    (character : AddChar K Complex) (b : Fin 5 → K)
    (m : MonicIrreducibleLE K N →₀ Nat) :
    multiplicativeFactorWeight
        (fun P ↦ formalRootWeight character b P.poly) m =
      formalRootWeight character b (monicFactorProduct m) := by
  let s : Multiset K[X] :=
    m.toMultiset.map MonicIrreducibleLE.poly
  have hs : ∀ F ∈ s, F.Monic := by
    intro F hF
    obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hF
    exact P.monic
  calc
    multiplicativeFactorWeight
        (fun P ↦ formalRootWeight character b P.poly) m =
        (m.toMultiset.map
          (fun P ↦ formalRootWeight character b P.poly)).prod :=
      (prod_map_toMultiset_eq_multiplicativeFactorWeight _ m).symm
    _ = (s.map (formalRootWeight character b)).prod := by
      simp only [s, Multiset.map_map, Function.comp_apply]
    _ = formalRootWeight character b s.prod :=
      (formalRootWeight_multiset_prod character b s hs).symm
    _ = formalRootWeight character b (monicFactorProduct m) := rfl

/-- Multiply every coordinate of a multiplicity function by its irreducible
degree.  These are the coefficient indices in the ordinary Cauchy product. -/
noncomputable def degreeScaledIndex
    (m : MonicIrreducibleLE K N →₀ Nat) :
    MonicIrreducibleLE K N →₀ Nat :=
  Finsupp.onFinset Finset.univ
    (fun P ↦ P.poly.natDegree * m P) (by simp)

/-- Evaluating the degree-scaled index recovers the degree-weighted coordinate. -/
@[simp]
theorem degreeScaledIndex_apply
    (m : MonicIrreducibleLE K N →₀ Nat)
    (P : MonicIrreducibleLE K N) :
    degreeScaledIndex m P = P.poly.natDegree * m P := by
  simp [degreeScaledIndex]

/-- Divide every coordinate by its irreducible degree.  On divisible
coefficient indices this inverts `degreeScaledIndex`. -/
noncomputable def degreeUnscaledIndex
    (l : MonicIrreducibleLE K N →₀ Nat) :
    MonicIrreducibleLE K N →₀ Nat :=
  Finsupp.onFinset Finset.univ
    (fun P ↦ l P / P.poly.natDegree) (by simp)

/-- Evaluating the degree-unscaled index divides by the irreducible degree. -/
@[simp]
theorem degreeUnscaledIndex_apply
    (l : MonicIrreducibleLE K N →₀ Nat)
    (P : MonicIrreducibleLE K N) :
    degreeUnscaledIndex l P = l P / P.poly.natDegree := by
  simp [degreeUnscaledIndex]

/-- Unscaling a degree-scaled multiplicity function recovers the original function. -/
theorem degreeUnscaledIndex_scaled
    (m : MonicIrreducibleLE K N →₀ Nat) :
    degreeUnscaledIndex (degreeScaledIndex m) = m := by
  ext P
  simp [Nat.mul_div_cancel_left _ P.natDegree_pos]

/-- Scaling a divisible index after unscaling recovers that index. -/
theorem degreeScaledIndex_unscaled
    (l : MonicIrreducibleLE K N →₀ Nat)
    (hl : ∀ P, P.poly.natDegree ∣ l P) :
    degreeScaledIndex (degreeUnscaledIndex l) = l := by
  ext P
  simp only [degreeScaledIndex_apply, degreeUnscaledIndex_apply]
  rw [mul_comm, Nat.div_mul_cancel (hl P)]

private theorem sum_degreeScaledIndex
    (m : MonicIrreducibleLE K N →₀ Nat) :
    ∑ P, degreeScaledIndex m P = monicFactorWeight m := by
  classical
  rw [monicFactorWeight, Finsupp.weight_apply,
    Finsupp.sum_fintype]
  · apply Finset.sum_congr rfl
    intro P hP
    simp [mul_comm]
  · intro P
    simp

private theorem weight_degreeUnscaledIndex
    (l : MonicIrreducibleLE K N →₀ Nat)
    (hl : ∀ P, P.poly.natDegree ∣ l P) :
    monicFactorWeight (degreeUnscaledIndex l) = ∑ P, l P := by
  classical
  rw [monicFactorWeight, Finsupp.weight_apply,
    Finsupp.sum_fintype]
  · apply Finset.sum_congr rfl
    intro P hP
    simp only [degreeUnscaledIndex_apply, nsmul_eq_mul]
    exact Nat.div_mul_cancel (hl P)
  · intro P
    simp

/-- The `n`-th coefficient of the bounded Euler product is the sum of the
multiplicative weights of all degree-weighted factor multiplicities. -/
theorem coeff_finiteEulerProduct_eq_sum_weightedFactors
    (w : MonicIrreducibleLE K N → R) :
    PowerSeries.coeff n
        (∏ P : MonicIrreducibleLE K N,
          localEuler P.poly.natDegree (w P)) =
      ∑ m : {m : MonicIrreducibleLE K N →₀ Nat //
          monicFactorWeight m = n},
        multiplicativeFactorWeight w m.1 := by
  classical
  rw [PowerSeries.coeff_prod]
  let good : Finset (MonicIrreducibleLE K N →₀ Nat) :=
    (Finset.finsuppAntidiag Finset.univ n).filter
      (fun l ↦ ∀ P, P.poly.natDegree ∣ l P)
  have hterm (l : MonicIrreducibleLE K N →₀ Nat) :
      (∏ P, PowerSeries.coeff (l P)
        (localEuler P.poly.natDegree (w P))) =
        if (∀ P, P.poly.natDegree ∣ l P) then
          ∏ P, w P ^ (l P / P.poly.natDegree) else 0 := by
    by_cases hl : ∀ P, P.poly.natDegree ∣ l P
    · rw [if_pos hl]
      apply Finset.prod_congr rfl
      intro P hP
      rw [coeff_localEuler (w P) P.natDegree_pos.ne', if_pos (hl P)]
    · rw [if_neg hl]
      push Not at hl
      obtain ⟨P, hP⟩ := hl
      apply Finset.prod_eq_zero (Finset.mem_univ P)
      rw [coeff_localEuler (w P) P.natDegree_pos.ne', if_neg hP]
  simp_rw [hterm]
  rw [← Finset.sum_filter]
  change (∑ l ∈ good, ∏ P, w P ^ (l P / P.poly.natDegree)) = _
  symm
  apply Finset.sum_bij
      (fun m _ ↦ degreeScaledIndex m.1)
  · intro m hm
    simp only [good, Finset.mem_filter, Finset.mem_finsuppAntidiag]
    refine ⟨⟨?_, Finset.subset_univ _⟩, ?_⟩
    · rw [sum_degreeScaledIndex]
      exact m.2
    · intro P
      simp
  · intro a ha b hb hab
    apply Subtype.ext
    simpa only [degreeUnscaledIndex_scaled] using
      congrArg degreeUnscaledIndex hab
  · intro l hl
    simp only [good, Finset.mem_filter, Finset.mem_finsuppAntidiag] at hl
    let m : MonicIrreducibleLE K N →₀ Nat := degreeUnscaledIndex l
    have hm : monicFactorWeight m = n := by
      rw [weight_degreeUnscaledIndex l hl.2, ← hl.1.1]
    refine ⟨⟨m, hm⟩, Finset.mem_univ _, ?_⟩
    exact degreeScaledIndex_unscaled l hl.2
  · intro m hm
    simp [multiplicativeFactorWeight,
      Nat.mul_div_cancel_left _ (MonicIrreducibleLE.natDegree_pos _)]

variable [DecidableEq K]

/-- For `n ≤ N`, the coefficient of the bounded Euler product is the sum over
all monic degree-`n` polynomials of the weight of their irreducible
factorization. -/
theorem coeff_finiteEulerProduct_eq_sum_monic
    (hnN : n ≤ N) (w : MonicIrreducibleLE K N → R) :
    PowerSeries.coeff n
        (∏ P : MonicIrreducibleLE K N,
          localEuler P.poly.natDegree (w P)) =
      ∑ F : {F : K[X] // F.Monic ∧ F.natDegree = n},
        multiplicativeFactorWeight w (monicFactorization hnN F) := by
  rw [coeff_finiteEulerProduct_eq_sum_weightedFactors]
  apply Fintype.sum_equiv (weightedFactorsEquivMonic hnN)
  intro m
  congr 1
  apply monicFactorProduct_injective
  rw [monicFactorProduct_factorization]
  rfl

/-- For the formal-root local weights, the coefficient expansion is the sum
of formal-root weights over monic polynomials of the requested degree. -/
theorem coeff_finiteEulerProduct_formalRootWeight_eq_sum_monic
    (hnN : n ≤ N) (character : AddChar K Complex) (b : Fin 5 → K) :
    PowerSeries.coeff n
        (∏ P : MonicIrreducibleLE K N,
          localEuler P.poly.natDegree
            (formalRootWeight character b P.poly)) =
      ∑ F : {F : K[X] // F.Monic ∧ F.natDegree = n},
        formalRootWeight character b F.1 := by
  rw [coeff_finiteEulerProduct_eq_sum_monic hnN]
  apply Finset.sum_congr rfl
  intro F hF
  rw [multiplicativeFactorWeight_formalRootWeight,
    monicFactorProduct_factorization]

/-- All coefficients from the highest phase degree through the Euler cutoff
vanish.  This is the finite, division-free polynomiality statement used in
the Artin `L`-function argument. -/
theorem coeff_finiteEulerProduct_formalRootWeight_eq_zero
    (hnN : n ≤ N) (character : AddChar K Complex)
    (hcharacter : character ≠ 1) (b : Fin 5 → K) {d : Nat}
    (hdpos : 0 < d) (hd5 : d ≤ 5) (hdn : d ≤ n)
    (hbtop : b ⟨d - 1, by omega⟩ ≠ 0)
    (hb : ∀ i : Fin 5, d < i.val + 1 → b i = 0)
    (hdcast : (d : K) ≠ 0) :
    PowerSeries.coeff n
        (∏ P : MonicIrreducibleLE K N,
          localEuler P.poly.natDegree
            (formalRootWeight character b P.poly)) = 0 := by
  rw [coeff_finiteEulerProduct_formalRootWeight_eq_sum_monic hnN]
  exact sum_formalRootWeight_monic_eq_zero character hcharacter b
    hdpos hd5 hdn hbtop hb hdcast

end Weil

end Waring.Analytic
