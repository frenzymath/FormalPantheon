import Waring.Analytic.WeilWeights
import Mathlib.Logic.Equiv.Prod

/-!
# Vanishing of the high coefficients of the degree-five Artin L-function

Monic polynomials of degree `n` are parametrized by their `n` lower
coefficients.  If the highest nonzero exponent of the phase is `d <= 5`,
varying the coefficient of `X^(n-d)` changes the formal root phase by a
nonzero linear term.  Additive-character orthogonality then makes the sum of
the weights vanish for every `n >= d`.
-/

namespace Waring.Analytic

open Polynomial
open scoped BigOperators

namespace Weil

variable {R : Type*} [CommRing R]

/-- The polynomial of degree less than `n` with coefficient vector `c`. -/
noncomputable def lowerPolynomial (n : Nat) (c : Fin n → R) : R[X] :=
  ((degreeLTEquiv R n).symm c).1

/-- The monic degree-`n` polynomial whose lower coefficient vector is `c`. -/
noncomputable def monicPolynomial (n : Nat) (c : Fin n → R) : R[X] :=
  X ^ n + lowerPolynomial n c

/-- The lower-coefficient polynomial has degree strictly less than `n`. -/
theorem lowerPolynomial_mem (n : Nat) (c : Fin n → R) :
    lowerPolynomial n c ∈ degreeLT R n :=
  ((degreeLTEquiv R n).symm c).2

/-- The polynomial constructed from `c` is monic of degree `n`. -/
theorem monicPolynomial_spec [Nontrivial R] (n : Nat) (c : Fin n → R) :
    (monicPolynomial n c).Monic ∧ (monicPolynomial n c).natDegree = n := by
  have hlt := mem_degreeLT.mp (lowerPolynomial_mem n c)
  refine ⟨monic_X_pow_add hlt, ?_⟩
  rw [monicPolynomial, natDegree_add_eq_left_of_degree_lt]
  · simp
  · simpa using hlt

/-- The coefficients of `lowerPolynomial` are the entries of its vector. -/
theorem lowerPolynomial_coeff (n : Nat) (c : Fin n → R) (i : Fin n) :
    (lowerPolynomial n c).coeff i = c i := by
  exact congrFun ((degreeLTEquiv R n).apply_symm_apply c) i

/-- The lower coefficients of `monicPolynomial` are the entries of its vector. -/
theorem monicPolynomial_coeff [Nontrivial R] (n : Nat) (c : Fin n → R)
    (i : Fin n) :
    (monicPolynomial n c).coeff i = c i := by
  rw [monicPolynomial, coeff_add, coeff_X_pow, if_neg i.isLt.ne, zero_add]
  exact lowerPolynomial_coeff n c i

/-- The standard equivalence between monic degree-`n` polynomials and their
lower coefficient vectors. -/
noncomputable def monicCoefficientEquiv [Nontrivial R] (n : Nat) :
    {F : R[X] // F.Monic ∧ F.natDegree = n} ≃ (Fin n → R) :=
  (monicEquivDegreeLT n).trans (degreeLTEquiv R n).toEquiv

/-- Monic polynomials of one fixed degree over a finite ring form a finite
type, by their lower coefficient vectors. -/
noncomputable instance instFintypeMonicNatDegree [Nontrivial R] [Fintype R]
    (n : Nat) : Fintype {F : R[X] // F.Monic ∧ F.natDegree = n} :=
  Fintype.ofEquiv (Fin n → R) (monicCoefficientEquiv n).symm

/-- The inverse coefficient parametrization is `monicPolynomial`. -/
theorem monicCoefficientEquiv_symm_apply [Nontrivial R] (n : Nat)
    (c : Fin n → R) :
    ((monicCoefficientEquiv n).symm c).1 = monicPolynomial n c := by
  rfl

/-- Reversed coefficient `k` is vector entry `n-k`. -/
theorem reverseCoeff_monicPolynomial [IsDomain R] (n k : Nat)
    (c : Fin n → R) (hkpos : 0 < k) (hk : k ≤ n) :
    reverseCoeff (monicPolynomial n c) k =
      c ⟨n - k, Nat.sub_lt (Nat.pos_of_ne_zero (by omega)) hkpos⟩ := by
  rw [reverseCoeff, Polynomial.coeff_reverse, (monicPolynomial_spec n c).2,
    Polynomial.revAt_le hk]
  simpa using monicPolynomial_coeff n c
    ⟨n - k, Nat.sub_lt (Nat.pos_of_ne_zero (by omega)) hkpos⟩

/-- Updating vector entry `n-d` updates reversed coefficient `d`. -/
theorem reverseCoeff_monicPolynomial_update_self [IsDomain R] {n d : Nat}
    (c : Fin n → R) (x : R) (hdpos : 0 < d) (hdn : d ≤ n) :
    reverseCoeff (monicPolynomial n
      (Function.update c
        ⟨n - d, Nat.sub_lt (Nat.pos_of_ne_zero (by omega)) hdpos⟩ x)) d = x := by
  rw [reverseCoeff_monicPolynomial n d _ hdpos hdn]
  simp

/-- Updating vector entry `n-d` leaves earlier reversed coefficients fixed. -/
theorem reverseCoeff_monicPolynomial_update_of_lt [IsDomain R]
    {n d k : Nat} (c : Fin n → R) (x : R) (hkpos : 0 < k)
    (hkd : k < d) (hdn : d ≤ n) :
    reverseCoeff (monicPolynomial n
      (Function.update c
        ⟨n - d, Nat.sub_lt (Nat.pos_of_ne_zero (by omega)) (by omega)⟩ x)) k =
      reverseCoeff (monicPolynomial n c) k := by
  have hkn : k ≤ n := by omega
  rw [reverseCoeff_monicPolynomial n k _ hkpos hkn,
    reverseCoeff_monicPolynomial n k c hkpos hkn, Function.update_of_ne]
  intro h
  have hval := congrArg Fin.val h
  dsimp only at hval
  omega

private theorem formalRootPhase_update_one [IsDomain R] {n : Nat}
    (b : Fin 5 → R) (c : Fin n → R) (x : R) (hn : 1 ≤ n)
    (hb : ∀ i : Fin 5, 1 < i.val + 1 → b i = 0) :
    formalRootPhase b (monicPolynomial n
      (Function.update c ⟨n - 1, by omega⟩ x)) =
      -(1 : R) * b ⟨0, by omega⟩ * x +
        formalRootPhase b (monicPolynomial n
          (Function.update c ⟨n - 1, by omega⟩ 0)) := by
  have hphase (F : R[X]) :
      formalRootPhase b F = b (0 : Fin 5) * formalRootPowerSum 1 F := by
    rw [formalRootPhase]
    apply Finset.sum_eq_single (0 : Fin 5)
    · intro i hi hi0
      have hbi : b i = 0 := hb i (by fin_cases i <;> simp_all)
      simp [hbi]
    · simp
  have hx := reverseCoeff_monicPolynomial_update_self c x
    (by omega : 0 < 1) hn
  have hz := reverseCoeff_monicPolynomial_update_self c (0 : R)
    (by omega : 0 < 1) hn
  rw [hphase, hphase]
  simp [formalRootPowerSum, hx, hz]

private theorem formalRootPhase_update_two [IsDomain R] {n : Nat}
    (b : Fin 5 → R) (c : Fin n → R) (x : R) (hn : 2 ≤ n)
    (hb : ∀ i : Fin 5, 2 < i.val + 1 → b i = 0) :
    formalRootPhase b (monicPolynomial n
      (Function.update c ⟨n - 2, by omega⟩ x)) =
      -(2 : R) * b ⟨1, by omega⟩ * x +
        formalRootPhase b (monicPolynomial n
          (Function.update c ⟨n - 2, by omega⟩ 0)) := by
  have hb2 : b (2 : Fin 5) = 0 := hb _ (by omega)
  have hb3 : b (3 : Fin 5) = 0 := hb _ (by omega)
  have hb4 : b (4 : Fin 5) = 0 := hb _ (by omega)
  have hphase (F : R[X]) :
      formalRootPhase b F = b (0 : Fin 5) * formalRootPowerSum 1 F +
        b (1 : Fin 5) * formalRootPowerSum 2 F := by
    rw [formalRootPhase, Fin.sum_univ_five]
    simp [hb2, hb3, hb4]
  have hx1 := reverseCoeff_monicPolynomial_update_of_lt c x
    (by omega : 0 < 1) (by omega : 1 < 2) hn
  have hz1 := reverseCoeff_monicPolynomial_update_of_lt c (0 : R)
    (by omega : 0 < 1) (by omega : 1 < 2) hn
  have hx2 := reverseCoeff_monicPolynomial_update_self c x
    (by omega : 0 < 2) hn
  have hz2 := reverseCoeff_monicPolynomial_update_self c (0 : R)
    (by omega : 0 < 2) hn
  rw [hphase, hphase]
  simp [formalRootPowerSum, hx1, hz1, hx2, hz2]
  ring

private theorem formalRootPhase_update_three [IsDomain R] {n : Nat}
    (b : Fin 5 → R) (c : Fin n → R) (x : R) (hn : 3 ≤ n)
    (hb : ∀ i : Fin 5, 3 < i.val + 1 → b i = 0) :
    formalRootPhase b (monicPolynomial n
      (Function.update c ⟨n - 3, by omega⟩ x)) =
      -(3 : R) * b ⟨2, by omega⟩ * x +
        formalRootPhase b (monicPolynomial n
          (Function.update c ⟨n - 3, by omega⟩ 0)) := by
  have hb3 : b (3 : Fin 5) = 0 := hb _ (by omega)
  have hb4 : b (4 : Fin 5) = 0 := hb _ (by omega)
  have hphase (F : R[X]) :
      formalRootPhase b F = b (0 : Fin 5) * formalRootPowerSum 1 F +
        b (1 : Fin 5) * formalRootPowerSum 2 F +
          b (2 : Fin 5) * formalRootPowerSum 3 F := by
    rw [formalRootPhase, Fin.sum_univ_five]
    simp [hb3, hb4]
  have hx1 := reverseCoeff_monicPolynomial_update_of_lt c x
    (by omega : 0 < 1) (by omega : 1 < 3) hn
  have hz1 := reverseCoeff_monicPolynomial_update_of_lt c (0 : R)
    (by omega : 0 < 1) (by omega : 1 < 3) hn
  have hx2 := reverseCoeff_monicPolynomial_update_of_lt c x
    (by omega : 0 < 2) (by omega : 2 < 3) hn
  have hz2 := reverseCoeff_monicPolynomial_update_of_lt c (0 : R)
    (by omega : 0 < 2) (by omega : 2 < 3) hn
  have hx3 := reverseCoeff_monicPolynomial_update_self c x
    (by omega : 0 < 3) hn
  have hz3 := reverseCoeff_monicPolynomial_update_self c (0 : R)
    (by omega : 0 < 3) hn
  rw [hphase, hphase]
  simp [formalRootPowerSum, hx1, hz1, hx2, hz2, hx3, hz3]
  ring

private theorem formalRootPhase_update_four [IsDomain R] {n : Nat}
    (b : Fin 5 → R) (c : Fin n → R) (x : R) (hn : 4 ≤ n)
    (hb : ∀ i : Fin 5, 4 < i.val + 1 → b i = 0) :
    formalRootPhase b (monicPolynomial n
      (Function.update c ⟨n - 4, by omega⟩ x)) =
      -(4 : R) * b ⟨3, by omega⟩ * x +
        formalRootPhase b (monicPolynomial n
          (Function.update c ⟨n - 4, by omega⟩ 0)) := by
  have hb4 : b (4 : Fin 5) = 0 := hb _ (by omega)
  have hphase (F : R[X]) :
      formalRootPhase b F = b (0 : Fin 5) * formalRootPowerSum 1 F +
        b (1 : Fin 5) * formalRootPowerSum 2 F +
          b (2 : Fin 5) * formalRootPowerSum 3 F +
            b (3 : Fin 5) * formalRootPowerSum 4 F := by
    rw [formalRootPhase, Fin.sum_univ_five]
    simp [hb4]
  have hx1 := reverseCoeff_monicPolynomial_update_of_lt c x
    (by omega : 0 < 1) (by omega : 1 < 4) hn
  have hz1 := reverseCoeff_monicPolynomial_update_of_lt c (0 : R)
    (by omega : 0 < 1) (by omega : 1 < 4) hn
  have hx2 := reverseCoeff_monicPolynomial_update_of_lt c x
    (by omega : 0 < 2) (by omega : 2 < 4) hn
  have hz2 := reverseCoeff_monicPolynomial_update_of_lt c (0 : R)
    (by omega : 0 < 2) (by omega : 2 < 4) hn
  have hx3 := reverseCoeff_monicPolynomial_update_of_lt c x
    (by omega : 0 < 3) (by omega : 3 < 4) hn
  have hz3 := reverseCoeff_monicPolynomial_update_of_lt c (0 : R)
    (by omega : 0 < 3) (by omega : 3 < 4) hn
  have hx4 := reverseCoeff_monicPolynomial_update_self c x
    (by omega : 0 < 4) hn
  have hz4 := reverseCoeff_monicPolynomial_update_self c (0 : R)
    (by omega : 0 < 4) hn
  rw [hphase, hphase]
  simp [formalRootPowerSum, hx1, hz1, hx2, hz2, hx3, hz3, hx4, hz4]
  ring

private theorem formalRootPhase_update_five [IsDomain R] {n : Nat}
    (b : Fin 5 → R) (c : Fin n → R) (x : R) (hn : 5 ≤ n) :
    formalRootPhase b (monicPolynomial n
      (Function.update c ⟨n - 5, by omega⟩ x)) =
      -(5 : R) * b ⟨4, by omega⟩ * x +
        formalRootPhase b (monicPolynomial n
          (Function.update c ⟨n - 5, by omega⟩ 0)) := by
  have hphase (F : R[X]) :
      formalRootPhase b F = b (0 : Fin 5) * formalRootPowerSum 1 F +
        b (1 : Fin 5) * formalRootPowerSum 2 F +
          b (2 : Fin 5) * formalRootPowerSum 3 F +
            b (3 : Fin 5) * formalRootPowerSum 4 F +
              b (4 : Fin 5) * formalRootPowerSum 5 F := by
    rw [formalRootPhase, Fin.sum_univ_five]
    norm_num
  have hx1 := reverseCoeff_monicPolynomial_update_of_lt c x
    (by omega : 0 < 1) (by omega : 1 < 5) hn
  have hz1 := reverseCoeff_monicPolynomial_update_of_lt c (0 : R)
    (by omega : 0 < 1) (by omega : 1 < 5) hn
  have hx2 := reverseCoeff_monicPolynomial_update_of_lt c x
    (by omega : 0 < 2) (by omega : 2 < 5) hn
  have hz2 := reverseCoeff_monicPolynomial_update_of_lt c (0 : R)
    (by omega : 0 < 2) (by omega : 2 < 5) hn
  have hx3 := reverseCoeff_monicPolynomial_update_of_lt c x
    (by omega : 0 < 3) (by omega : 3 < 5) hn
  have hz3 := reverseCoeff_monicPolynomial_update_of_lt c (0 : R)
    (by omega : 0 < 3) (by omega : 3 < 5) hn
  have hx4 := reverseCoeff_monicPolynomial_update_of_lt c x
    (by omega : 0 < 4) (by omega : 4 < 5) hn
  have hz4 := reverseCoeff_monicPolynomial_update_of_lt c (0 : R)
    (by omega : 0 < 4) (by omega : 4 < 5) hn
  have hx5 := reverseCoeff_monicPolynomial_update_self c x
    (by omega : 0 < 5) hn
  have hz5 := reverseCoeff_monicPolynomial_update_self c (0 : R)
    (by omega : 0 < 5) hn
  rw [hphase, hphase]
  simp [formalRootPowerSum, hx1, hz1, hx2, hz2, hx3, hz3, hx4, hz4,
    hx5, hz5]
  ring

/-- If `d` is the largest possible phase exponent, varying coefficient
`X^(n-d)` changes the phase by the affine term `-d * b[d-1] * x`. -/
theorem formalRootPhase_update_highest [IsDomain R] {n d : Nat}
    (b : Fin 5 → R) (c : Fin n → R) (x : R) (hdpos : 0 < d)
    (hd5 : d ≤ 5) (hdn : d ≤ n)
    (hb : ∀ i : Fin 5, d < i.val + 1 → b i = 0) :
    formalRootPhase b (monicPolynomial n
      (Function.update c
        ⟨n - d, Nat.sub_lt (Nat.pos_of_ne_zero (by omega)) hdpos⟩ x)) =
      -(d : R) * b ⟨d - 1, by omega⟩ * x +
        formalRootPhase b (monicPolynomial n
          (Function.update c
            ⟨n - d, Nat.sub_lt (Nat.pos_of_ne_zero (by omega)) hdpos⟩ 0)) := by
  interval_cases d
  · simpa using formalRootPhase_update_one b c x hdn hb
  · simpa using formalRootPhase_update_two b c x hdn hb
  · simpa using formalRootPhase_update_three b c x hdn hb
  · simpa using formalRootPhase_update_four b c x hdn hb
  · simpa using formalRootPhase_update_five b c x hdn

/-- A nontrivial additive character sums to zero on a nonconstant affine
linear function over a finite field. -/
theorem sum_addChar_affine_eq_zero {K : Type*} [Field K] [Fintype K]
    (character : AddChar K Complex) (hcharacter : character ≠ 1)
    {a : K} (ha : a ≠ 0) (z : K) :
    ∑ x : K, character (a * x + z) = 0 := by
  have hshiftOne : character.mulShift a ≠ 1 :=
    (AddChar.IsPrimitive.of_ne_one hcharacter) ha
  have hshift : character.mulShift a ≠ 0 := by
    simpa only [AddChar.one_eq_zero] using hshiftOne
  have hzero : ∑ x : K, character (a * x) = 0 := by
    change ∑ x : K, character.mulShift a x = 0
    exact AddChar.sum_eq_zero_iff_ne_zero.mpr hshift
  simp_rw [character.map_add_eq_mul]
  rw [← Finset.sum_mul, hzero, zero_mul]

/-- A sum over a finite function space vanishes if it vanishes on every fiber
obtained by varying one coordinate. -/
theorem sum_pi_eq_zero_of_sum_update_eq_zero {I K A : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] [Zero K] [AddCommMonoid A]
    (j : I) (w : (I → K) → A)
    (h : ∀ c : I → K, c j = 0 →
      ∑ x : K, w (Function.update c j x) = 0) :
    ∑ c : I → K, w c = 0 := by
  classical
  let e := Equiv.funSplitAt j K
  calc
    ∑ c : I → K, w c =
        ∑ q : K × ({i // i ≠ j} → K), w (e.symm q) := by
      exact (e.symm.sum_comp w).symm
    _ = ∑ r : ({i // i ≠ j} → K), ∑ x : K, w (e.symm (x, r)) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      have he (x : K) :
          e.symm (x, r) = Function.update (e.symm (0, r)) j x := by
        ext i
        by_cases hij : i = j
        · subst i
          simp [e]
        · simp [e, hij]
      calc
        ∑ x : K, w (e.symm (x, r)) =
            ∑ x : K, w (Function.update (e.symm (0, r)) j x) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [he x]
        _ = 0 := h _ (by simp [e])

/-- For `n >= d`, the total degree-`n` formal root weight is zero when `d` is
the highest nonzero phase exponent and remains nonzero in the field. -/
theorem sum_formalRootWeight_monicPolynomial_eq_zero {K : Type*}
    [Field K] [Fintype K] (character : AddChar K Complex)
    (hcharacter : character ≠ 1) (b : Fin 5 → K) {d n : Nat}
    (hdpos : 0 < d) (hd5 : d ≤ 5) (hdn : d ≤ n)
    (hbtop : b ⟨d - 1, by omega⟩ ≠ 0)
    (hb : ∀ i : Fin 5, d < i.val + 1 → b i = 0)
    (hdcast : (d : K) ≠ 0) :
    ∑ c : Fin n → K, formalRootWeight character b (monicPolynomial n c) = 0 := by
  let j : Fin n :=
    ⟨n - d, Nat.sub_lt (Nat.pos_of_ne_zero (by omega)) hdpos⟩
  apply sum_pi_eq_zero_of_sum_update_eq_zero j
  intro c hc
  let a : K := -(d : K) * b ⟨d - 1, by omega⟩
  have ha : a ≠ 0 := by
    exact mul_ne_zero (neg_ne_zero.mpr hdcast) hbtop
  let z : K := formalRootPhase b (monicPolynomial n
    (Function.update c j 0))
  calc
    ∑ x : K, formalRootWeight character b
        (monicPolynomial n (Function.update c j x)) =
        ∑ x : K, character (a * x + z) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [formalRootWeight, formalRootPhase_update_highest b c x hdpos hd5 hdn hb]
    _ = 0 := sum_addChar_affine_eq_zero character hcharacter ha z

/-- The same cancellation, stated as a sum over bundled monic polynomials of
degree `n`. -/
theorem sum_formalRootWeight_monic_eq_zero {K : Type*} [Field K] [Fintype K]
    (character : AddChar K Complex) (hcharacter : character ≠ 1)
    (b : Fin 5 → K) {d n : Nat} (hdpos : 0 < d) (hd5 : d ≤ 5)
    (hdn : d ≤ n) (hbtop : b ⟨d - 1, by omega⟩ ≠ 0)
    (hb : ∀ i : Fin 5, d < i.val + 1 → b i = 0)
    (hdcast : (d : K) ≠ 0) :
    ∑ F : {F : K[X] // F.Monic ∧ F.natDegree = n},
      formalRootWeight character b F.1 = 0 := by
  let e := monicCoefficientEquiv (R := K) n
  calc
    ∑ F : {F : K[X] // F.Monic ∧ F.natDegree = n},
        formalRootWeight character b F.1 =
        ∑ c : Fin n → K, formalRootWeight character b (e.symm c).1 := by
      exact (e.symm.sum_comp (fun F ↦ formalRootWeight character b F.1)).symm
    _ = ∑ c : Fin n → K,
        formalRootWeight character b (monicPolynomial n c) := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [monicCoefficientEquiv_symm_apply]
    _ = 0 := sum_formalRootWeight_monicPolynomial_eq_zero character hcharacter
      b hdpos hd5 hdn hbtop hb hdcast

-- Nontriviality remains in this coefficient theorem so it shares the reviewed
-- monic-polynomial interface used by the equivalence and finite enumeration.
attribute [nolint unusedArguments] monicPolynomial_coeff

end Weil

end Waring.Analytic
