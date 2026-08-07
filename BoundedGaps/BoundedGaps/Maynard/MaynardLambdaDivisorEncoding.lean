import BoundedGaps.Maynard.MaynardLambdaDivisorIdentity

noncomputable section

/-!
# Encoding divisor and quotient products in the lambda bound

Maynard2013v3, equation `eq:LambdaSize` (source lines 304--316), replaces a
divisor `a` of the fixed tuple product and a coprime quotient product `t` by
the single squarefree natural `a*t`. This file proves that the replacement is
injective on the exact finite support and preserves the required cutoff.
-/

namespace BoundedGaps.Maynard

open scoped ArithmeticFunction.omega BigOperators
local instance divisorEncodingDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

def lambdaDivisorQuotientProductSupport
    (H : Finset ℕ) (R : ℕ) (d : H → ℕ) : Finset (ℕ × ℕ) :=
  ((lambdaQuotientTupleSupport H R d).image (divisorTupleProduct H)) ×ˢ
    (divisorTupleProduct H d).divisors

def lambdaDivisorQuotientEncoding (x : ℕ × ℕ) : ℕ :=
  x.2 * x.1

theorem lambdaQuotientProduct_image_data
    {H : Finset ℕ} {R W t : ℕ} {d : H → ℕ}
    (hd : IsMaynardDivisorTuple H R W d)
    (ht : t ∈ (lambdaQuotientTupleSupport H R d).image
      (divisorTupleProduct H)) :
    0 < t ∧
      divisorTupleProduct H d * t < R ∧
      Squarefree t ∧
      Nat.Coprime (divisorTupleProduct H d) t := by
  classical
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
  have hsData := lambdaQuotientTupleSupport_data hd hs
  refine ⟨?_, hsData.2.1, hsData.2.2.1, hsData.2.2.2⟩
  unfold divisorTupleProduct
  exact Finset.prod_pos fun h _ => hsData.1 h

theorem lambdaDivisorQuotientEncoding_injOn
    {H : Finset ℕ} {R W : ℕ} {d : H → ℕ}
    (hd : IsMaynardDivisorTuple H R W d) :
    Set.InjOn lambdaDivisorQuotientEncoding
      (lambdaDivisorQuotientProductSupport H R d : Set (ℕ × ℕ)) := by
  intro x hx y hy hxy
  have hxMem := Finset.mem_product.mp hx
  have hyMem := Finset.mem_product.mp hy
  have hxData := lambdaQuotientProduct_image_data hd hxMem.1
  have hyData := lambdaQuotientProduct_image_data hd hyMem.1
  have hxGcd : Nat.gcd (lambdaDivisorQuotientEncoding x)
      (divisorTupleProduct H d) = x.2 := by
    unfold lambdaDivisorQuotientEncoding
    rw [mul_comm]
    exact Nat.gcd_mul_of_coprime_of_dvd hxData.2.2.2.symm
      (Nat.dvd_of_mem_divisors hxMem.2)
  have hyGcd : Nat.gcd (lambdaDivisorQuotientEncoding y)
      (divisorTupleProduct H d) = y.2 := by
    unfold lambdaDivisorQuotientEncoding
    rw [mul_comm]
    exact Nat.gcd_mul_of_coprime_of_dvd hyData.2.2.2.symm
      (Nat.dvd_of_mem_divisors hyMem.2)
  have hsecond : x.2 = y.2 := by
    rw [← hxGcd, hxy, hyGcd]
  have hfirst : x.1 = y.1 := by
    unfold lambdaDivisorQuotientEncoding at hxy
    rw [hsecond] at hxy
    apply Nat.mul_left_cancel (Nat.pos_of_mem_divisors hyMem.2)
    exact hxy
  exact Prod.ext hfirst hsecond

theorem lambdaDivisorQuotientEncoding_data
    {H : Finset ℕ} {R W : ℕ} {d : H → ℕ} {x : ℕ × ℕ}
    (hd : IsMaynardDivisorTuple H R W d)
    (hx : x ∈ lambdaDivisorQuotientProductSupport H R d) :
    0 < lambdaDivisorQuotientEncoding x ∧
      lambdaDivisorQuotientEncoding x < R ∧
      Squarefree (lambdaDivisorQuotientEncoding x) := by
  have hxMem := Finset.mem_product.mp hx
  have htData := lambdaQuotientProduct_image_data hd hxMem.1
  have haDvd := Nat.dvd_of_mem_divisors hxMem.2
  have haPos := Nat.pos_of_mem_divisors hxMem.2
  have haSq := hd.2.2.squarefree_of_dvd haDvd
  have haCop : Nat.Coprime x.2 x.1 := htData.2.2.2.of_dvd_left haDvd
  refine ⟨Nat.mul_pos haPos htData.1, ?_, (Nat.squarefree_mul haCop).mpr ⟨haSq,
    htData.2.2.1⟩⟩
  exact lt_of_le_of_lt (Nat.mul_le_mul_right x.1
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hd.2.2.ne_zero) haDvd)) htData.2.1

theorem lambdaDivisorQuotientEncoding_image_subset_Icc
    {H : Finset ℕ} {R W : ℕ} {d : H → ℕ}
    (hd : IsMaynardDivisorTuple H R W d) :
    (lambdaDivisorQuotientProductSupport H R d).image
        lambdaDivisorQuotientEncoding ⊆ Finset.Icc 1 R := by
  intro u hu
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
  have hxData := lambdaDivisorQuotientEncoding_data hd hx
  exact Finset.mem_Icc.mpr ⟨hxData.1, hxData.2.1.le⟩

theorem squarefree_of_mem_lambdaDivisorQuotientEncoding_image
    {H : Finset ℕ} {R W u : ℕ} {d : H → ℕ}
    (hd : IsMaynardDivisorTuple H R W d)
    (hu : u ∈ (lambdaDivisorQuotientProductSupport H R d).image
      lambdaDivisorQuotientEncoding) :
    Squarefree u := by
  classical
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
  exact (lambdaDivisorQuotientEncoding_data hd hx).2.2

theorem lambdaDivisorQuotient_tauWeight_le
    {H : Finset ℕ} {R W k : ℕ} {d : H → ℕ} {x : ℕ × ℕ}
    (hk : 1 ≤ k) (hd : IsMaynardDivisorTuple H R W d)
    (hx : x ∈ lambdaDivisorQuotientProductSupport H R d) :
    ((k ^ ω x.1 : ℕ) : ℝ) /
        (Nat.totient (lambdaDivisorQuotientEncoding x) : ℝ) ≤
      ((k ^ ω (lambdaDivisorQuotientEncoding x) : ℕ) : ℝ) /
        (Nat.totient (lambdaDivisorQuotientEncoding x) : ℝ) := by
  have hxMem := Finset.mem_product.mp hx
  have htData := lambdaQuotientProduct_image_data hd hxMem.1
  have haCop : Nat.Coprime x.2 x.1 :=
    htData.2.2.2.of_dvd_left (Nat.dvd_of_mem_divisors hxMem.2)
  have homega : ω x.1 ≤ ω (lambdaDivisorQuotientEncoding x) := by
    unfold lambdaDivisorQuotientEncoding
    rw [ArithmeticFunction.cardDistinctFactors_mul haCop]
    omega
  apply div_le_div_of_nonneg_right
  · exact_mod_cast pow_le_pow_right₀ hk homega
  · positivity

end BoundedGaps.Maynard
