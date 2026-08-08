import Mathlib.Tactic

/-!
# Parameters for the pure-additive Stepanov construction

This file records the elementary natural-number arithmetic behind the
even-degree Stepanov auxiliary polynomial.  The extension degree is
`2 * (h + 3)`.  The parameters `S`, `K`, `R`, `A`, and `D` are respectively
the coefficient cutoff, monomial cutoff, number of imposed Hasse derivatives,
phase-degree allowance, and total auxiliary degree bound.
-/

namespace Waring.Analytic

namespace Stepanov

/-- The number `S = p ^ (2 * h + 4)` of available coefficients for each
pair of auxiliary-polynomial indices. -/
def S (p h : Nat) : Nat :=
  p ^ (2 * h + 4)

/-- The cutoff `K = p ^ h` for the ordinary monomial index. -/
def K (p h : Nat) : Nat :=
  p ^ h

/-- The number `R = p ^ (h + 1)` of Hasse-derivative conditions. -/
def R (p h : Nat) : Nat :=
  p ^ (h + 1)

/-- The phase contribution `A = d * (p - 1) * p ^ (h + 2)` to the degree
bound. -/
def A (p h d : Nat) : Nat :=
  d * (p - 1) * p ^ (h + 2)

/-- The total degree bound `D = S + A + K` for each imposed identity. -/
def D (p h d : Nat) : Nat :=
  S p h + A p h d + K p h

/-- The derivative count is the monomial cutoff multiplied by `p`. -/
theorem R_eq_K_mul (p h : Nat) :
    R p h = K p h * p := by
  simp only [R, K, pow_add, pow_one]

/-- The coefficient cutoff is `K` times `p ^ (h + 4)`. -/
theorem S_eq_K_mul_pow (p h : Nat) :
    S p h = K p h * p ^ (h + 4) := by
  simp only [S, K, ← pow_add]
  congr 1
  omega

/-- Multiplying the coefficient cutoff by `p` gives `R * p ^ (h + 4)`. -/
theorem R_mul_pow_eq_p_mul_S (p h : Nat) :
    R p h * p ^ (h + 4) = p * S p h := by
  simp only [R, S]
  calc
    p ^ (h + 1) * p ^ (h + 4) = p ^ ((h + 1) + (h + 4)) :=
      (pow_add _ _ _).symm
    _ = p ^ (1 + (2 * h + 4)) := by congr 1; omega
    _ = p ^ 1 * p ^ (2 * h + 4) := pow_add _ _ _
    _ = p * p ^ (2 * h + 4) := by rw [pow_one]

/-- A factorization of the two lower-order contributions to `D`. -/
theorem A_add_K_eq_K_mul (p h d : Nat) :
    A p h d + K p h = K p h * (d * (p - 1) * p ^ 2 + 1) := by
  simp only [A, K, pow_add]
  ring

/-- The fixed quartic inequality that drives the dimension count. -/
theorem core_lt_pow_four {p d : Nat} (hp : 1 < p) (hd : d < p) :
    d * (p - 1) * p ^ 2 + 1 < p ^ 4 := by
  have hp0 : 0 < p := by omega
  have hpm : p - 1 < p := by omega
  have hdle : d ≤ p - 1 := by omega
  have hterm :
      d * (p - 1) * p ^ 2 ≤ (p - 1) * (p - 1) * p ^ 2 := by
    gcongr
  have hsquare : (p - 1) ^ 2 < p ^ 2 :=
    Nat.pow_lt_pow_left hpm (by norm_num)
  have hfactor :
      (p - 1) * (p - 1) * p ^ 2 < p ^ 2 * p ^ 2 := by
    exact Nat.mul_lt_mul_of_pos_right (by simpa [pow_two] using hsquare)
      (Nat.pow_pos hp0)
  calc
    d * (p - 1) * p ^ 2 + 1
        ≤ (p - 1) * (p - 1) * p ^ 2 + 1 :=
      Nat.add_le_add_right hterm 1
    _ < p ^ 2 * p ^ 2 := by
      nlinarith [show 2 ≤ p by omega]
    _ = p ^ 4 := by ring

/-- The lower-order degree terms fit strictly below `p ^ (h + 4)`. -/
theorem A_add_K_lt_pow {p h d : Nat} (hp : 1 < p) (hd : d < p) :
    A p h d + K p h < p ^ (h + 4) := by
  have hp0 : 0 < p := by omega
  rw [A_add_K_eq_K_mul, show p ^ (h + 4) = K p h * p ^ 4 by
    simp only [K, pow_add]]
  exact Nat.mul_lt_mul_of_pos_left (core_lt_pow_four hp hd)
    (Nat.pow_pos hp0)

/-- The imposed derivative order is below `p ^ (h + 3)`, the degree of one
half of the even extension. -/
theorem R_lt_pow {p h : Nat} (hp : 1 < p) :
    R p h < p ^ (h + 3) := by
  rw [R]
  exact Nat.pow_lt_pow_right hp (by omega)

/-- The number `p * S * (K + 1)` of unknown coefficients is strictly larger
than the at-most `R * D` scalar coefficient conditions. -/
theorem constraints_lt_coefficients {p h d : Nat} (hp : 1 < p)
    (hd : d < p) :
    R p h * D p h d < p * S p h * (K p h + 1) := by
  have hp0 : 0 < p := by omega
  have hinside :
      S p h + (A p h d + K p h) < S p h + p ^ (h + 4) :=
    Nat.add_lt_add_left (A_add_K_lt_pow hp hd) _
  have hRpos : 0 < R p h := by
    exact Nat.pow_pos hp0
  have hmul := Nat.mul_lt_mul_of_pos_left hinside hRpos
  rw [← add_assoc] at hmul
  change R p h * D p h d < R p h * (S p h + p ^ (h + 4)) at hmul
  calc
    R p h * D p h d < R p h * (S p h + p ^ (h + 4)) := hmul
    _ = R p h * (p ^ (h + 4) * K p h + p ^ (h + 4)) := by
      rw [S_eq_K_mul_pow]
      ring
    _ = (R p h * p ^ (h + 4)) * (K p h + 1) := by ring
    _ = (p * S p h) * (K p h + 1) := by
      rw [R_mul_pow_eq_p_mul_S]
    _ = p * S p h * (K p h + 1) := rfl

end Stepanov

end Waring.Analytic
