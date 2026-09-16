import PrimesRestrictedDigits.Fourier.ClosedWindowMaximum
import PrimesRestrictedDigits.Fourier.HybridSourceResidueReindex

/-!
# Source phases for the alternative hybrid Sigma branches

These are the phases and modulo-one identities used between the denominator split and the
`Sigma_2`--`Sigma_5` factorization in published Lemma 10.7, pp. 181--183.
-/

namespace PrimesRestrictedDigits

noncomputable section

/-- A period-one function has the same closed-window value at centers that
represent the same point of the unit additive circle. This definition-level
identity is valid even when the window radius is negative. -/
theorem closedWindowMaximum_eq_of_unitAddCircle_eq
    {f : Real → Real} (hf : Function.Periodic f 1)
    (delta x y : Real)
    (hxy : (x : UnitAddCircle) = (y : UnitAddCircle)) :
    closedWindowMaximum f delta x = closedWindowMaximum f delta y := by
  have hpoint (eta : Real) : f (x + eta) = f (y + eta) := by
    have hxy' : ((x + eta : Real) : UnitAddCircle) =
        ((y + eta : Real) : UnitAddCircle) := by
      change (x : UnitAddCircle) + (eta : UnitAddCircle) =
        (y : UnitAddCircle) + (eta : UnitAddCircle)
      exact congrArg (fun w : UnitAddCircle => w + (eta : UnitAddCircle)) hxy
    simpa only [Function.Periodic.lift_coe] using congrArg hf.lift hxy'
  unfold closedWindowMaximum
  congr 1
  exact Set.image_congr fun eta _ => hpoint eta

/-- The source phase `beta_2`, with its first two decimal coordinates combined
by the low-first mixed-radix equivalence. -/
noncomputable def hybridSourceBetaTwo
    (q d₁ d₂ d₃ : Nat) (a : ReducedResidue q)
    (b : Fin d₁ × Fin d₂) : Real :=
  (a.val.val : Real) / (q : Real) +
    ((lowHighFinEquiv d₁ d₂ b).val : Real) / (d₁ * d₂ * d₃ : Nat)

/-- The source phase `beta_3` after the two decimal-power scales have been
applied. Natural division is retained before coercion to `Real`. -/
noncomputable def decimalHybridSourceBetaThree
    (q d₁ d₂ d₃ k v : Nat) (a : ReducedResidue q)
    (b₁ : Fin d₁) : Real :=
  (((10 ^ k * 10 ^ v) * a.val.val : Nat) : Real) / (q : Real) +
    (((((10 ^ k * 10 ^ v) / (d₂ * d₃)) * b₁.val : Nat) : Real) /
      (d₁ : Real))

/-- The combined definition of `beta_2` is literally the source's
three-fraction expression. -/
theorem hybridSourceBetaTwo_eq
    {q d₁ d₂ d₃ : Nat} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hd₃ : 0 < d₃) (a : ReducedResidue q) (b₁ : Fin d₁)
    (b₂ : Fin d₂) :
    hybridSourceBetaTwo q d₁ d₂ d₃ a (b₁, b₂) =
      (a.val.val : Real) / (q : Real) +
        (b₁.val : Real) / (d₁ * d₂ * d₃ : Nat) +
          (b₂.val : Real) / (d₂ * d₃ : Nat) := by
  rw [hybridSourceBetaTwo, lowHighFinEquiv_val]
  push_cast
  field_simp [show (d₁ : Real) ≠ 0 by exact_mod_cast hd₁.ne',
    show (d₂ : Real) ≠ 0 by exact_mod_cast hd₂.ne',
    show (d₃ : Real) ≠ 0 by exact_mod_cast hd₃.ne']
  ring

/-- Multiplying `beta_2` by a scale divisible by `d₃` gives the weighted
first-two-coordinate phase used by the reduced-residue equivalence. -/
theorem hybridSourceBetaTwo_scale_eq
    {q d₁ d₂ d₃ D : Nat} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hd₃ : 0 < d₃) (hd₃D : d₃ ∣ D) (a : ReducedResidue q)
    (b : Fin d₁ × Fin d₂) :
    (D : Real) * hybridSourceBetaTwo q d₁ d₂ d₃ a b =
      (((D * a.val.val : Nat) : Real) / (q : Real) +
        ((((D / d₃) * (lowHighFinEquiv d₁ d₂ b).val : Nat) : Real) /
          (d₁ * d₂ : Nat))) := by
  rcases hd₃D with ⟨t, rfl⟩
  rw [hybridSourceBetaTwo]
  simp only [Nat.mul_div_right _ hd₃]
  push_cast
  field_simp [show (d₁ : Real) ≠ 0 by exact_mod_cast hd₁.ne',
    show (d₂ : Real) ≠ 0 by exact_mod_cast hd₂.ne',
    show (d₃ : Real) ≠ 0 by exact_mod_cast hd₃.ne']

/-- Combining `(b₂,b₃)` gives the exact complete grid in the second
Sigma branch. -/
theorem hybridSourceBetaTwo_add_third_eq_grid
    {q d₁ d₂ d₃ : Nat} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hd₃ : 0 < d₃) (a : ReducedResidue q) (b₁ : Fin d₁)
    (b₂ : Fin d₂) (b₃ : Fin d₃) :
    hybridSourceBetaTwo q d₁ d₂ d₃ a (b₁, b₂) +
        (b₃.val : Real) / (d₃ : Real) =
      ((a.val.val : Real) / (q : Real) +
          (b₁.val : Real) / (d₁ * d₂ * d₃ : Nat)) +
        ((lowHighFinEquiv d₂ d₃ (b₂, b₃)).val : Real) /
          (d₂ * d₃ : Nat) := by
  rw [hybridSourceBetaTwo, lowHighFinEquiv_val, lowHighFinEquiv_val]
  push_cast
  field_simp [show (d₁ : Real) ≠ 0 by exact_mod_cast hd₁.ne',
    show (d₂ : Real) ≠ 0 by exact_mod_cast hd₂.ne',
    show (d₃ : Real) ≠ 0 by exact_mod_cast hd₃.ne']
  ring

/-- After multiplication by a scale divisible by `d₃`, the third-coordinate
phase disappears modulo one. -/
theorem hybridSourceBetaTwo_add_third_scale_unitAddCircle_eq
    {q d₁ d₂ d₃ D : Nat} (hd₃ : 0 < d₃) (hd₃D : d₃ ∣ D)
    (a : ReducedResidue q) (b : Fin d₁ × Fin d₂) (b₃ : Fin d₃) :
    (((D : Real) *
        (hybridSourceBetaTwo q d₁ d₂ d₃ a b +
          (b₃.val : Real) / (d₃ : Real)) : Real) : UnitAddCircle) =
      (((D : Real) * hybridSourceBetaTwo q d₁ d₂ d₃ a b : Real) :
        UnitAddCircle) := by
  have hD : D / d₃ * d₃ = D := Nat.div_mul_cancel hd₃D
  have hreal :
      (D : Real) *
          (hybridSourceBetaTwo q d₁ d₂ d₃ a b +
            (b₃.val : Real) / (d₃ : Real)) =
        (D : Real) * hybridSourceBetaTwo q d₁ d₂ d₃ a b +
          (((D / d₃) * b₃.val : Nat) : Real) := by
    have hDReal : (D : Real) = (D / d₃ : Nat) * (d₃ : Nat) := by
      exact_mod_cast hD.symm
    rw [hDReal]
    push_cast
    field_simp [show (d₃ : Real) ≠ 0 by exact_mod_cast hd₃.ne']
  rw [hreal, AddCircle.coe_add]
  have hinteger :
      (((((D / d₃) * b₃.val : Nat) : Real)) : UnitAddCircle) = 0 := by
    let n : Nat := (D / d₃) * b₃.val
    change (((n : Nat) : Real) : UnitAddCircle) = 0
    rw [AddCircle.coe_eq_zero_iff]
    refine ⟨(n : Int), ?_⟩
    simp [zsmul_eq_mul]
  rw [hinteger, add_zero]

/-- Multiplication by the enlarged decimal scale sends `beta_2` to `beta_3`
modulo one; the omitted second-coordinate term is integral. -/
theorem decimalHybridSourceBetaTwo_enlargedScale_unitAddCircle_eq
    {q d k v : Nat} (hd : 0 < d) (a : ReducedResidue q)
    (b₁ : Fin (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v)))
    (b₂ : Fin (hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v))) :
    (((((10 ^ k * 10 ^ v : Nat) : Real) *
        hybridSourceBetaTwo q
          (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v))
          (hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v))
          (hybridDenominatorThirdFactor d (10 ^ k)) a (b₁, b₂) : Real)) :
      UnitAddCircle) =
      (decimalHybridSourceBetaThree q
        (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v))
        (hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v))
        (hybridDenominatorThirdFactor d (10 ^ k)) k v a b₁ :
          UnitAddCircle) := by
  let d₁ := hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v)
  let d₂ := hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v)
  let d₃ := hybridDenominatorThirdFactor d (10 ^ k)
  let S := 10 ^ k * 10 ^ v
  have hd₁ : 0 < d₁ := hybridDenominatorFirstFactor_pos hd
  have hd₂ : 0 < d₂ := hybridDenominatorSecondFactor_pos hd
  have hd₃ : 0 < d₃ := hybridDenominatorThirdFactor_pos hd
  have hdiv : d₂ * d₃ ∣ S :=
    hybridDenominatorSecondThird_dvd_scale d (10 ^ k) (10 ^ v)
  have hS : S / (d₂ * d₃) * (d₂ * d₃) = S :=
    Nat.div_mul_cancel hdiv
  have hreal :
      (S : Real) * hybridSourceBetaTwo q d₁ d₂ d₃ a (b₁, b₂) =
        decimalHybridSourceBetaThree q d₁ d₂ d₃ k v a b₁ +
          (((S / (d₂ * d₃)) * b₂.val : Nat) : Real) := by
    rw [hybridSourceBetaTwo, decimalHybridSourceBetaThree,
      lowHighFinEquiv_val]
    change (S : Real) *
        ((a.val.val : Real) / (q : Real) +
          ((b₁.val + d₁ * b₂.val : Nat) : Real) /
            (d₁ * d₂ * d₃ : Nat)) =
      (((S * a.val.val : Nat) : Real) / (q : Real) +
          ((((S / (d₂ * d₃)) * b₁.val : Nat) : Real) / (d₁ : Real))) +
        (((S / (d₂ * d₃)) * b₂.val : Nat) : Real)
    have hSReal : (S : Real) =
        (S / (d₂ * d₃) : Nat) * ((d₂ * d₃ : Nat) : Real) := by
      exact_mod_cast hS.symm
    change (S : Real) * _ = _
    push_cast
    rw [hSReal]
    push_cast
    field_simp [show (d₁ : Real) ≠ 0 by exact_mod_cast hd₁.ne',
      show (d₂ : Real) ≠ 0 by exact_mod_cast hd₂.ne',
      show (d₃ : Real) ≠ 0 by exact_mod_cast hd₃.ne']
    ring
  have hinteger :
      (((((S / (d₂ * d₃)) * b₂.val : Nat) : Real)) : UnitAddCircle) = 0 := by
    let n : Nat := (S / (d₂ * d₃)) * b₂.val
    change (((n : Nat) : Real) : UnitAddCircle) = 0
    rw [AddCircle.coe_eq_zero_iff]
    refine ⟨(n : Int), ?_⟩
    simp [zsmul_eq_mul]
  have hcircle := congrArg (fun x : Real => (x : UnitAddCircle)) hreal
  rw [AddCircle.coe_add, hinteger, add_zero] at hcircle
  simpa only [d₁, d₂, d₃, S] using hcircle

/-- The first decimal reduced-residue equivalence represents `10^k*beta_2`
on the unit circle. -/
theorem decimalHybridFirstTwoSourceResidue_betaTwo_unitAddCircle_eq
    {q d k v u : Nat} (hq : 0 < q) (hd : 0 < d)
    (hdvd : d ∣ 10 ^ u) (hq10 : q.Coprime 10)
    (a : ReducedResidue q)
    (b : HybridMixedRadixReducedPair
      (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v))
      (hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v))) :
    (((decimalHybridFirstTwoSourceResidueEquiv hq hd hdvd hq10 (a, b)).val.val : Real) /
        ((q *
          (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v) *
            hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v)) : Nat) : Real) :
      UnitAddCircle) =
      ((((10 ^ k : Nat) : Real) *
        hybridSourceBetaTwo q
          (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v))
          (hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v))
          (hybridDenominatorThirdFactor d (10 ^ k)) a b.val : Real) :
        UnitAddCircle) := by
  rw [decimalHybridFirstTwoSourceResidue_unitAddCircle_eq hq hd hdvd hq10 a b]
  congr 1
  symm
  exact hybridSourceBetaTwo_scale_eq
    (hybridDenominatorFirstFactor_pos hd)
    (hybridDenominatorSecondFactor_pos hd)
    (hybridDenominatorThirdFactor_pos hd)
    (hybridDenominatorThirdFactor_dvd_scale d (10 ^ k)) a b.val

/-- The second decimal reduced-residue equivalence represents `beta_3` on the
unit circle. -/
theorem decimalHybridFirstResidue_betaThree_unitAddCircle_eq
    {q d k v u : Nat} (hq : 0 < q) (hd : 0 < d)
    (hdvd : d ∣ 10 ^ u) (hq10 : q.Coprime 10)
    (a : ReducedResidue q)
    (b : ReducedResidue (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v))) :
    (((decimalHybridFirstReducedResidueEquiv hq hd hdvd hq10 (a, b)).val.val : Real) /
        ((q * hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v) : Nat) : Real) :
      UnitAddCircle) =
      (decimalHybridSourceBetaThree q
        (hybridDenominatorFirstFactor d (10 ^ k) (10 ^ v))
        (hybridDenominatorSecondFactor d (10 ^ k) (10 ^ v))
        (hybridDenominatorThirdFactor d (10 ^ k)) k v a b.val :
          UnitAddCircle) := by
  simpa [decimalHybridSourceBetaThree] using
    decimalHybridFirstResidue_unitAddCircle_eq hq hd hdvd hq10 a b

end

end PrimesRestrictedDigits
