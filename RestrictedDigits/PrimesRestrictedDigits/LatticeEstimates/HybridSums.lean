import PrimesRestrictedDigits.Fourier.HybridAlternativeBound
import PrimesRestrictedDigits.Fourier.HybridSourceEstimates

/-!
# Hybrid sums in the lattice estimate

This file defines the literal `S1` and `S2` denominator sums from published Lemma 14.3 and
proves the two pointwise `S1` bounds used in Lemma 14.4.
-/

namespace PrimesRestrictedDigits

open scoped BigOperators

noncomputable section

/-- The unrestricted source decade band `G / 10 < g <= G`. -/
def latticeFactorTenBand (G : Nat) : Finset Nat :=
  (Finset.Icc 1 G).filter fun g => G < 10 * g

theorem mem_latticeFactorTenBand_iff {G g : Nat} :
    g ∈ latticeFactorTenBand G <-> 1 <= g ∧ g <= G ∧ G < 10 * g := by
  simp [latticeFactorTenBand, and_assoc]

/-- The reduced-numerator and aligned-perturbation weight at one denominator. -/
noncomputable def latticeHybridDenominatorWeight
    (digit : Fin 10) (length E q : Nat) : Real :=
  ∑ a : ReducedResidue q,
    alignedGridSum digit length (E : Real)
      ((a.val.val : Real) / (q : Real))

theorem latticeHybridDenominatorWeight_nonneg
    (digit : Fin 10) (length E q : Nat) :
    0 <= latticeHybridDenominatorWeight digit length E q := by
  exact Finset.sum_nonneg fun a _ => alignedGridSum_nonneg digit length E _

/-- The two standard hybrid branches as a function of their common scale. -/
noncomputable def latticeHybridTarget (length : Nat) (T : Real) : Real :=
  T ^ largeSieveAlpha +
    T * (((10 ^ length : Nat) : Real) ^ (-largeSieveSigma))

theorem latticeHybridTarget_mono {length : Nat} {T U : Real}
    (hT : 0 <= T) (hTU : T <= U) :
    latticeHybridTarget length T <= latticeHybridTarget length U := by
  have hpower : T ^ largeSieveAlpha <= U ^ largeSieveAlpha :=
    Real.rpow_le_rpow hT hTU largeSieveAlpha_nonneg
  have hdecay :
      0 <= (((10 ^ length : Nat) : Real) ^ (-largeSieveSigma)) := by
    positivity
  unfold latticeHybridTarget
  exact add_le_add hpower (mul_le_mul_of_nonneg_right hTU hdecay)

/-- The all-multiples enlargement used to pass a weak natural endpoint to
Lemma 10.6's strict real cutoff. -/
noncomputable def latticeHybridMultiplesSum
    (digit : Fin 10) (length d B E : Nat) : Real :=
  ∑ m ∈ Finset.Icc 1 B,
    latticeHybridDenominatorWeight digit length E (d * m)

/-- The pointwise source `S1` sum at a fixed `q'`. -/
noncomputable def latticeSOneAt
    (digit : Fin 10) (length d q G E : Nat) : Real :=
  ∑ g ∈ hybridResidualSourceDenominators G,
    latticeHybridDenominatorWeight digit length E ((q * d) * g)

/-- The literal factorized source `S2` sum. The second factor has no
coprimality-with-ten restriction. -/
noncomputable def latticeSTwo
    (digit : Fin 10) (length d Q G E : Nat) : Real :=
  ∑ x ∈ hybridResidualSourceDenominators Q ×ˢ latticeFactorTenBand G,
    latticeHybridDenominatorWeight digit length E (d * (x.1 * x.2))

theorem latticeSOneAt_eq_decimalHybridAlignedSourceBandSum
    (digit : Fin 10) (length d q G E : Nat) :
    latticeSOneAt digit length d q G E =
      decimalHybridAlignedSourceBandSum digit length q d G E := by
  unfold latticeSOneAt decimalHybridAlignedSourceBandSum
  apply Finset.sum_congr rfl
  intro g hg
  unfold latticeHybridDenominatorWeight
  have hden : (q * d) * g = (q * g) * d := by ring
  rw [hden]

private theorem latticeHybridCutoffTarget_le_four
    {length d B : Nat} (hd : 0 < d) (hB : 0 < B)
    {E : Real} (hE : 0 <= E) :
    latticeHybridTarget length
        (((((d * B + 1 : Nat) : Real) ^ 2 / d) * E)) <=
      4 * latticeHybridTarget length
        (((d * B ^ 2 : Nat) : Real) * E) := by
  have hdR : (0 : Real) < d := by exact_mod_cast hd
  have hAOne : (1 : Real) <= (d * B : Nat) := by
    exact_mod_cast Nat.mul_pos hd hB
  have hcut : ((d * B : Nat) : Real) + 1 <= 2 * (d * B : Nat) := by
    nlinarith
  have hsq :
      (((d * B : Nat) : Real) + 1) ^ 2 <=
        (2 * ((d * B : Nat) : Real)) ^ 2 := by
    nlinarith
  have hscale :
      ((((d * B + 1 : Nat) : Real) ^ 2 / d) * E) <=
        4 * (((d * B ^ 2 : Nat) : Real) * E) := by
    have hbase :
        (((d * B + 1 : Nat) : Real) ^ 2 / d) <=
          4 * ((d * B ^ 2 : Nat) : Real) := by
      apply (div_le_iff₀ hdR).2
      calc
        (((d * B + 1 : Nat) : Real) ^ 2) =
            (((d * B : Nat) : Real) + 1) ^ 2 := by norm_num
        _ <= (2 * ((d * B : Nat) : Real)) ^ 2 := hsq
        _ = 4 * ((d * B ^ 2 : Nat) : Real) * d := by
          norm_num only [Nat.cast_mul, Nat.cast_pow]
          ring
    calc
      ((((d * B + 1 : Nat) : Real) ^ 2 / d) * E) <=
          (4 * ((d * B ^ 2 : Nat) : Real)) * E :=
        mul_le_mul_of_nonneg_right hbase hE
      _ = 4 * (((d * B ^ 2 : Nat) : Real) * E) := by ring
  have hhead :
      (((((d * B + 1 : Nat) : Real) ^ 2 / d) * E) ^
          largeSieveAlpha) <=
        4 * ((((d * B ^ 2 : Nat) : Real) * E) ^ largeSieveAlpha) := by
    have hpower := Real.rpow_le_rpow (by positivity) hscale
      largeSieveAlpha_nonneg
    have hfour : (4 : Real) ^ largeSieveAlpha <= 4 := by
      calc
        (4 : Real) ^ largeSieveAlpha <= 4 ^ (1 : Real) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (by norm_num [largeSieveAlpha])
        _ = 4 := Real.rpow_one 4
    calc
      (((((d * B + 1 : Nat) : Real) ^ 2 / d) * E) ^
          largeSieveAlpha) <=
          (4 * (((d * B ^ 2 : Nat) : Real) * E)) ^
            largeSieveAlpha := hpower
      _ = 4 ^ largeSieveAlpha *
          ((((d * B ^ 2 : Nat) : Real) * E) ^ largeSieveAlpha) := by
        rw [Real.mul_rpow (by norm_num : (0 : Real) <= 4) (by positivity)]
      _ <= 4 * ((((d * B ^ 2 : Nat) : Real) * E) ^
          largeSieveAlpha) :=
        mul_le_mul_of_nonneg_right hfour (by positivity)
  have hdecay :
      0 <= (((10 ^ length : Nat) : Real) ^ (-largeSieveSigma)) := by
    positivity
  have htail := mul_le_mul_of_nonneg_right hscale hdecay
  unfold latticeHybridTarget
  nlinarith

/-- Weak upper denominator bands cost at most four when embedded into the
strict cutoff of Lemma 10.6. -/
theorem latticeHybridMultiplesSum_le_hybridBound
    (digit : Fin 10) (length d B E : Nat)
    (hd : 0 < d) (hB : 0 < B) (hE : 0 < E) :
    latticeHybridMultiplesSum digit length d B E <=
      4 * hybridConstant *
        latticeHybridTarget length
          (((d * B ^ 2 : Nat) : Real) * E) := by
  classical
  let s := (Finset.Icc 1 B).sigma fun m =>
    (Finset.univ : Finset (ReducedResidue (d * m)))
  let embed : (Σ m, ReducedResidue (d * m)) -> Nat × Nat := fun x =>
    (d * x.1, x.2.val.val)
  let cutoff : Real := ((d * B + 1 : Nat) : Real)
  let t := strictDivisibleReducedFractionSourceCarrier cutoff d
  let value : Nat × Nat -> Real := fun y =>
    alignedGridSum digit length (E : Real)
      ((y.2 : Real) / (y.1 : Real))
  have hinj : Set.InjOn embed (s : Set (Σ m, ReducedResidue (d * m))) := by
    rintro ⟨m, a⟩ hm ⟨n, b⟩ hn hmn
    have hden := congrArg Prod.fst hmn
    have hnum := congrArg Prod.snd hmn
    dsimp [embed] at hden hnum
    have hmn' : m = n := Nat.eq_of_mul_eq_mul_left hd hden
    subst n
    have hab : a = b := by
      apply Subtype.ext
      apply Fin.ext
      exact hnum
    exact Sigma.ext rfl (heq_of_eq hab)
  have hmaps : Set.MapsTo embed (s : Set (Σ m, ReducedResidue (d * m)))
      (t : Set (Nat × Nat)) := by
    rintro ⟨m, a⟩ hx
    have hm := (Finset.mem_sigma.mp hx).1
    have hmData := Finset.mem_Icc.mp hm
    have hmPos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hmData.1
    have hdenPos : 0 < d * m := Nat.mul_pos hd hmPos
    have hdenUpper : d * m <= d * B := Nat.mul_le_mul_left d hmData.2
    apply mem_strictDivisibleReducedFractionSourceCarrier_iff.mpr
    have hfloor : Nat.floor cutoff = d * B + 1 := by
      change Nat.floor (((d * B + 1 : Nat) : Real)) = d * B + 1
      exact Nat.floor_natCast _
    refine ⟨hdenPos, ?_, ?_, Nat.dvd_mul_right d m,
      a.val.isLt.le, a.property⟩
    · change d * m <= Nat.floor cutoff
      rw [hfloor]
      omega
    · dsimp [embed, cutoff]
      exact_mod_cast hdenUpper.trans_lt (Nat.lt_succ_self _)
  have himage : s.image embed ⊆ t := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    exact hmaps hx
  have hsource := divisibleDenominators_hybridEstimate digit length d hd
    (Q := cutoff) (E := (E : Real)) (by
      change (1 : Real) <= ((d * B + 1 : Nat) : Real)
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le (d * B)))
    (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hE.ne'))
  have hcutoff := latticeHybridCutoffTarget_le_four
    (length := length) hd hB (E := (E : Real)) (by positivity)
  have hconstant : 0 <= hybridConstant := by
    norm_num [hybridConstant]
  unfold latticeHybridMultiplesSum latticeHybridDenominatorWeight
  rw [Finset.sum_sigma']
  change (∑ x ∈ s, value (embed x)) <= _
  calc
    (∑ x ∈ s, value (embed x)) = ∑ y ∈ s.image embed, value y :=
      (Finset.sum_image hinj).symm
    _ <= ∑ y ∈ t, value y := by
      apply Finset.sum_le_sum_of_subset_of_nonneg himage
      intro y hy hnot
      dsimp [value]
      exact alignedGridSum_nonneg digit length E _
    _ <= hybridConstant *
        latticeHybridTarget length
          (((cutoff ^ 2 / d) * E)) := by
      simpa only [t, value, latticeHybridTarget] using hsource
    _ <= hybridConstant *
        (4 * latticeHybridTarget length
          (((d * B ^ 2 : Nat) : Real) * E)) :=
      mul_le_mul_of_nonneg_left hcutoff hconstant
    _ = 4 * hybridConstant *
        latticeHybridTarget length
          (((d * B ^ 2 : Nat) : Real) * E) := by ring

/-- Equation (14.9)'s standard hybrid shape, with the weak-endpoint loss
made explicit and only the used upper band endpoints retained. -/
theorem latticeSOneAt_le_hybridBound
    (digit : Fin 10) (length d q D Q G E : Nat)
    (hd : 0 < d) (hq : 0 < q) (hG : 0 < G) (hE : 0 < E)
    (hdD : d <= D) (hqQ : q <= Q) :
    latticeSOneAt digit length d q G E <=
      4 * hybridConstant *
        latticeHybridTarget length
          (((D * Q * G ^ 2 : Nat) : Real) * E) := by
  have hband :
      latticeSOneAt digit length d q G E <=
        latticeHybridMultiplesSum digit length (q * d) G E := by
    unfold latticeSOneAt latticeHybridMultiplesSum
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (show hybridResidualSourceDenominators G ⊆ Finset.Icc 1 G from
        Finset.filter_subset _ _)
    intro g hg hnot
    exact latticeHybridDenominatorWeight_nonneg digit length E ((q * d) * g)
  have hmultiple := latticeHybridMultiplesSum_le_hybridBound
    digit length (q * d) G E (Nat.mul_pos hq hd) hG hE
  have hscaleNat : q * d * G ^ 2 <= D * Q * G ^ 2 := by
    have hqd : q * d <= Q * D := Nat.mul_le_mul hqQ hdD
    calc
      q * d * G ^ 2 <= Q * D * G ^ 2 := Nat.mul_le_mul_right _ hqd
      _ = D * Q * G ^ 2 := by ring
  have hscaleReal :
      (((q * d * G ^ 2 : Nat) : Real) * E) <=
        (((D * Q * G ^ 2 : Nat) : Real) * E) := by
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast hscaleNat) (Nat.cast_nonneg E)
  have htarget := latticeHybridTarget_mono (length := length)
    (by positivity) hscaleReal
  have hcoefficient : 0 <= 4 * hybridConstant := by
    norm_num [hybridConstant]
  calc
    latticeSOneAt digit length d q G E <=
        latticeHybridMultiplesSum digit length (q * d) G E := hband
    _ <= 4 * hybridConstant *
        latticeHybridTarget length
          (((q * d * G ^ 2 : Nat) : Real) * E) := hmultiple
    _ <= 4 * hybridConstant *
        latticeHybridTarget length
          (((D * Q * G ^ 2 : Nat) : Real) * E) :=
      mul_le_mul_of_nonneg_left htarget hcoefficient

/-- Equation (14.11)'s Alternative Hybrid Bound for the literal pointwise
`S1` sum. -/
theorem latticeSOneAt_le_alternativeHybridBound
    (loss : Nat) (digit : Fin 10)
    {length dLength eLength q d u Q G : Nat}
    (hscale : dLength + eLength <= length + loss)
    (hq : 0 < q) (hd : 0 < d) (hdD : d <= 10 ^ dLength)
    (hdvd : d ∣ 10 ^ u) (hq10 : q.Coprime 10) (hqQ : q <= Q) :
    let C : Real := ((10 ^ loss : Nat) : Real)
    let D : Real := ((10 ^ dLength : Nat) : Real)
    let E : Real := ((10 ^ eLength : Nat) : Real)
    let Y : Real := ((10 ^ length : Nat) : Real)
    let L : Real := ((Q * G ^ 2 : Nat) : Real)
    latticeSOneAt digit length d q G (10 ^ eLength) <=
      (72000 * largeSieveSamplingConstant ^ 2 * (1 + 2 * C) ^ 2 *
          (1 + C) * (3 + C ^ largeSieveSigma)) *
        ((D * E) ^ largeSieveAlpha * L ^ hybridResidualGrowth +
          E ^ (5 / 6 : Real) * D ^ (3 / 2 : Real) * L /
            Y ^ hybridResidualHalfDecay) := by
  rw [latticeSOneAt_eq_decimalHybridAlignedSourceBandSum]
  exact decimalHybridAlignedSourceBandSum_le_publishedPowers
    loss digit hscale hq hd hdD hdvd hq10 hqQ

end

end PrimesRestrictedDigits
