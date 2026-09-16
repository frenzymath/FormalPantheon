import PrimesRestrictedDigits.Fourier.RationalEndpointUpper

/-!
# Fixed-denominator rational cosine upper

The d20 Taylor upper is represented by one signed integer numerator over a
common denominator. This avoids repeated normalization of large rationals in
later finite certificates.
-/

namespace PrimesRestrictedDigits

def rationalCosineUpper20D20BaseDenominator : Nat := 10 ^ 50

def rationalCosineUpper20D20FixedDenominator : Nat :=
  0xa603e0423fe5b33eb8d996f645047de41a71d522a35001a7fcfc113fca3efbd1e3c54d0877eae170a1aafc09bd4789bd86809fdd1494248af6b7ae3beab255937509d9cfd8f36227bc03e11f55c4281d474999bde1fda532e409791b229e61c58c74fbf9ca1b298b0343e57d47554424678a9ba60a691f6c13388db2933aa18be0b69e8d99f20ec00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

theorem rationalCosineUpper20D20FixedDenominator_eq :
    rationalCosineUpper20D20FixedDenominator =
      Nat.factorial 18 * rationalCosineUpper20D20BaseDenominator ^ 9 := by
  norm_num [rationalCosineUpper20D20FixedDenominator,
    rationalCosineUpper20D20BaseDenominator]

private def polynomialConstant : Int :=
  0xa603e05e1a3179c66db7643a7f8a5f1aac695f36cbf4c155dfce1f3e8fda30c311c4b1fe3c09b6312a41a0ec7cef2ba25437415ae8c538d8797d8823c6ec5cc7b9c360018d6ff8f59c318f77eedd4385a38533d3d9a586debaad3cd578af6a066842b8c82fc3a3df0be0ae76d6487ba00d28d6758077b55dbe3b6d641da38ea304afb991caf3d126c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

private def polynomialCoefficient1 : Int :=
  0x57f76c9b47b8a192755ffd7e1d295bfdfed9f453dc8c662138b0ff2bb8bca733225696faeb8a0562fed08d9baaeb8df6a49523166bbbca00aae0b4334827c9c0c1db72a53d864b4ed2dacf9cc3540c812e0672b0578e8ca91f669e70daabfab7314b3ebf41c8c856f70a4b61637672ad6afbf8ba5e47f41a5452f5fcae0916ab4c24c285601a67d0385800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

private def polynomialCoefficient2 : Int :=
  0x7c4baad4f3c56f576df1e1120b2650594790ff8d9797449488033799904aa77972dc8276f2f11e342c96e14864db04b1602697a7408973ab43871986d9509f59548d53715fbd7257b7cf95b8ee720169229a5f77b862702d4216993241e5be3b691f68fb1ceea5dac12e22aa877e0f5a0a8906e7737e17169430a5265515f1a222cd3a22553fe2cff60355ac80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000

private def polynomialCoefficient3 : Int :=
  0x4640517519e34a707c93a1dbe81b01a3917ff0e4d9f5f8ad5b1d7257b7631b064424fda518d2e981a780f8ef5c80c12da5925ae407c72476b9a14560a9f907fbc5fbd9a8698689e1928418afc9b5456f88bccc8ea4047679029acba500a43666306891db71571d7ce912973edcbc26cd4cc04cb95d4cc35b1eb37a150a53d0c7f777a0229c917ef9a3d3f66fc37000000000000000000000000000000000000000000000000000000000000000000000000000000000

private def polynomialCoefficient4 : Int :=
  0x154558cbc814b03a9e5ec296f6922ba20aab22c88e07b2b6916c0ea826f1e81c69810bfdf2792ca487bf016c229e1323515ae359ba4fc28ac1f937cd4bcee63a8bedb65486184784115ef19b258c87a3810976148a6bcf027af6e24ee13dde0fd561cdaed16ad0f4548af5aa6f5f2e539d004ca5322ccb753e8c13315ddc0d2592102d0fac1ec6cbcadb053dbeb6a1b708000000000000000000000000000000000000000000000000000000000000000000

private def polynomialCoefficient5 : Int :=
  0x401e4f404b77fc3cb2901b395a96f61cb32fa6174d90c7ce2e18e8d3181065b7dff20e9c4f5662366877117b0d6b812d56e9ee32cd59aeaa4f798430760d0c36722bdc9892728ebcec14e2d42767d4f2136ba254d9fd3be2d9c93cf8d95e36263392bea4505019846595c9c18b163aad48cd439441c8530ebc5461116cdf0aaf03898af2a36a980990e5a4b1571a4b2a95000000000000000000000000000000000000000000000000000000000

private def polynomialCoefficient6 : Int :=
  0x83c7963bfcf019bfe9be4b41bb9bdfad56b4186d45c6c990550d4ac066e058a2c4c12db434a278d6e557eb1445cb0aab5c28691217797d1d98e1ce9adfd5c4f0eac8b3aa4142fec519c074beb375865934dc0bc17fc359f81830e70300b808785fa0fe33b1896cea8d644d73a4e51a9a816f0d7f659633bc481d2fcb2d9c0231509155c6895846f39bd30d3003cd12e7516a9d95000000000000000000000000000000000000000000

private def polynomialCoefficient7 : Int :=
  0xc46f15c65ff00e6e9e5ffd15eccae720f5f9b5455bf5f2d43fa03e438456faa883d80b85d1e65eda661f7d8f9d9fcc8a1419fb5f5a7eb465650ebe03f1b8498ce14ed6ff7d4c3ff76de25ebcdee5bb552983f54fab8c29e616883e6d5ef5c8ef244dc1b9a09b2ef9ca2a25d3c826ff90f4d6d8ad0478ae7674f82ac39d1a842b6010ed42d7b7ecbfd766235a78b940b5ba7cd01e000000000000000000000000000000000

private def polynomialCoefficient8 : Int :=
  0xde0c05b3a4edd3182aaeb62728835f86aa41af28436291a7befe87738a03bee97b35aaa314ad3c2e6db30de5ad1b04e316b5b50f61ffacbdf8a21e9b7f6fa8a3b4631ce6c001f425e6829e9abfabdd1d80c0bf0803588e28913d194897b324cf3eb2aeae11c40d6b1ba4703e2a72d416be6cf819084d5772739c95a992a3439282696996e76ab52acc96817f0decc72282c98874ba421d880000000000000000

private def polynomialCoefficient9 : Int :=
  0xc4dccc9d580742c24a9435d62c2bb6dec82c8c9f1c4ddd10dfa13416bba64f848e6335537bc462af502ad0627b224302ec001f89d72959c3175142e352af367e8c9c337a6d72a927b4603eda923b118ab77a6992163291b1e615c45c164b498ff8f4e6fc1c05d50238e0a165ddd503881f3e37d817430637b20dd4dd62be335ae6009cb659f6cf94898ff3377cffe148608fc0fd73c689000000000

/-- Signed common-denominator numerator for the established d20 cosine upper. -/
def rationalCosineUpper20D20FixedNumerator (x : Int) : Int :=
  let u := x ^ 2
  polynomialConstant + u *
    (-polynomialCoefficient1 + u *
      (polynomialCoefficient2 + u *
        (-polynomialCoefficient3 + u *
          (polynomialCoefficient4 + u *
            (-polynomialCoefficient5 + u *
              (polynomialCoefficient6 + u *
                (-polynomialCoefficient7 + u *
                  (polynomialCoefficient8 - u * polynomialCoefficient9))))))))

def centeredResidual100000 (n : Int) : Int :=
  (n + 50000) % 100000 - 50000

theorem centeredRationalPart_eq_fixedResidual (n : Int) :
    centeredRationalPart n 100000 =
      (centeredResidual100000 n : Rat) / 100000 := by
  have h := centeredResidualNumerator_eq_emod_sub_half n 100000
  norm_num at h
  rw [centeredRationalPart, centeredResidual100000, ← h]
  norm_num

theorem centeredResidual100000_bounds (n : Int) :
    -50000 ≤ centeredResidual100000 n ∧ centeredResidual100000 n < 50000 := by
  have h := centeredResidualNumerator_bounds n 100000 (by norm_num)
    (by exact ⟨50000, by norm_num⟩)
  have heq := centeredResidualNumerator_eq_emod_sub_half n 100000
  norm_num at h heq
  rw [centeredResidual100000, ← heq]
  omega

theorem rationalCosineUpper20D20Rat_eq_fixedNumerator (x : Int) :
    rationalCosineUpper20D20Rat ((x : Rat) / 100000) =
      (rationalCosineUpper20D20FixedNumerator x : Rat) /
        rationalCosineUpper20D20FixedDenominator := by
  simp only [rationalCosineUpper20D20Rat, cosinePolynomial20UpperRat]
  norm_num [rationalCosineUpper20D20FixedNumerator,
    polynomialConstant, polynomialCoefficient1, polynomialCoefficient2,
    polynomialCoefficient3, polynomialCoefficient4, polynomialCoefficient5,
    polynomialCoefficient6, polynomialCoefficient7, polynomialCoefficient8,
    polynomialCoefficient9,
    rationalCosineUpper20D20BaseDenominator,
    rationalCosineUpper20D20FixedDenominator]
  ring

theorem rationalCosineUpper20D20FixedNumerator_neg_half :
    rationalCosineUpper20D20FixedNumerator (-50000) < 0 := by
  norm_num [rationalCosineUpper20D20FixedNumerator,
    polynomialConstant, polynomialCoefficient1, polynomialCoefficient2,
    polynomialCoefficient3, polynomialCoefficient4, polynomialCoefficient5,
    polynomialCoefficient6, polynomialCoefficient7, polynomialCoefficient8,
    polynomialCoefficient9,
    rationalCosineUpper20D20BaseDenominator,
    rationalCosineUpper20D20FixedDenominator]

end PrimesRestrictedDigits
