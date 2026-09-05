

import MathlibNt.AnalyticNumberTheory.LargeSieve.PrincipalLambdaGlobalReduction
import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanDirectAPNormalizedAssembly

/-!
 # Standard BV through a low/high primitive-conductor split

This module keeps three logically different inputs separate.

* `PrimitivePrefixSiegelWalfiszSource` is the minimal low-conductor source: a
  pointwise bound for a primitive twisted Λ prefix.  It is not a BV statement.
* Above `R = floor(log(N)^C)` all direct means remain literal finite sums.
* The Standard-BV endpoint is obtained only after the principal, prime-power,
  and partial-summation physical terms have all been paid.

The weighted-Cauchy lemma below records the only automatic effect of deleting
conductors `≤ R`: the outer factor is the harmonic tail `sum_{R<d≤Q} 1/d`.
There is no factor `R⁻¹`.  Consequently the needed inverse-log saving is
located explicitly in `VaughanHighConductorHybridSaving`, not attributed to
Cauchy or to the choice of the modulus exponent `B`.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset Filter
open scoped BigOperators ArithmeticFunction Topology

noncomputable section

/-- The literal low/high separator `R = floor(log(N)^C)`. -/
def logConductorThreshold (N C : ℕ) : ℕ :=
  Nat.floor (Real.log (N : ℝ) ^ C)

/-- Primitive conductors from two through the logarithmic separator. -/
def lowConductorSet (N Q C : ℕ) : Finset ℕ :=
  (Finset.Icc 2 Q).filter fun d => d ≤ logConductorThreshold N C

/-- Primitive conductors strictly above the logarithmic separator. -/
def highConductorSet (N Q C : ℕ) : Finset ℕ :=
  (Finset.Icc 2 Q).filter fun d => logConductorThreshold N C < d

lemma lowConductorSet_disjoint_highConductorSet (N Q C : ℕ) :
    Disjoint (lowConductorSet N Q C) (highConductorSet N Q C) := by
  apply Finset.disjoint_left.2
  intro d hdL hdH
  simp only [lowConductorSet, highConductorSet, Finset.mem_filter] at hdL hdH
  omega

lemma lowConductorSet_union_highConductorSet (N Q C : ℕ) :
    lowConductorSet N Q C ∪ highConductorSet N Q C = Finset.Icc 2 Q := by
  ext d
  simp only [lowConductorSet, highConductorSet, Finset.mem_union,
    Finset.mem_filter]
  constructor
  · rintro (h | h) <;> exact h.1
  · intro h
    by_cases hd : d ≤ logConductorThreshold N C
    · exact Or.inl ⟨h, hd⟩
    · exact Or.inr ⟨h, by omega⟩

/-- Direct conductor sum on an arbitrary conductor set. -/
def directConductorMeanOn (a : ℤ → ℂ) (N Q : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ d ∈ S, directConductorWeight Q d *
    ∑ ψ : PrimitiveCharacter d, primitivePrefixAmplitude a N d ψ

/-- Low-conductor physical term after exact all-character regrouping. -/
def lowConductorPhysical (N Q C : ℕ) : ℝ :=
  directConductorMeanOn vonMangoldtIntegerCoeff N Q (lowConductorSet N Q C)

/-- High-conductor physical term.  No estimate is built into this definition. -/
def highConductorPhysical (N Q C : ℕ) : ℝ :=
  directConductorMeanOn vonMangoldtIntegerCoeff N Q (highConductorSet N Q C)

/-- Exact low/high partition of the conductor-regrouped direct mean. -/
theorem directConductorMean_low_high (a : ℤ → ℂ) (N Q C : ℕ) :
    (∑ d ∈ Finset.Icc 2 Q, directConductorWeight Q d *
      ∑ ψ : PrimitiveCharacter d, primitivePrefixAmplitude a N d ψ) =
      directConductorMeanOn a N Q (lowConductorSet N Q C) +
        directConductorMeanOn a N Q (highConductorSet N Q C) := by
  unfold directConductorMeanOn
  rw [← Finset.sum_union (lowConductorSet_disjoint_highConductorSet N Q C)]
  rw [lowConductorSet_union_highConductorSet]

/-- Minimal Siegel--Walfisz primitive-prefix source.  It controls each primitive
Λ twist at conductor `d ≤ log(N)^C`; no modulus average and no BV conclusion
occurs in its type.  The decay exponent `D` is chosen after `C`. -/
def PrimitivePrefixSiegelWalfiszSource : Prop :=
  ∀ C D : ℕ, ∃ K : ℝ, 0 < K ∧
    ∀ᶠ N : ℕ in Filter.atTop, 2 ≤ N →
      ∀ d ∈ Finset.Icc 2 (logConductorThreshold N C),
        ∀ ψ : PrimitiveCharacter d,
          primitivePrefixAmplitude vonMangoldtIntegerCoeff N d ψ ≤
            K * (N : ℝ) / Real.log (N : ℝ) ^ D

/-- The exact finite arithmetic mass multiplying a pointwise SW estimate. -/
def lowConductorArithmeticMass (N Q C : ℕ) : ℝ :=
  ∑ d ∈ lowConductorSet N Q C,
    directConductorWeight Q d * Fintype.card (PrimitiveCharacter d)

/-- A primitive-prefix SW bound pays the low-conductor physical term with its
literal conductor multiplicity and character count. -/
theorem lowConductorPhysical_le_of_primitivePrefix
    (N Q C : ℕ) (X : ℝ)
    (hX : 0 ≤ X)
    (hSW : ∀ d ∈ lowConductorSet N Q C,
      ∀ ψ : PrimitiveCharacter d,
        primitivePrefixAmplitude vonMangoldtIntegerCoeff N d ψ ≤ X) :
    lowConductorPhysical N Q C ≤ lowConductorArithmeticMass N Q C * X := by
  unfold lowConductorPhysical directConductorMeanOn lowConductorArithmeticMass
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro d hd
  have hw : 0 ≤ directConductorWeight Q d := by
    unfold directConductorWeight
    exact Finset.sum_nonneg fun _ _ => by positivity
  calc
    directConductorWeight Q d *
        (∑ ψ : PrimitiveCharacter d,
          primitivePrefixAmplitude vonMangoldtIntegerCoeff N d ψ) ≤
        directConductorWeight Q d *
          (∑ _ψ : PrimitiveCharacter d, X) := by
            exact mul_le_mul_of_nonneg_left
              (Finset.sum_le_sum fun ψ _ => hSW d hd ψ) hw
    _ = (directConductorWeight Q d *
          Fintype.card (PrimitiveCharacter d)) * X := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
            ring

/-- AP-normalized primitive direct mean restricted to a conductor set. -/
def apNormalizedPrimitiveMeanOn
    (a : ℤ → ℂ) (N : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ d ∈ S, ((d.totient : ℝ)⁻¹) *
    ∑ ψ : PrimitiveCharacter d, primitivePrefixAmplitude a N d ψ

/-- Square-large-sieve ledger on exactly the same conductor set. -/
def primitivePrefixSquareLedgerOn
    (a : ℤ → ℂ) (N : ℕ) (S : Finset ℕ) : ℝ :=
  ∑ d ∈ S, ((d : ℝ) / (d.totient : ℝ)) *
    ∑ ψ : PrimitiveCharacter d,
      primitiveCharacterPrefixMaxSquare a 0 N d ψ

/-- The genuine weighted-Cauchy outer payment after deleting conductors `≤ R`. -/
def highConductorHarmonicFactor (Q R : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc (R + 1) Q, ((d : ℝ)⁻¹)

/-- Weighted Cauchy on the high-conductor interval.  The lower cutoff produces
exactly the harmonic tail, while `d/φ(d)` occurs only in the square ledger. -/
theorem apNormalizedPrimitiveMeanOn_high_sq_le
    (a : ℤ → ℂ) (N Q R : ℕ)
    (hcard : ∀ d ∈ Finset.Icc (R + 1) Q,
      Fintype.card (PrimitiveCharacter d) ≤ d.totient) :
    apNormalizedPrimitiveMeanOn a N (Finset.Icc (R + 1) Q) ^ 2 ≤
      highConductorHarmonicFactor Q R *
        primitivePrefixSquareLedgerOn a N (Finset.Icc (R + 1) Q) := by
  let T : ℕ → ℝ := fun d => ((d.totient : ℝ)⁻¹) *
    ∑ ψ : PrimitiveCharacter d, primitivePrefixAmplitude a N d ψ
  let B : ℕ → ℝ := fun d => ((d : ℝ) / (d.totient : ℝ)) *
    ∑ ψ : PrimitiveCharacter d,
      primitiveCharacterPrefixMaxSquare a 0 N d ψ
  have hTB (d : ℕ) (hd : d ∈ Finset.Icc (R + 1) Q) :
      (d : ℝ) * T d ^ 2 ≤ B d := by
    have hd0 : 0 < d := by
      have := (Finset.mem_Icc.mp hd).1
      omega
    have hφ : (0 : ℝ) < d.totient := by
      exact_mod_cast Nat.totient_pos.mpr hd0
    let A : PrimitiveCharacter d → ℝ := fun ψ => primitivePrefixAmplitude a N d ψ
    have hs := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (PrimitiveCharacter d))) (f := A)
    have hs' : (∑ ψ : PrimitiveCharacter d, A ψ) ^ 2 ≤
        (d.totient : ℝ) * ∑ ψ : PrimitiveCharacter d, A ψ ^ 2 := by
      refine hs.trans ?_
      gcongr
      exact_mod_cast hcard d hd
    have hamp : (∑ ψ : PrimitiveCharacter d, A ψ ^ 2) =
        ∑ ψ : PrimitiveCharacter d,
          primitiveCharacterPrefixMaxSquare a 0 N d ψ := by
      apply Finset.sum_congr rfl
      intro ψ hψ
      exact primitivePrefixAmplitude_sq a N d ψ
    dsimp [T, B]
    rw [hamp] at hs'
    rw [div_eq_mul_inv]
    field_simp
    nlinarith
  have hsplit : apNormalizedPrimitiveMeanOn a N (Finset.Icc (R + 1) Q) =
      ∑ d ∈ Finset.Icc (R + 1) Q,
        (Real.sqrt (d : ℝ))⁻¹ * (Real.sqrt (d : ℝ) * T d) := by
    unfold apNormalizedPrimitiveMeanOn
    apply Finset.sum_congr rfl
    intro d hd
    have hd0N : 0 < d := by
      have := (Finset.mem_Icc.mp hd).1
      omega
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd0N
    have hsne : Real.sqrt (d : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hd0
    dsimp [T]
    field_simp
  rw [hsplit]
  refine (Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc (R + 1) Q)
    (fun d => (Real.sqrt (d : ℝ))⁻¹)
    (fun d => Real.sqrt (d : ℝ) * T d)).trans ?_
  have hfirst :
      (∑ d ∈ Finset.Icc (R + 1) Q, (Real.sqrt (d : ℝ))⁻¹ ^ 2) =
        highConductorHarmonicFactor Q R := by
    unfold highConductorHarmonicFactor
    apply Finset.sum_congr rfl
    intro d hd
    rw [inv_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ d)]
  rw [hfirst]
  apply mul_le_mul_of_nonneg_left
  · unfold primitivePrefixSquareLedgerOn
    apply Finset.sum_le_sum
    intro d hd
    rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ d)]
    exact hTB d hd
  · unfold highConductorHarmonicFactor
    positivity

/-- Removing low conductors only deletes positive harmonic summands. -/
theorem highConductorHarmonicFactor_le (Q R : ℕ) :
    highConductorHarmonicFactor Q R ≤ conductorHarmonicFactor Q := by
  unfold highConductorHarmonicFactor conductorHarmonicFactor
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.Icc_subset_Icc_left (by omega)
  · intro d hd hnot
    positivity

/-- If the high range is nonempty, its Cauchy factor still contains the final
summand `1/Q`.  Thus Cauchy supplies no automatic power of `R`; any useful
inverse-log gain must enter the high-conductor analytic estimate itself. -/
theorem inv_Q_le_highConductorHarmonicFactor
    {Q R : ℕ} (hRQ : R < Q) :
    ((Q : ℝ)⁻¹) ≤ highConductorHarmonicFactor Q R := by
  unfold highConductorHarmonicFactor
  apply Finset.single_le_sum (f := fun d : ℕ => ((d : ℝ)⁻¹))
  · intro d hd
    positivity
  · exact Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩

/-- Exact high-conductor Type-I direct mean. -/
def highConductorVaughanTypeIMean (N Q C u v : ℕ) : ℝ :=
  apNormalizedPrimitiveMeanOn
    (vaughanTypeICoeff vaughanUnitIntegerCoeff u v) N
    (highConductorSet N Q C)

/-- Exact high-conductor Type-II direct mean. -/
def highConductorVaughanTypeIIMean (N Q C u v : ℕ) : ℝ :=
  apNormalizedPrimitiveMeanOn
    (vaughanTypeIICoeff vaughanUnitIntegerCoeff u v) N
    (highConductorSet N Q C)

/-- Exact high-conductor small Vaughan mean. -/
def highConductorVaughanSmallMean (N Q C v : ℕ) : ℝ :=
  apNormalizedPrimitiveMeanOn
    (vaughanSmallCoeff vaughanUnitIntegerCoeff v) N
    (highConductorSet N Q C)

/-- The missing analytic saving is frozen at its real location: the sum of the
three exact high-conductor Vaughan means.  This is not a BV conclusion. -/
def VaughanHighConductorHybridSaving
    (N Q C u v : ℕ) (X : ℝ) : Prop :=
  highConductorVaughanTypeIMean N Q C u v +
      highConductorVaughanTypeIIMean N Q C u v +
      highConductorVaughanSmallMean N Q C v ≤ X

/-- Exact physical terms appearing after principal reduction and discrete
partial summation.  `nonprincipal` is where the low/high conductor route feeds
in; all other lanes are already concrete. -/
structure StandardBVPhysicalTerms where
  nonprincipal : ℝ
  principal : ℝ
  principalBad : ℝ
  primePower : ℝ
  chebyshevToLi : ℝ

/-- Literal total physical payment after the Abel amplifier. -/
def StandardBVPhysicalTerms.total (P : StandardBVPhysicalTerms) (abel : ℝ) : ℝ :=
  abel * (P.nonprincipal + P.principal + P.principalBad + P.primePower) +
    P.chebyshevToLi

/-- Exact nonprincipal character term produced by the finite AP
orthogonality theorem. -/
def nonprincipalLambdaPhysical (N Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℝ)⁻¹) *
    ∑ χ ∈ nonprincipalCharacters q,
      lambdaCharacterPrefixMaxAmplitude N q χ

/-- Exact principal modulus-one term, with its `1/φ(q)` transport retained. -/
def principalGlobalPhysical (N Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℝ)⁻¹) *
    principalLambdaPrefixMaxError N 1

/-- Exact bad-prime-power deletion from the principal characters. -/
def principalBadPhysical (N Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℝ)⁻¹) *
    ((Nat.log2 q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ))

/-- Exact higher-prime-power correction in the `ψ`-to-prime passage. -/
def primePowerPhysical (N Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, lambdaPrimePowerCorrectionPrefixMaxError N q

/-- Exact scalar discrete-main-to-`li` source after summing `1/φ(q)`. -/
def chebyshevToLiPhysical (N Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℝ)⁻¹) *
    globalChebyshevToLiSourcePrefixMaxError N

/-- The literal five-lane packet supplied by character orthogonality,
principal reduction, prime-power removal, and partial summation. -/
def concreteStandardBVPhysicalTerms (N Q : ℕ) : StandardBVPhysicalTerms where
  nonprincipal := nonprincipalLambdaPhysical N Q
  principal := principalGlobalPhysical N Q
  principalBad := principalBadPhysical N Q
  primePower := primePowerPhysical N Q
  chebyshevToLi := chebyshevToLiPhysical N Q

/-- The proven finite principal/prime-power/partial-summation connector.  No
analytic estimate is used here. -/
theorem sum_standardPrimeAPPrefixMaxError_le_concretePhysical
    (N Q : ℕ) (hN : 2 ≤ N) :
    (∑ q ∈ Finset.Icc 1 Q,
      MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPPrefixMaxError N q) ≤
      (concreteStandardBVPhysicalTerms N Q).total
        (discreteAbelAmplifierPrefixMax N) := by
  have hsplit :
      (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℝ)⁻¹) *
        (principalLambdaPrefixMaxError N 1 +
          (Nat.log2 q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ) +
          ∑ χ ∈ nonprincipalCharacters q,
            lambdaCharacterPrefixMaxAmplitude N q χ)) =
        nonprincipalLambdaPhysical N Q + principalGlobalPhysical N Q +
          principalBadPhysical N Q := by
    unfold nonprincipalLambdaPhysical principalGlobalPhysical principalBadPhysical
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    ring
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 Q,
        (discreteAbelAmplifierPrefixMax N *
          ((q.totient : ℝ)⁻¹ *
              (principalLambdaPrefixMaxError N 1 +
                (Nat.log2 q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log (N : ℝ) +
                ∑ χ ∈ nonprincipalCharacters q,
                  lambdaCharacterPrefixMaxAmplitude N q χ) +
            lambdaPrimePowerCorrectionPrefixMaxError N q) +
          (q.totient : ℝ)⁻¹ * globalChebyshevToLiSourcePrefixMaxError N) := by
          apply Finset.sum_le_sum
          intro q hq
          exact standardPrimeAPPrefixMaxError_le_global_principal_bridge
            (Finset.mem_Icc.mp hq).1 hN
    _ = (concreteStandardBVPhysicalTerms N Q).total
        (discreteAbelAmplifierPrefixMax N) := by
          change _ =
            discreteAbelAmplifierPrefixMax N *
                (nonprincipalLambdaPhysical N Q + principalGlobalPhysical N Q +
                  principalBadPhysical N Q + primePowerPhysical N Q) +
              chebyshevToLiPhysical N Q
          unfold primePowerPhysical chebyshevToLiPhysical
          rw [Finset.sum_add_distrib, ← Finset.mul_sum,
            Finset.sum_add_distrib, hsplit]

/-- The remaining finite normalization connector needed to feed the conductor
split into the preceding concrete packet.  Its statement is an inequality
between literal finite means, not an analytic or BV hypothesis. -/
def LambdaToLowHighConductorConnector (N Q C : ℕ) : Prop :=
  nonprincipalLambdaPhysical N Q ≤
    2 * (lowConductorPhysical N Q C + highConductorPhysical N Q C) +
      2 * directConductorCorrectionMean vonMangoldtIntegerCoeff N Q

/-- At a fixed `N,Q`, a Standard-BV estimate follows once every named physical
lane is dominated and their literal total fits the target.  The theorem does
not allow the modulus exponent `B` to pay a `Q`-independent `N` term: such a
term remains in `P.nonprincipal` until the Vaughan hybrid hypothesis saves it. -/
theorem standardBV_sufficient_at
    (A : ℝ) (B C N Q : ℕ) (K : ℝ)
    (P : StandardBVPhysicalTerms)
    (hQ : Q = MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N B)
    (_hconnector : LambdaToLowHighConductorConnector N Q C)
    (hcomponents :
      (∑ q ∈ Finset.Icc 1 Q,
        MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPPrefixMaxError N q) ≤
        P.total (discreteAbelAmplifierPrefixMax N))
    (hpay : P.total (discreteAbelAmplifierPrefixMax N) ≤
      K * (N : ℝ) / Real.log (N : ℝ) ^ A) :
    (∑ q ∈ Finset.Icc 1
        (MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N B),
      MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPPrefixMaxError N q) ≤
        K * (N : ℝ) / Real.log (N : ℝ) ^ A := by
  subst Q
  exact hcomponents.trans hpay

/-- Quantifier-faithful sufficient interface for Standard BV.  For each target
`A`, choose the conductor exponent `C`; then choose the modulus exponent `B`.
The producer must pay all five physical lanes uniformly for large `N`.
This ordering makes explicit that increasing `B` cannot repair a missing
`Q`-independent high-conductor `N` saving. -/
def StandardBVSufficient : Prop :=
  ∀ A : ℝ, 0 < A →
    ∃ C : ℕ, ∃ B : ℕ, ∃ K : ℝ, 0 < K ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        ∃ P : StandardBVPhysicalTerms,
          LambdaToLowHighConductorConnector N
              (MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N B) C ∧
          (∑ q ∈ Finset.Icc 1
              (MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N B),
            MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPPrefixMaxError N q) ≤
              P.total (discreteAbelAmplifierPrefixMax N) ∧
          P.total (discreteAbelAmplifierPrefixMax N) ≤
            K * (N : ℝ) / Real.log (N : ℝ) ^ A

/-- The sufficient interface has exactly the usual Standard-BV conclusion. -/
theorem standardBV_of_sufficient (h : StandardBVSufficient) :
    ∀ A : ℝ, 0 < A →
      ∃ C : ℕ, ∃ B : ℕ, ∃ K : ℝ, 0 < K ∧
        ∀ᶠ N : ℕ in Filter.atTop,
          (∑ q ∈ Finset.Icc 1
              (MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N B),
            MathlibNt.SieveTheory.BombieriVinogradov.standardPrimeAPPrefixMaxError N q) ≤
              K * (N : ℝ) / Real.log (N : ℝ) ^ A := by
  intro A hA
  obtain ⟨C, B, K, hK, hN⟩ := h A hA
  refine ⟨C, B, K, hK, ?_⟩
  filter_upwards [hN] with N hPN
  obtain ⟨P, _hconnector, hcomp, hpay⟩ := hPN
  exact hcomp.trans hpay

end

end AnalyticNumberTheory.LargeSieve
