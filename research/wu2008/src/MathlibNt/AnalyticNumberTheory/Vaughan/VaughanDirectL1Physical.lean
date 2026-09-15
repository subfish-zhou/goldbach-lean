

import MathlibNt.AnalyticNumberTheory.LargeSieve.StandardBVSquareMeanToL1Dyadic
import MathlibNt.AnalyticNumberTheory.LargeSieve.DirectConductorWeight

/-!
 # Direct L¹ Vaughan route at the physical scale

This module deliberately does not pass through a square mean for the complete
von Mangoldt coefficient sequence.  It proves the finite character, conductor,
and Vaughan assembly for the literal prefix maxima.  The main unresolved
analytic interfaces are the Type-I and Type-II *mean values themselves*; the
small/correction terms remain visible, while the reciprocal-totient conductor
weight is discharged by a separate unconditional finite-arithmetic module.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators

noncomputable section

/-- Unsquared primitive-character prefix maximum. -/
def primitivePrefixAmplitude (a : ℤ → ℂ) (N q : ℕ)
    (χ : PrimitiveCharacter q) : ℝ :=
  Real.sqrt (primitiveCharacterPrefixMaxSquare a 0 N q χ)

lemma primitivePrefixAmplitude_nonneg (a : ℤ → ℂ) (N q : ℕ)
    (χ : PrimitiveCharacter q) : 0 ≤ primitivePrefixAmplitude a N q χ :=
  Real.sqrt_nonneg _

lemma primitivePrefixAmplitude_sq (a : ℤ → ℂ) (N q : ℕ)
    (χ : PrimitiveCharacter q) :
    primitivePrefixAmplitude a N q χ ^ 2 =
      primitiveCharacterPrefixMaxSquare a 0 N q χ := by
  apply Real.sq_sqrt
  exact primitiveCharacterPrefixMaxSquare_nonneg a 0 N q χ

/-- The classical direct primitive L¹ mean.  This, rather than a square mean of
an already collected length-`N` coefficient sequence, is the proper target of
Vaughan's Type-I/II argument. -/
def directPrimitiveMean (a : ℤ → ℂ) (N Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
    ∑ χ : PrimitiveCharacter q, primitivePrefixAmplitude a N q χ

lemma directPrimitiveMean_nonneg (a : ℤ → ℂ) (N Q : ℕ) :
    0 ≤ directPrimitiveMean a N Q := by
  unfold directPrimitiveMean primitivePrefixAmplitude
  positivity

/-- The three genuine Vaughan means. -/
def directVaughanTypeIMean (N Q u v : ℕ) : ℝ :=
  directPrimitiveMean (vaughanTypeICoeff vaughanUnitIntegerCoeff u v) N Q

def directVaughanTypeIIMean (N Q u v : ℕ) : ℝ :=
  directPrimitiveMean (vaughanTypeIICoeff vaughanUnitIntegerCoeff u v) N Q

def directVaughanSmallMean (N Q v : ℕ) : ℝ :=
  directPrimitiveMean (vaughanSmallCoeff vaughanUnitIntegerCoeff v) N Q

private lemma amplitude_three_piece
    {x a b c : ℝ} (hx : 0 ≤ x) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : x ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2)) :
    x ≤ 2 * (a + b + c) := by
  nlinarith [sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)]

/-- Exact Vaughan decomposition consumed directly in L¹.  This is the crucial
finite assembly: no `N²` square-mean target appears. -/
theorem directPrimitiveMean_vaughan_le
    (N Q u v : ℕ) :
    directPrimitiveMean vonMangoldtIntegerCoeff N Q ≤
      2 * (directVaughanTypeIMean N Q u v +
        directVaughanTypeIIMean N Q u v + directVaughanSmallMean N Q v) := by
  unfold directVaughanTypeIMean directVaughanTypeIIMean directVaughanSmallMean
  unfold directPrimitiveMean
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          2 * (primitivePrefixAmplitude
              (vaughanTypeICoeff vaughanUnitIntegerCoeff u v) N q χ +
            primitivePrefixAmplitude
              (vaughanTypeIICoeff vaughanUnitIntegerCoeff u v) N q χ +
            primitivePrefixAmplitude
              (vaughanSmallCoeff vaughanUnitIntegerCoeff v) N q χ) := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro χ hχ
        apply amplitude_three_piece
        · exact primitivePrefixAmplitude_nonneg _ _ _ _
        · exact primitivePrefixAmplitude_nonneg _ _ _ _
        · exact primitivePrefixAmplitude_nonneg _ _ _ _
        · exact primitivePrefixAmplitude_nonneg _ _ _ _
        · rw [primitivePrefixAmplitude_sq, primitivePrefixAmplitude_sq,
            primitivePrefixAmplitude_sq, primitivePrefixAmplitude_sq]
          exact primitiveCharacterPrefixMaxSquare_le_three _ _ _ _ N q χ
            (fun n _ => (vaughanLambdaCoeff_unit_eq n).symm.trans
              (vaughanLambdaCoeff_eq vaughanUnitIntegerCoeff u v n))
      · positivity
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      ring

/-- Direct all-character nonprincipal prefix mean before conductor reduction. -/
def directAllCharacterMean (a : ℤ → ℂ) (N Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℝ)⁻¹) *
    ∑ χ ∈ nonprincipalCharacters q, nonprincipalPrefixAmplitude a N q χ

/-- The starting character-orthogonality step for arbitrary nonnegative residue
errors.  The caller supplies only the literal one-modulus character expansion. -/
theorem residue_errors_le_directAllCharacterMean
    (E : ℕ → ℝ) (N Q : ℕ)
    (hE : ∀ q ∈ Finset.Icc 1 Q, E q ≤ ((q.totient : ℝ)⁻¹) *
      ∑ χ ∈ nonprincipalCharacters q,
        nonprincipalPrefixAmplitude vonMangoldtIntegerCoeff N q χ) :
    (∑ q ∈ Finset.Icc 1 Q, E q) ≤
      directAllCharacterMean vonMangoldtIntegerCoeff N Q := by
  exact Finset.sum_le_sum hE

/-- Exact conductor regrouping with the direct `1/φ(q)` weight. -/
theorem direct_sum_nonprincipal_by_conductor
    (Q : ℕ) (F : (d : ℕ) → PrimitiveCharacter d → ℝ) :
    (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℝ)⁻¹) *
      ∑ χ ∈ nonprincipalCharacters q,
        F χ.conductor (conductorPrimitiveCharacter χ)) =
      ∑ d ∈ Finset.Icc 2 Q, directConductorWeight Q d *
        ∑ ψ : PrimitiveCharacter d, F d ψ := by
  calc
    _ = ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℝ)⁻¹) *
        ∑ d ∈ nonprincipalConductors q, ∑ ψ : PrimitiveCharacter d, F d ψ := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [sum_nonprincipal_by_conductor (Finset.mem_Icc.mp hq).1 F]
    _ = ∑ q ∈ Finset.Icc 1 Q, ∑ d ∈ Finset.Icc 2 Q,
        if d ∣ q then ((q.totient : ℝ)⁻¹) *
          ∑ ψ : PrimitiveCharacter d, F d ψ else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.mul_sum, ← Finset.sum_filter]
      apply Finset.sum_subset
      · intro d hd
        have hd' := Finset.mem_filter.mp hd
        have hddiv : d ∣ q := (Nat.mem_divisors.mp hd'.1).1
        rw [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hd'.2, (Nat.le_of_dvd (Finset.mem_Icc.mp hq).1 hddiv).trans
          (Finset.mem_Icc.mp hq).2⟩, hddiv⟩
      · intro d hdQ hdnot
        simp only [Finset.mem_filter] at hdQ
        exfalso
        apply hdnot
        rw [nonprincipalConductors, Finset.mem_filter]
        exact ⟨Nat.mem_divisors.mpr ⟨hdQ.2,
          Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩,
          (Finset.mem_Icc.mp hdQ.1).1⟩
    _ = ∑ d ∈ Finset.Icc 2 Q, ∑ q ∈ Finset.Icc 1 Q,
        if d ∣ q then ((q.totient : ℝ)⁻¹) *
          ∑ ψ : PrimitiveCharacter d, F d ψ else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [directConductorWeight, Finset.sum_filter, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hdq : d ∣ q <;> simp [hdq]

/-- Prefix correction amplitude at change of level. -/
def conductorErrorAmplitude {q : ℕ} (χ : DirichletCharacter ℂ q)
    (a : ℤ → ℂ) (N : ℕ) : ℝ :=
  Real.sqrt (conductorErrorPrefixMaxSquare χ a 0 N)

lemma conductorErrorAmplitude_sq {q : ℕ} (χ : DirichletCharacter ℂ q)
    (a : ℤ → ℂ) (N : ℕ) :
    conductorErrorAmplitude χ a N ^ 2 =
      conductorErrorPrefixMaxSquare χ a 0 N := by
  apply Real.sq_sqrt
  unfold conductorErrorPrefixMaxSquare
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨0, by simp, by simp [conductorErrorPrefixSquare]⟩

lemma conductorErrorAmplitude_nonneg {q : ℕ} (χ : DirichletCharacter ℂ q)
    (a : ℤ → ℂ) (N : ℕ) : 0 ≤ conductorErrorAmplitude χ a N :=
  Real.sqrt_nonneg _

private lemma amplitude_two_piece
    {x a b : ℝ} (hx : 0 ≤ x) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : x ^ 2 ≤ 2 * (a ^ 2 + b ^ 2)) : x ≤ 2 * (a + b) := by
  nlinarith [sq_nonneg (a + b)]

lemma nonprincipalAmplitude_le_conductor
    {q : ℕ} (χ : DirichletCharacter ℂ q) (a : ℤ → ℂ) (N : ℕ) :
    nonprincipalPrefixAmplitude a N q χ ≤
      2 * (primitivePrefixAmplitude a N χ.conductor
        (conductorPrimitiveCharacter χ) + conductorErrorAmplitude χ a N) := by
  apply amplitude_two_piece
  · exact nonprincipalPrefixAmplitude_nonneg _ _ _ _
  · exact primitivePrefixAmplitude_nonneg _ _ _ _
  · exact conductorErrorAmplitude_nonneg _ _ _
  · rw [nonprincipalPrefixAmplitude_sq, primitivePrefixAmplitude_sq,
      conductorErrorAmplitude_sq]
    apply characterPrefixMaxSquare_le_conductor_add_error

/-- Literal correction mean; this is separate from the Type-I/II hybrid input. -/
def directConductorCorrectionMean (a : ℤ → ℂ) (N Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℝ)⁻¹) *
    ∑ χ ∈ nonprincipalCharacters q, conductorErrorAmplitude χ a N

/-- Finite all-character to primitive-conductor L¹ reduction. -/
theorem directAllCharacterMean_le_conductor
    (a : ℤ → ℂ) (N Q : ℕ) :
    directAllCharacterMean a N Q ≤
      2 * (∑ d ∈ Finset.Icc 2 Q, directConductorWeight Q d *
        ∑ ψ : PrimitiveCharacter d, primitivePrefixAmplitude a N d ψ) +
      2 * directConductorCorrectionMean a N Q := by
  unfold directAllCharacterMean directConductorCorrectionMean
  calc
    _ ≤ ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℝ)⁻¹) *
        ∑ χ ∈ nonprincipalCharacters q,
          2 * (primitivePrefixAmplitude a N χ.conductor
            (conductorPrimitiveCharacter χ) + conductorErrorAmplitude χ a N) := by
      gcongr with q hq χ hχ
      exact nonprincipalAmplitude_le_conductor χ a N
    _ = 2 * (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℝ)⁻¹) *
        ∑ χ ∈ nonprincipalCharacters q,
          primitivePrefixAmplitude a N χ.conductor
            (conductorPrimitiveCharacter χ)) +
        2 * (∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℝ)⁻¹) *
          ∑ χ ∈ nonprincipalCharacters q, conductorErrorAmplitude χ a N) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      ring
    _ = _ := by
      rw [direct_sum_nonprincipal_by_conductor]

/-- Compatibility transport to the historical `q / φ(q)` primitive mean.
The stronger production transport is
`direct_conductor_sum_le_apNormalizedPrimitive` in the AP-normalized assembly;
this theorem deliberately retains the old majorant for downstream API
compatibility only. -/
theorem direct_conductor_sum_le_primitive
    (a : ℤ → ℂ) (N Q : ℕ) :
    (∑ d ∈ Finset.Icc 2 Q, directConductorWeight Q d *
      ∑ ψ : PrimitiveCharacter d, primitivePrefixAmplitude a N d ψ) ≤
      conductorHarmonicFactor Q ^ 2 * directPrimitiveMean a N Q := by
  unfold directPrimitiveMean
  calc
    _ ≤ ∑ d ∈ Finset.Icc 2 Q,
        (conductorHarmonicFactor Q ^ 2 * ((d : ℝ) / (d.totient : ℝ))) *
          ∑ ψ : PrimitiveCharacter d, primitivePrefixAmplitude a N d ψ := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_right
        (directConductorWeight_le_compatibility_majorant Q d)
        (Finset.sum_nonneg fun ψ _ => primitivePrefixAmplitude_nonneg a N d ψ)
    _ = ∑ d ∈ Finset.Icc 2 Q,
        conductorHarmonicFactor Q ^ 2 *
          (((d : ℝ) / (d.totient : ℝ)) *
            ∑ ψ : PrimitiveCharacter d, primitivePrefixAmplitude a N d ψ) := by
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ ∑ d ∈ Finset.Icc 1 Q,
        conductorHarmonicFactor Q ^ 2 *
          (((d : ℝ) / (d.totient : ℝ)) *
            ∑ ψ : PrimitiveCharacter d, primitivePrefixAmplitude a N d ψ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.Icc_subset_Icc_left (by omega)
      · intro d hd hnot
        unfold primitivePrefixAmplitude
        positivity
    _ = _ := by rw [Finset.mul_sum]

/-- Minimal missing Type-I direct mean input.  It is an inequality on the real
Vaughan lane, not a BV endpoint and not a conclusion-shaped AP error premise. -/
def VaughanDirectTypeIInput (N Q u v : ℕ) (K logPay : ℝ) : Prop :=
  directVaughanTypeIMean N Q u v ≤
    K * logPay * ((N : ℝ) + (Q : ℝ) ^ 2 * Real.sqrt N)

/-- Minimal missing Type-II hybrid mean input.  The last term retains the cutoff
payment `QN/√(u+1)` which becomes `Q N^(13/14)` for `u≈N^(1/7)`. -/
def VaughanDirectTypeIIInput (N Q u v : ℕ) (K logPay : ℝ) : Prop :=
  directVaughanTypeIIMean N Q u v ≤
    K * logPay * ((N : ℝ) + (Q : ℝ) ^ 2 * Real.sqrt N +
      (Q : ℝ) * N / Real.sqrt (u + 1 : ℕ))

/-- The honest physical majorant exposed by the direct route. -/
def vaughanDirectPhysicalMajorant (N Q u : ℕ) (K logPay : ℝ) : ℝ :=
  K * logPay * ((N : ℝ) + (Q : ℝ) ^ 2 * Real.sqrt N +
    (Q : ℝ) * N / Real.sqrt (u + 1 : ℕ))

/-- Finite substitution of the two minimal analytic inputs.  The small lane and
change-level correction remain explicit, so this theorem cannot be mistaken
for Bombieri--Vinogradov. -/
theorem direct_L1_vaughan_physical_assembly
    (E : ℕ → ℝ) (N Q u v : ℕ) (K logPay : ℝ)
    (hK : 0 ≤ K) (hlogPay : 0 ≤ logPay)
    (hE : ∀ q ∈ Finset.Icc 1 Q, E q ≤ ((q.totient : ℝ)⁻¹) *
      ∑ χ ∈ nonprincipalCharacters q,
        nonprincipalPrefixAmplitude vonMangoldtIntegerCoeff N q χ)
    (hI : VaughanDirectTypeIInput N Q u v K logPay)
    (hII : VaughanDirectTypeIIInput N Q u v K logPay) :
    (∑ q ∈ Finset.Icc 1 Q, E q) ≤
      4 * conductorHarmonicFactor Q ^ 2 *
        (2 * vaughanDirectPhysicalMajorant N Q u K logPay +
          directVaughanSmallMean N Q v) +
      2 * directConductorCorrectionMean vonMangoldtIntegerCoeff N Q := by
  have hstart := residue_errors_le_directAllCharacterMean E N Q hE
  have hcond := directAllCharacterMean_le_conductor vonMangoldtIntegerCoeff N Q
  have htransport := direct_conductor_sum_le_primitive
    vonMangoldtIntegerCoeff N Q
  have hv := directPrimitiveMean_vaughan_le N Q u v
  have hlanes :
      directVaughanTypeIMean N Q u v + directVaughanTypeIIMean N Q u v ≤
        2 * vaughanDirectPhysicalMajorant N Q u K logPay := by
    unfold VaughanDirectTypeIInput at hI
    have hIphysical : directVaughanTypeIMean N Q u v ≤
        vaughanDirectPhysicalMajorant N Q u K logPay := by
      refine hI.trans ?_
      unfold vaughanDirectPhysicalMajorant
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity))
        (mul_nonneg hK hlogPay)
    calc
      _ ≤ vaughanDirectPhysicalMajorant N Q u K logPay +
          vaughanDirectPhysicalMajorant N Q u K logPay := add_le_add hIphysical hII
      _ = _ := by ring
  calc
    _ ≤ directAllCharacterMean vonMangoldtIntegerCoeff N Q := hstart
    _ ≤ 2 * (∑ d ∈ Finset.Icc 2 Q, directConductorWeight Q d *
          ∑ ψ : PrimitiveCharacter d,
            primitivePrefixAmplitude vonMangoldtIntegerCoeff N d ψ) +
        2 * directConductorCorrectionMean vonMangoldtIntegerCoeff N Q := hcond
    _ ≤ 2 * (conductorHarmonicFactor Q ^ 2 *
          directPrimitiveMean vonMangoldtIntegerCoeff N Q) +
        2 * directConductorCorrectionMean vonMangoldtIntegerCoeff N Q := by gcongr
    _ ≤ 2 * (conductorHarmonicFactor Q ^ 2 *
          (2 * (directVaughanTypeIMean N Q u v +
            directVaughanTypeIIMean N Q u v + directVaughanSmallMean N Q v))) +
        2 * directConductorCorrectionMean vonMangoldtIntegerCoeff N Q := by gcongr
    _ ≤ 2 * (conductorHarmonicFactor Q ^ 2 *
          (2 * (2 * vaughanDirectPhysicalMajorant N Q u K logPay +
            directVaughanSmallMean N Q v))) +
        2 * directConductorCorrectionMean vonMangoldtIntegerCoeff N Q := by gcongr
    _ = _ := by ring

/-- Pure cutoff algebra.  If `u+1 ≥ R²` and `N ≤ R¹⁴`, then the Type-II tail is
at most `Q R¹³`; choosing `R=N^(1/14)` means `u≈N^(1/7)`. -/
theorem vaughan_cutoff_fourteen_payment
    (N Q u : ℕ) (R : ℝ) (hR : 0 < R)
    (hu : R ^ 2 ≤ (u + 1 : ℕ)) (hN : (N : ℝ) ≤ R ^ 14) :
    (Q : ℝ) * N / Real.sqrt (u + 1 : ℕ) ≤ (Q : ℝ) * R ^ 13 := by
  have hs : R ≤ Real.sqrt (u + 1 : ℕ) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    simpa [sq] using hu
  have hspos : 0 < Real.sqrt (u + 1 : ℕ) := Real.sqrt_pos.2 (by positivity)
  have hQR : 0 ≤ (Q : ℝ) := by positivity
  calc
    (Q : ℝ) * N / Real.sqrt (u + 1 : ℕ)
        ≤ (Q : ℝ) * (R ^ 14) / Real.sqrt (u + 1 : ℕ) := by gcongr
    _ ≤ (Q : ℝ) * (R ^ 14) / R := by
      exact div_le_div_of_nonneg_left (mul_nonneg hQR (by positivity)) hR hs
    _ = (Q : ℝ) * R ^ 13 := by
      field_simp

/-- Log ledger: conductor regrouping contributes two powers.  If the direct
Type-I/II theorem costs `log^C`, choosing `B ≥ A+C+2` pays all displayed logs
in the usual cutoff `Q≤√N/log^B`.  This is exponent bookkeeping only. -/
theorem vaughan_log_exponent_payment
    (A C B : ℕ) (L : ℝ) (hL : 1 ≤ L) (hB : A + C + 2 ≤ B) :
    L ^ (C + 2) / L ^ B ≤ 1 / L ^ A := by
  have hpos : 0 < L ^ B := pow_pos (lt_of_lt_of_le zero_lt_one hL) _
  have hApos : 0 < L ^ A := pow_pos (lt_of_lt_of_le zero_lt_one hL) _
  rw [div_le_div_iff₀ hpos hApos]
  calc
    L ^ (C + 2) * L ^ A = L ^ (A + C + 2) := by ring_nf
    _ ≤ L ^ B := pow_le_pow_right₀ hL hB
    _ = 1 * L ^ B := by ring

end

end AnalyticNumberTheory.LargeSieve
