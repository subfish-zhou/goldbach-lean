

import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanDirectAPNormalizedAssembly
import MathlibNt.AnalyticNumberTheory.LargeSieve.BilinearTensorPrefixMaximalExplicit

/-!
 # AP-normalized direct Type-II bilinear shells

The direct mean is formed before squaring.  Cauchy is first taken over primitive
characters and then over moduli with the outer weight `q⁻¹/²`; hence the square
side has exactly the `q / φ(q)` weight accepted by the bilinear tensor large
sieve.  The canonical `(d,t)` tensor prefix remains intact throughout.

The resulting square scale on a `d`-shell is

`H * RM² * D * (M + c(Q)Q²) * E(D,M)`.

For the actual tensor energy `E(D,M) ≪ D M log⁵`, taking the square root gives
`D M + sqrt(c(Q)) Q sqrt(D * D M)`, rather than another unsquared factor `D M`.
Thus the existing second moment is sufficient for the direct shell.  The final
theorem below only aggregates already-physical shell bounds; it does not freeze
a Type-II conclusion as a new analytic premise.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators

noncomputable section

/-- The unsquared AP-normalized mean of one actual canonical `(d,t)` tensor
prefix.  The maximum in `t` is inside each primitive-character summand. -/
def apNormalizedVaughanCanonicalBilinearShellMean
    (b : ℕ → ℂ) (y N u v k l Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, ((q.totient : ℝ)⁻¹) *
    ∑ χ : PrimitiveCharacter q,
      Real.sqrt (vaughanCanonicalBilinearPrefixMaxSquare
        b y N u v k l q χ)

lemma apNormalizedVaughanCanonicalBilinearShellMean_nonneg
    (b : ℕ → ℂ) (y N u v k l Q : ℕ) :
    0 ≤ apNormalizedVaughanCanonicalBilinearShellMean b y N u v k l Q := by
  unfold apNormalizedVaughanCanonicalBilinearShellMean
  positivity

/-- The correct double Cauchy inequality for a direct bilinear shell.  Character
Cauchy is local to each modulus; modulus Cauchy uses `q⁻¹/²`.  Consequently no
cardinality factor for the modulus interval and no second tensor energy appear. -/
theorem apNormalizedVaughanCanonicalBilinearShellMean_sq_le
    (b : ℕ → ℂ) (y N u v k l Q : ℕ)
    (hcard : ∀ q ∈ Finset.Icc 1 Q,
      Fintype.card (PrimitiveCharacter q) ≤ q.totient) :
    apNormalizedVaughanCanonicalBilinearShellMean b y N u v k l Q ^ 2 ≤
      conductorHarmonicFactor Q *
        (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter q,
            vaughanCanonicalBilinearPrefixMaxSquare
              b y N u v k l q χ) := by
  let F : (q : ℕ) → PrimitiveCharacter q → ℝ := fun q χ =>
    vaughanCanonicalBilinearPrefixMaxSquare b y N u v k l q χ
  let T : ℕ → ℝ := fun q => ((q.totient : ℝ)⁻¹) *
    ∑ χ : PrimitiveCharacter q, Real.sqrt (F q χ)
  let Bq : ℕ → ℝ := fun q => ((q : ℝ) / (q.totient : ℝ)) *
    ∑ χ : PrimitiveCharacter q, F q χ
  have hT (q : ℕ) (hq : q ∈ Finset.Icc 1 Q) :
      (q : ℝ) * T q ^ 2 ≤ Bq q := by
    have hq0 : 0 < q := (Finset.mem_Icc.mp hq).1
    have hφ : (0 : ℝ) < q.totient := by
      exact_mod_cast Nat.totient_pos.mpr hq0
    have hchars := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (PrimitiveCharacter q)))
      (f := fun χ => Real.sqrt (F q χ))
    have hsquares : (∑ χ : PrimitiveCharacter q, Real.sqrt (F q χ)) ^ 2 ≤
        (q.totient : ℝ) * ∑ χ : PrimitiveCharacter q, F q χ := by
      calc
        _ ≤ (Fintype.card (PrimitiveCharacter q) : ℝ) *
            ∑ χ : PrimitiveCharacter q, (Real.sqrt (F q χ)) ^ 2 := hchars
        _ ≤ (q.totient : ℝ) *
            ∑ χ : PrimitiveCharacter q, (Real.sqrt (F q χ)) ^ 2 := by
              gcongr
              exact_mod_cast hcard q hq
        _ = (q.totient : ℝ) * ∑ χ : PrimitiveCharacter q, F q χ := by
              congr 1
              apply Finset.sum_congr rfl
              intro χ hχ
              rw [Real.sq_sqrt]
              exact bilinearTensorCharacterPrefixMaxSquare_nonneg _ _ _ _ _
    dsimp [T, Bq]
    have hφne : (q.totient : ℝ) ≠ 0 := ne_of_gt hφ
    rw [div_eq_mul_inv]
    field_simp
    nlinarith
  have hsplit : apNormalizedVaughanCanonicalBilinearShellMean
      b y N u v k l Q =
      ∑ q ∈ Finset.Icc 1 Q,
        (Real.sqrt (q : ℝ))⁻¹ * (Real.sqrt (q : ℝ) * T q) := by
    unfold apNormalizedVaughanCanonicalBilinearShellMean
    apply Finset.sum_congr rfl
    intro q hq
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
    have hsne : Real.sqrt (q : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hq0
    dsimp [T, F]
    field_simp
  rw [hsplit]
  refine (Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 Q)
    (fun q => (Real.sqrt (q : ℝ))⁻¹)
    (fun q => Real.sqrt (q : ℝ) * T q)).trans ?_
  have hfirst : (∑ q ∈ Finset.Icc 1 Q,
      (Real.sqrt (q : ℝ))⁻¹ ^ 2) = conductorHarmonicFactor Q := by
    unfold conductorHarmonicFactor
    apply Finset.sum_congr rfl
    intro q hq
    rw [inv_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ q)]
  rw [hfirst]
  apply mul_le_mul_of_nonneg_left
  · calc
      (∑ q ∈ Finset.Icc 1 Q, (Real.sqrt (q : ℝ) * T q) ^ 2) ≤
          ∑ q ∈ Finset.Icc 1 Q, Bq q := by
            apply Finset.sum_le_sum
            intro q hq
            rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ q)]
            exact hT q hq
      _ = ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter q,
            vaughanCanonicalBilinearPrefixMaxSquare b y N u v k l q χ := by
            rfl
  · exact conductorHarmonicFactor_nonneg Q

/-- Existing bilinear tensor prefix large sieve inserted after the direct double
Cauchy.  The actual energy occurs exactly once. -/
theorem apNormalizedVaughanCanonicalBilinearShellMean_sq_le_energy
    (b : ℕ → ℂ) (y N u v k l Q : ℕ)
    (hQ : 0 < Q)
    (hcard : ∀ q ∈ Finset.Icc 1 Q,
      Fintype.card (PrimitiveCharacter q) ≤ q.totient) :
    apNormalizedVaughanCanonicalBilinearShellMean b y N u v k l Q ^ 2 ≤
      conductorHarmonicFactor Q *
        ((((Nat.log2 (vaughanCanonicalTensorLength y k) + 1 : ℕ) : ℝ) ^ 2) *
        ((2 ^ k : ℕ) : ℝ) *
        ((vaughanCanonicalTensorLength y k : ℕ) +
          primitiveBilinearQFactor Q * (Q : ℝ) ^ 2) *
        vaughanCanonicalShortTensorEnergy vaughanMangoldtCoeff b
          y N u v k l) := by
  refine (apNormalizedVaughanCanonicalBilinearShellMean_sq_le
    b y N u v k l Q hcard).trans ?_
  apply mul_le_mul_of_nonneg_left
  · exact weighted_primitive_vaughanCanonicalBilinear_prefixMax_unconditional
      b y N u v k l Q hQ
  · exact conductorHarmonicFactor_nonneg Q

/-- Fully explicit direct-shell square bound.  In contrast with applying an
additional rowwise estimate after Cauchy, the `27` tensor energy is multiplied
only once. -/
theorem apNormalizedVaughanCanonicalBilinearShellMean_sq_le_energy27
    (b : ℕ → ℂ) (y N u v k l Q : ℕ) (B : ℝ)
    (hQ : 0 < Q)
    (hcard : ∀ q ∈ Finset.Icc 1 Q,
      Fintype.card (PrimitiveCharacter q) ≤ q.totient)
    (hB : ∀ n ≤ y, ‖b n‖ ≤ B) :
    apNormalizedVaughanCanonicalBilinearShellMean b y N u v k l Q ^ 2 ≤
      conductorHarmonicFactor Q *
        ((((Nat.log2 (vaughanCanonicalTensorLength y k) + 1 : ℕ) : ℝ) ^ 2) *
        ((2 ^ k : ℕ) : ℝ) *
        ((vaughanCanonicalTensorLength y k : ℕ) +
          primitiveBilinearQFactor Q * (Q : ℝ) ^ 2) *
        (27 * B ^ 2 * (((2 ^ k : ℕ) : ℝ) *
          vaughanCanonicalTensorLength y k) * Real.log (y + 1 : ℕ) ^ 5)) := by
  refine (apNormalizedVaughanCanonicalBilinearShellMean_sq_le
    b y N u v k l Q hcard).trans ?_
  apply mul_le_mul_of_nonneg_left
  · exact weighted_primitive_vaughanCanonicalBilinear_prefixMax_energy27
      b y N u v k l Q B hQ hB
  · exact conductorHarmonicFactor_nonneg Q

/-- Scalar physical-scale extraction from the square ledger.  If `X = D*M ≤ y`,
then the polynomial part of the direct shell is bounded by
`y + sqrt(c) Q sqrt(D*y)`.  This is the point at which the apparent extra
`D*M` is removed by taking the square root. -/
theorem bilinear_direct_shell_physical_scale
    (D M y Q c : ℝ)
    (hD : 0 ≤ D) (hM : 0 ≤ M) (hy : 0 ≤ y)
    (hQ : 0 ≤ Q) (hc : 0 ≤ c) (hDM : D * M ≤ y) :
    Real.sqrt (D * (M + c * Q ^ 2) * (D * M)) ≤
      y + Real.sqrt c * Q * Real.sqrt (D * y) := by
  have hleft0 : 0 ≤ D * (M + c * Q ^ 2) * (D * M) := by positivity
  have hDy : 0 ≤ D * y := mul_nonneg hD hy
  have hmain : D * (M + c * Q ^ 2) * (D * M) ≤
      (y + Real.sqrt c * Q * Real.sqrt (D * y)) ^ 2 := by
    have hcroot : (Real.sqrt c) ^ 2 = c := Real.sq_sqrt hc
    have hdyroot : (Real.sqrt (D * y)) ^ 2 = D * y := Real.sq_sqrt hDy
    have hDM0 : 0 ≤ D * M := mul_nonneg hD hM
    have hsqDM : (D * M) ^ 2 ≤ y ^ 2 := by nlinarith
    have hmod : c * Q ^ 2 * D * (D * M) ≤ c * Q ^ 2 * D * y := by
      gcongr
    have hcross : 0 ≤ 2 * y * (Real.sqrt c * Q * Real.sqrt (D * y)) := by
      positivity
    rw [show D * (M + c * Q ^ 2) * (D * M) =
      (D * M) ^ 2 + c * Q ^ 2 * D * (D * M) by ring]
    have hrootprod :
        (Real.sqrt c * Q * Real.sqrt (D * y)) ^ 2 = c * Q ^ 2 * D * y := by
      rw [mul_pow, mul_pow, hcroot, hdyroot]
      ring
    rw [show (y + Real.sqrt c * Q * Real.sqrt (D * y)) ^ 2 =
      y ^ 2 + c * Q ^ 2 * D * y +
        2 * y * (Real.sqrt c * Q * Real.sqrt (D * y)) by
          rw [add_pow_two, hrootprod]
          ring]
    linarith
  have htarget : 0 ≤ y + Real.sqrt c * Q * Real.sqrt (D * y) := by positivity
  exact (Real.sqrt_le_iff).2 ⟨htarget, hmain⟩

/-- Honest final wiring: once the exact canonical shell decomposition and its
physical bounds have been proved, their finite sum inhabits the existing
AP-normalized Type-II input.  No Type-II estimate is assumed under another name. -/
theorem vaughanDirectAPNormalizedTypeIIInput_of_bilinear_shells
    {ι : Type*} [DecidableEq ι]
    (shells : Finset ι) (shellMean : ι → ℝ)
    (N Q u v : ℕ) (logPay : ℝ)
    (hdecomp : apNormalizedVaughanTypeIIMean N Q u v ≤
      ∑ s ∈ shells, shellMean s)
    (hshell : ∀ s ∈ shells, shellMean s ≤ logPay *
      ((N : ℝ) + (Q : ℝ) * N / Real.sqrt (u + 1 : ℕ))) :
    VaughanDirectAPNormalizedTypeIIInput N Q u v
      (shells.card : ℝ) logPay := by
  unfold VaughanDirectAPNormalizedTypeIIInput
  let X : ℝ := (N : ℝ) + (Q : ℝ) * N / Real.sqrt (u + 1 : ℕ)
  calc
    apNormalizedVaughanTypeIIMean N Q u v ≤ ∑ s ∈ shells, shellMean s := hdecomp
    _ ≤ ∑ _s ∈ shells, logPay * X := by
      apply Finset.sum_le_sum
      intro s hs
      exact hshell s hs
    _ = (shells.card : ℝ) * logPay * X := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring

end

end AnalyticNumberTheory.LargeSieve
